module IRCompiler where
import Instr

import qualified Npos.Latte.Abs as L
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import System.FilePath

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Data.Maybe ( fromJust, isJust, fromMaybe, catMaybes, mapMaybe )
import System.Process (system)
import ConstExpr (evalConstExpr)

data IEnv = IEnv {
    vars :: Map L.Ident Name, -- mapping from latte var to llvm name
    funRetTypes :: Map FuncName Type,
    classInfo :: Map ClassName ClassMembers
}

-- latte variables will have unique names in IR (declarations create new names)
data IState = IState {
    curBlockName :: Maybe BlockName,
    code :: Code,
    graph :: Cfg,
    newloc :: Loc,
    newlabel :: Loc,
    sPool :: Map String Val
}

type IM a = StateT IState (ReaderT IEnv Identity) a

run :: IState -> IEnv -> IM a -> (a, IState)
run s e c = runIdentity (runReaderT (runStateT c s) e)

freshState :: Map String Val -> IState
freshState spool = IState {
    curBlockName = Just "entry",
    code = [],
    graph = M.fromList [("entry", Bb [] [] [] [])],
    newloc = 0,
    newlabel = 0,
    sPool = spool
}

freshEnv :: Map FuncName Type -> Map ClassName ClassMembers -> IEnv
freshEnv funs cinfo = IEnv {
    vars = M.empty,
    funRetTypes = M.union (M.fromList [
        ("_printInt", VoidT),
        ("_readInt", IntT),
        ("_error", VoidT),
        ("_printString", VoidT),
        ("_readString", StringT),
        ("addStrings", StringT),
        ("malloc", Ptr IntT)
        ]) funs,
    classInfo = cinfo
}

parseLatteType :: L.Type -> Type
parseLatteType L.Int = IntT
parseLatteType L.Bool = BoolT
parseLatteType L.Void = VoidT
parseLatteType L.Str = StringT
parseLatteType (L.Arr t) = ArrRef (parseLatteType t)
parseLatteType (L.Class (L.Ident name)) = ClassRef name
parseLatteType _ = error "Fun type?"

defaultNoInit :: L.Type -> L.Expr
defaultNoInit L.Int = L.ELitInt 0
defaultNoInit L.Bool = L.ELitFalse
defaultNoInit L.Str = L.EString ""
defaultNoInit (L.Class n) = L.ENullRef n
defaultNoInit _ = error "Given type doesn't have a default"


-- control flow utils -----
-- the basic idea is: we keep the current block name and generated code in state
-- if we encounter block terminators, we end the block and clear this part of the state
-- all of these instructions work on the assumption that currently, we are in some active block i.e blockname in state is not Nothing
-- new instructions can only get emitted if we are in an active block
endBlock :: BlockName -> IM ()
endBlock curBName = do
    oldState <- get
    -- this is called only if the cur block is alive, so it is not Nothing
    let updatedBasicBlock = (fromJust (M.lookup curBName (graph oldState))) {blockCode = code oldState} 
    put (oldState {curBlockName = Nothing, code = [], graph = M.insert curBName updatedBasicBlock (graph oldState)})
    return ()

addEdge :: BlockName -> BlockName -> IM () -- predecessor, successor
addEdge predecessor successor = do
    predBlock <- gets (fromJust . M.lookup predecessor . graph) -- edges are added when ending a block, so predecessor has got to be non empty
    succBlock <- gets (fromMaybe emptyBlock . M.lookup successor . graph) -- successor may not exist yet, so we build a placeholder

    let updatedPredBlock = predBlock {successors = successor:successors predBlock}
    let updatedSuccBlock = succBlock {predecessors = predecessor: predecessors succBlock}

    modify (\old -> old {graph = M.insert successor updatedSuccBlock (graph old)})
    modify (\old -> old {graph = M.insert predecessor updatedPredBlock (graph old)})

append :: Instr -> IM ()
append i = modify (\old -> old {code = code old ++ [i]})

actualEmit :: BlockName -> Instr -> IM ()
actualEmit bname i@(Ret v) = do
    append i
    endBlock bname
actualEmit bname VRet = do
    append VRet
    endBlock bname
actualEmit bname i@(CondJump v b1 b2) = do
    append i
    endBlock bname
    addEdge bname b1
    addEdge bname b2
actualEmit bname i@(Jump b) = do
    append i
    endBlock bname
    addEdge bname b
actualEmit _ i = append i

emitIfInBlock :: Instr -> IM ()
emitIfInBlock i = do
    curBName <- gets curBlockName
    case curBName of
        Nothing -> return ()
        Just name -> actualEmit name i

emit :: Instr -> IM ()
emit = emitIfInBlock

placeLabel :: BlockName -> IM ()
placeLabel name = do
    curBName <- gets curBlockName
    curCode <- gets code
    when (isJust curBName) $ error "Label placed while in active block"
    when (curCode /= []) $ error "Label placed while in active block"
    preds <- gets (M.lookup name . graph)
    -- label is placed iff this block has had predecessors. Otherwise it is unreachable. Of course it is possible that there will be more predecessors later on (cycles), but 
    -- it has to have at least one not from the cycle to be reachable (otherwise how would we reach it)
    when (isJust preds) $ modify (\old -> old {curBlockName = Just name})

-- monad utils ----
newLoc :: IM Loc
newLoc = do
    newLocation <- gets newloc
    modify (\old -> old {newloc = newloc old + 1})
    return newLocation

newLab :: IM Loc
newLab = do
    newLabelId <- gets newlabel
    modify (\old -> old {newlabel = newlabel old + 1})
    return newLabelId

freshTemp :: Type -> IM Name
freshTemp t = do
    Local IR t <$> newLoc

freshBlockName :: IM BlockName
freshBlockName = do
    freshLabId <- newLab
    return ("label_" ++ show freshLabId)

freshLocal :: Type -> L.Ident -> IM (Name, IEnv)
freshLocal t id = do
    oldEnv <- ask
    var <- Local IR t <$> newLoc
    return (var, oldEnv {vars = M.insert id var (vars oldEnv)})

--- code generation ---
genBinOp :: Bop -> L.Expr -> L.Expr -> IM Val
genBinOp op e1 e2 = do
    v1 <- genExp e1
    v2 <- genExp e2
    r <- case (getValType v1, op) of
        (StringT, Add) -> do
            tmp <- freshTemp StringT
            emit $ Call tmp "addStrings" [v1, v2]
            return tmp
        (_, op) -> do
            tmp <- freshTemp (if isOpResBool op then BoolT else IntT)
            emit $ BinOp tmp op v1 v2
            return tmp

    return $ Var r

-- since I'm doing phi nodes, 
-- L.Var is a special case where lval and rval doesn't really change much
-- ArrEl and Attr return a pointer to the given thing (array element or object attribute)
genLVal :: L.LValue -> IM Name
genLVal (L.Var id) = asks $ fromJust . M.lookup id . vars
genLVal (L.ArrEl a i) = do
    arref <- genExp a
    arrPlace <- freshTemp $ Ptr (Ptr (getArrElemType (getValType arref)))
    attrIdx <- asks (idx . fromJust . M.lookup "arr" . attrs . fromJust . M.lookup (getLLClassName (getValType arref)) . classInfo)
    emit $ ObjAttr arrPlace arref 0
    arr <- freshTemp $ deref (getType arrPlace)
    emit $ Load arr (Var arrPlace)
    idx <- genExp i
    res <- freshTemp (Ptr (getArrElemType (getValType arref)))
    emit $ PtrOffset res (Var arr) idx
    return res
genLVal (L.Attr e (L.Ident name)) = do
    v <- genExp e
    attr <- asks (fromJust . M.lookup name . attrs . fromJust . M.lookup (getLLClassName (getValType v)) . classInfo)
    res <- freshTemp $ Ptr $ tp attr
    emit $ ObjAttr res v (idx attr)
    return res


genExp :: L.Expr -> IM Val
genExp (L.ELValue lval@(L.Var id)) = do
    v <- genLVal lval
    return $ Var v
genExp (L.ELValue lval) = do
    place <- genLVal lval
    res <- freshTemp (deref (getType place))
    emit $ Load res (Var place)
    return (Var res)
genExp (L.EMul e1 op e2) = do
    let bop = case op of
            L.Times -> Mul
            L.Div -> Sdiv
            L.Mod -> Srem
    genBinOp bop e1 e2
genExp (L.EAdd e1 op e2) = do
    let bop = case op of
            L.Plus -> Add
            L.Minus -> Sub
    genBinOp bop e1 e2
genExp (L.ERel e1 op e2) = do
    let bop = case op of
            L.LTH -> Slt
            L.LE -> Sle
            L.GTH -> Sgt
            L.GE -> Sge
            L.EQU -> Eq
            L.NE -> Ne
    genBinOp bop e1 e2
genExp (L.ELitInt i) = return $ ImmI $ fromInteger i
genExp L.ELitFalse = return $ ImmB False
genExp L.ELitTrue = return $ ImmB True
genExp (L.EString s) = do
    nm <- gets (M.lookup s . sPool)
    case nm of
        Nothing -> do
            sp <- gets sPool
            let v = ImmS (length s + 1) (M.size sp)
            modify (\old -> old {sPool = M.insert s v (sPool old)})
            return v
        Just v -> return v
genExp (L.Neg e) = genExp (L.EAdd (L.ELitInt 0) L.Minus e)
genExp (L.EApp (L.Ident name) args) = do
    argVals <- mapM genExp args
    let fnName = getMangledName name
    retType <- asks (fromJust . M.lookup fnName . funRetTypes)
    case retType of
        VoidT -> do
            emit $ VCall fnName argVals
            return (Nullptr VoidT) -- since it has to return some value
        other -> do
            tmp <- freshTemp retType
            emit $ Call tmp fnName argVals
            return (Var tmp)
genExp (L.ECrtArr tp len) = do
    -- arrays are just objects with two fields -- arr and length. Arr has a pointer to the actual array of elements.
    let elemType = parseLatteType tp
    let lt = ArrRef elemType

    res <- freshTemp lt
    malloced <- freshTemp $ Ptr IntT
    emit $ Call malloced "malloc" [ImmI 12] -- 8 for ptr and 4 for len
    emit $ BitCast res (Var malloced)

    lenPtr <- freshTemp (Ptr IntT)
    emit $ ObjAttr lenPtr (Var res) 1 -- for simplicity, let it be that arr - 0, len - 1
    lenv <- genExp len
    emit $ Store lenv lenPtr

    arrPtr <- freshTemp (Ptr (Ptr (parseLatteType tp)))
    emit $ ObjAttr arrPtr (Var res) 0

    mallocedArr <- freshTemp $ Ptr IntT
    typedMallocedArr <- freshTemp $ Ptr (parseLatteType tp)
    size <- freshTemp IntT
    emit $ BinOp size Mul lenv (ImmI (sizeOf elemType))
    emit $ Call mallocedArr "malloc" [Var size]
    emit $ BitCast typedMallocedArr (Var mallocedArr)

    emit $ Store (Var typedMallocedArr) arrPtr
    return (Var res)
genExp (L.ECrtClass tp) = do
    let lt = parseLatteType tp
    res <- freshTemp lt
    malloced <- freshTemp $ Ptr IntT
    clsSize <- asks (size . fromJust . M.lookup (getLLClassName lt) . classInfo)
    emit $ Call malloced "malloc" [ImmI clsSize]
    emit $ BitCast res (Var malloced)
    return $ Var res
genExp (L.ENullRef (L.Ident n)) = return (Nullptr (ClassRef n))
genExp logic = do
    case evalConstExpr logic of
        (Just v@(ImmB True)) -> return v
        (Just v@(ImmB False)) -> return v
        _ -> do
            res <- freshTemp BoolT
            emit $ Copy res (ImmB False)
            lTrue <- freshBlockName
            lNext <- freshBlockName

            genCond logic lTrue lNext
            placeLabel lTrue
            emit $ Copy res (ImmB True)
            emit $ Jump lNext
            placeLabel lNext
            return (Var res)

genLatBlock :: L.Block -> IM IEnv
genLatBlock (L.Block []) = ask
genLatBlock (L.Block (stmt:rest)) = do
    newEnv <- genStmt stmt
    local (const newEnv) (genLatBlock (L.Block rest))

genStmt :: L.Stmt -> IM IEnv
genStmt L.Empty = ask
genStmt (L.BStmt block) = genLatBlock block >> ask
genStmt (L.Ret e) = do
    v <- genExp e
    emit $ Ret v
    ask
genStmt L.VRet = do
    emit VRet
    ask
genStmt (L.Incr lval) = do
    genStmt (L.Ass lval (L.EAdd (L.ELValue lval) L.Plus (L.ELitInt 1)))
    ask
    -- could also be
    -- v <- genLVal lval
    -- emit $ BinOp v Add (Var v) (ImmI 1) -- doesn't really matter since it's taken care of further
    -- ask
genStmt (L.Decr lval) = do
    genStmt (L.Ass lval (L.EAdd (L.ELValue lval) L.Minus (L.ELitInt 1)))
    ask
genStmt (L.SExp e) = do
    genExp e
    ask
genStmt (L.Ass lval e) = do
    l <- genLVal lval
    v <- genExp e
    case getType l of
        Ptr t -> emit $ Store v l
        _ -> emit $ Copy l v
    ask
genStmt (L.Decl tp []) = ask
genStmt (L.Decl tp ((L.NoInit id):its)) = do
    let lt = parseLatteType tp
    case lt of
        ArrRef t -> do
            (v, newEnv) <- freshLocal lt id
            emit $ Copy v (Nullptr lt) -- ugly cause I forgot to add null arrays to grammar
            local (const newEnv) (genStmt (L.Decl tp its))
        _ -> genStmt (L.Decl tp (L.Init id (defaultNoInit tp):its))
genStmt (L.Decl tp ((L.Init id expr):its)) = do
    let t = parseLatteType tp
    (v, newEnv) <- freshLocal t id
    val <- genExp expr
    emit $ Copy v val
    local (const newEnv) (genStmt (L.Decl tp its))
genStmt (L.CondElse c strue sfalse) = do
    case evalConstExpr c of
        Just (ImmB True) -> genStmt strue
        Just (ImmB False) -> genStmt sfalse
        _ -> do
            lTrue <- freshBlockName
            lFalse <- freshBlockName
            lNext <- freshBlockName
            genCond c lTrue lFalse
            placeLabel lTrue
            genStmt strue
            emit $ Jump lNext
            placeLabel lFalse
            genStmt sfalse
            emit $ Jump lNext
            placeLabel lNext
            ask


genStmt (L.Cond c stmt) = do
    case evalConstExpr c of
        Just (ImmB True) -> genStmt stmt
        Just (ImmB False) -> ask
        _ -> do
            lTrue <- freshBlockName
            lNext <- freshBlockName
            genCond c lTrue lNext
            placeLabel lTrue
            genStmt stmt
            emit $ Jump lNext
            placeLabel lNext
            ask


genStmt (L.While e stmt) = do
    case evalConstExpr e of
        Just (ImmB True) -> genStmt stmt
        Just (ImmB False) -> ask
        _ -> do
            lCond <- freshBlockName
            lBody <- freshBlockName
            lNext <- freshBlockName
            emit $ Jump lCond
            placeLabel lCond
            genCond e lBody lNext
            placeLabel lBody
            genStmt stmt
            emit $ Jump lCond
            placeLabel lNext
            ask
genStmt (L.ForEach tp id e stmt) = do
    lCond <- freshBlockName 
    lBody <- freshBlockName
    lNext <- freshBlockName
    arref <- genExp e
    arrPlace <- freshTemp $ Ptr (Ptr (getArrElemType (getValType arref)))
    emit $ ObjAttr arrPlace arref 0
    arr <- freshTemp $ deref (getType arrPlace)
    emit $ Load arr (Var arrPlace)

    lenPlace <- freshTemp $ Ptr IntT
    emit $ ObjAttr lenPlace arref 1
    len <- freshTemp $ deref (getType lenPlace)
    emit $ Load len (Var lenPlace)

    index <- freshTemp IntT
    emit $ Copy index (ImmI 0)
    emit $ Jump lCond

    placeLabel lCond
    comp <- freshTemp BoolT
    emit $ BinOp comp Slt (Var index) (Var len)
    emit $ CondJump (Var comp) lBody lNext

    placeLabel lBody
    (v, newEnv) <- freshLocal (parseLatteType tp) id
    locPlace <- freshTemp (getType arr)
    emit $ PtrOffset locPlace (Var arr) (Var index)
    emit $ Load v (Var locPlace)
    local (const newEnv) (genStmt stmt)
    emit $ BinOp index Add (Var index) (ImmI 1)
    emit $ Jump lCond

    placeLabel lNext
    ask

genCond :: L.Expr -> BlockName -> BlockName -> IM IEnv
genCond (L.EAnd e1 e2) lTrue lFalse = do
    lMid <- freshBlockName
    genCond e1 lMid lFalse
    placeLabel lMid
    genCond e2 lTrue lFalse
genCond (L.EOr e1 e2) lTrue lFalse = do
    lMid <- freshBlockName
    genCond e1 lTrue lMid
    placeLabel lMid
    genCond e2 lTrue lFalse
genCond (L.Not e) lTrue lFalse = do
    genCond e lFalse lTrue
genCond e lTrue lFalse = do
    case evalConstExpr e of -- this is a tiny optimization for folding constexprs, but not very good
        Just (ImmB True) -> emit $ Jump lTrue
        Just (ImmB False) -> emit $ Jump lFalse
        _ -> do
            v <- genExp e
            emit $ CondJump v lTrue lFalse
    
    ask
    


parseParams :: [L.Arg] -> IM (IEnv, [Name])
parseParams ((L.Arg latteT id):rest) = do
    (v, newEnv) <- freshLocal (parseLatteType latteT) id
    (newEnv, params) <- local (const newEnv) (parseParams rest)
    return $ (newEnv, v:params)
parseParams _ = do
    env <- ask
    return (env, [])


genTopDef :: L.TopDef -> IM [Fun]
genTopDef (L.FnDef retTp (L.Ident name) params body) = do
    (env, params) <- parseParams params
    local (const env) (genLatBlock body)
    when (VoidT == parseLatteType retTp) $ emit VRet
    cfg <- gets graph
    return  [Fn (parseLatteType retTp) (getMangledName name) params cfg]
genTopDef _ = return []

readFunRetTypes :: [L.TopDef] -> Map FuncName Type
readFunRetTypes topDefs = M.fromList (mapMaybe go topDefs) where
    go (L.FnDef retTp (L.Ident name) params body) = Just (getMangledName name, parseLatteType retTp)
    go _ = Nothing

-- it's so ugly
-- reads class definitions and extracts attributes 
-- using mapAccum to keep track of idx of the attribute and count size of class fields
readClassDefs :: [L.TopDef] -> Map ClassName ClassMembers
readClassDefs topdefs = M.fromList (mapMaybe readClassDef topdefs) where
    readClassDef (L.ClassDef (L.Ident name) _ (L.CBlock cstmts)) = Just (getLLClassName (ClassRef name), CMembers {attrs = att, size = sz, typ=ClassRef name}) where
        ((cnt, sz), att) = M.mapAccum (\ (cnter, siz) t -> ((cnter + 1, siz + sizeOf t), Attr {tp = t, idx = cnter})) (0, 0) nmToTp
        nmToTp = M.fromList (concatMap readCstmt cstmts)
        readCstmt (L.CDecl tp its) = map (\(L.CNoInit (L.Ident i)) -> (i, parseLatteType tp)) its
        readCstmt _ = []
    readClassDef _ = Nothing

genArrDefs :: [Type] -> Map ClassName ClassMembers
genArrDefs ts = M.fromList (map go (ts ++ [IntT, StringT, BoolT]))   where
    go t = (arrname, CMembers {
            attrs = M.fromList [
                    ("arr", Attr {tp = Ptr t, idx = 0}),
                    ("length", Attr {tp = IntT, idx = 1})
                ],
            size = 12,
            typ = arreft
        }) where
            arreft = ArrRef t
            arrname = getLLClassName arreft

-- generates tac using foldr to thread stringPool in between functions
genTac :: L.Program -> Tac
genTac (L.Program topdefs) = foldr combine (Tac {functions = M.empty, classes = cinfo, stringPool = M.empty}) topdefs where
    cinfo = M.union cls (genArrDefs (map typ (M.elems cls)))
    cls = readClassDefs topdefs
    combine :: L.TopDef -> Tac -> Tac
    combine topdef old = old { functions = M.union (M.fromList (zip (map funName f) f)) (functions old), stringPool = sPool s} where
        (f,s) = run (freshState (stringPool old)) (freshEnv funRetTypes cinfo) (genTopDef topdef)
        funRetTypes = readFunRetTypes topdefs

saveTacToFile :: FilePath -> String -> Tac -> IO ()
saveTacToFile fpath ext tac = do
    let tacFileName = fpath -<.> ext

    writeFile tacFileName  (show tac)
    return ()

assemble :: FilePath -> IO ()
assemble fpath = do
    let byteCodeFileName = fpath -<.> ".bc"
    let llvmFileName = fpath -<.> ".ll"

    system $ "llvm-as -o " ++ byteCodeFileName ++ " " ++ llvmFileName
    system $ "llvm-link -o " ++ byteCodeFileName ++ " " ++ byteCodeFileName ++ " lib/runtime.bc"
    return ()