module TypeChecker where

import qualified Data.Map as M
import Data.Map(Map)

import qualified Data.Set as S
import Data.Set(Set)

import qualified Latte.Abs as L
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import Data.Maybe (fromJust)

data Type
    = IntT
    | StrT
    | BoolT
    | VoidT
    | ArrT Type
    | ClassT L.Ident
    deriving (Eq, Ord)

instance Show Type where
    show IntT = "int"
    show StrT = "string"
    show BoolT = "boolean"
    show VoidT = "void"
    show (ArrT t) = show t ++ "[]"
    show (ClassT id) = "class " ++ showIdent id

data FunT = FunT Type [Type] deriving (Show, Eq)

data ClassMembers = ClassMembers {attrs :: Map L.Ident Type, methods :: Map L.Ident FunT, super :: Maybe L.Ident} deriving Show

data TCEnv = TCEnv {
    varTypes :: Map L.Ident Type,
    funcTypes :: Map L.Ident FunT,
    classes :: Map L.Ident ClassMembers,
    blockVars :: Set L.Ident,
    inFunc :: Maybe L.Ident,
    inClass :: Maybe L.Ident,
    allPathsReturn :: Bool
} deriving Show

data Error = Error {desc :: String, location :: L.BNFC'Position} deriving Show

type TCM a = (ReaderT TCEnv (ExceptT Error Identity)) a

-- Util
predefinedFuncEnv :: Map L.Ident FunT
predefinedFuncEnv = M.fromList [
    (L.Ident "printInt", FunT VoidT [IntT]),
    (L.Ident "printString", FunT VoidT [StrT]),
    (L.Ident "error", FunT VoidT []),
    (L.Ident "readString", FunT StrT []),
    (L.Ident "readInt", FunT IntT [])
    ]

emptyEnv :: TCEnv
emptyEnv = TCEnv M.empty predefinedFuncEnv  M.empty S.empty Nothing Nothing False

showErr :: Error -> String
showErr (Error desc loc) = desc ++ "\n" ++ showPos loc

showPos :: L.BNFC'Position -> String
showPos (Just (line, col)) = show line ++ ":" ++ show col
showPos Nothing = "??:??"

showIdent :: L.Ident -> String
showIdent (L.Ident id) = id

getCMembers :: L.Ident -> L.BNFC'Position -> TCM ClassMembers
getCMembers cname pos = do
    maybeCmembers <- asks $ M.lookup cname . classes
    case maybeCmembers of
         Just cmembers -> return cmembers
         Nothing -> throwError $ Error ("Trying to access members of undeclared class: " ++ showIdent cname) pos

getAttributeType :: Type -> L.Ident -> L.BNFC'Position -> TCM (Maybe Type)
getAttributeType (ClassT cname) attr pos = do
    cmembers <- getCMembers cname pos
    let mAttrT = M.lookup attr (attrs cmembers)
    case mAttrT of
        Just attrT -> return $ Just attrT
        Nothing -> case super cmembers of
            Just s -> getAttributeType (ClassT s) attr pos
            Nothing -> return Nothing
getAttributeType (ArrT _) (L.Ident "length") _ = return $ Just IntT
getAttributeType t attr pos = throwError $ Error ("Cannot access " ++ showIdent attr ++ " of " ++ show t) pos

getMethodType :: Type -> L.Ident -> L.BNFC'Position -> TCM (Maybe FunT)
getMethodType (ClassT cname) meth pos = do
    cmembers <- getCMembers cname pos
    let mMethT = M.lookup meth (methods cmembers)
    case mMethT of
        Just methT -> return $ Just methT
        Nothing -> case super cmembers of
            Just s -> getMethodType (ClassT s) meth pos
            Nothing -> return Nothing
getMethodType t meth pos = throwError $ Error ("Cannot access " ++ showIdent meth ++ " of " ++ show t) pos

parseArrayElemType :: L.Type -> TCM Type
parseArrayElemType (L.Arr pos _) = throwError $ Error "Invalid array type, arrays can only be one dimensional." pos
parseArrayElemType (L.Void pos) = throwError $ Error "Cannot create arrays of type Void." pos
parseArrayElemType t = parseType t

parseType :: L.Type -> TCM Type
parseType (L.Int _) = return IntT
parseType (L.Str _) = return StrT
parseType (L.Bool _) = return BoolT
parseType (L.Void _) = return VoidT
parseType (L.Arr _ t) = do
    t <- parseArrayElemType t
    return $ ArrT t
parseType (L.Class pos ident) = do
    classExists <- asks $ M.member ident . classes
    if classExists then return $ ClassT ident else throwError $ Error ("Usage of undeclared class: " ++ showIdent ident) pos
parseType (L.Fun pos _ _ ) = throwError $ Error "Catastrophe! How did I get here?" pos

doesTypeMatch :: Type -> Type -> L.BNFC'Position -> TCM Bool -- t2 is "expected", can be a superclass
doesTypeMatch t1@(ClassT id1) t2@(ClassT id2) pos = 
    if t1 == t2 then
        return True
    else do
        cmembers <- getCMembers id1 pos
        let s = super cmembers
        case s of
            Nothing -> return False
            Just s -> doesTypeMatch (ClassT s) t2 pos
doesTypeMatch (ArrT t1@(ClassT id1)) (ArrT t2@(ClassT id2)) pos = doesTypeMatch t1 t2 pos
doesTypeMatch t1 t2 pos = return $ t1 == t2

doesTypeMatchList :: Type -> [Type] -> L.BNFC'Position -> TCM Bool
doesTypeMatchList t1 (t2:rest) pos = do
    match <- doesTypeMatch t1 t2 pos
    if match then
        return True
    else
        doesTypeMatchList t1 rest pos
doesTypeMatchList t [] pos = return False

checkTypeMatchesList :: Type -> [Type]-> L.BNFC'Position -> String -> TCM ()
checkTypeMatchesList t expected pos msg = do
    match <- doesTypeMatchList t expected pos
    if not match then
        throwError $ Error ("Type mismatch in " ++ msg ++ ": \nExpected types: " ++ show expected ++ "\nGot: " ++ show t) pos
    else return ()    

checkTypesAreSame :: Type -> Type -> L.BNFC'Position -> String -> TCM ()
checkTypesAreSame t1 t2 pos msg = if t1 /= t2
    then
        throwError $ Error ("Type mismatch in " ++ msg ++ "\nGot " ++ show t1 ++ " and " ++ show t2) pos
    else
        return ()

checkBinOperandsHaveSameTypeMatchingFrom :: [Type] -> L.BNFC'Position -> L.Expr -> L.Expr -> String -> TCM Type
checkBinOperandsHaveSameTypeMatchingFrom expected pos e1 e2 msg = do
    t1 <- typeOf e1
    t2 <- typeOf e2
    if t1 /= t2 then
        throwError $ Error ("Type mismatch in " ++ msg ++ "\nGot " ++ show t1 ++ " and " ++ show t2) pos
    else do
        checkTypeMatchesList t1 expected pos msg
        return t1

checkBinOperandsHaveMatchingType :: L.BNFC'Position -> L.Expr -> L.Expr -> String -> TCM ()
checkBinOperandsHaveMatchingType pos e1 e2 msg = do
    t1 <- typeOf e1
    t2 <- typeOf e2
    match1 <- doesTypeMatch t1 t2 pos
    match2 <- doesTypeMatch t2 t1 pos 
    if t1 == VoidT then throwError $ Error ("Invalid binary operands: type " ++ show VoidT) pos 
    else if not (match1 || match2) then throwError $ Error ("Types do not match in " ++ msg ++ "\nGot: " ++ show t1 ++ " and " ++ show t2) pos
    else return ()

-- consteval
data ConsType
    = BoolCT Bool
    | IntCT Int
    deriving Show

evalSimExpr :: L.Expr -> Maybe ConsType
evalSimExpr (L.ELitFalse pos) = return $ BoolCT False
evalSimExpr (L.ELitTrue pos) = return $ BoolCT True
evalSimExpr (L.ELitInt pos i) = return $ IntCT $ fromInteger i
evalSimExpr (L.Neg pos expr) = do
    IntCT i <- evalSimExpr expr
    return $ IntCT (-i)
evalSimExpr (L.Not pos expr) = do
    BoolCT b <- evalSimExpr expr
    return $ BoolCT (not b)
evalSimExpr (L.EAnd pos e1 e2) = do
    BoolCT b1 <- evalSimExpr e1
    if not b1 then return $ BoolCT False else do
        BoolCT b2 <- evalSimExpr e2
        if not b2 then return $ BoolCT False else return $ BoolCT True
evalSimExpr (L.EOr pos e1 e2) = do
    BoolCT b1 <- evalSimExpr e1
    if b1 then return $ BoolCT True else do
        BoolCT b2 <- evalSimExpr e2
        if b2 then return $ BoolCT True else return $ BoolCT False
evalSimExpr (L.EAdd pos e1 op e2) = do
    IntCT v1 <- evalSimExpr e1
    IntCT v2 <- evalSimExpr e2

    case op of
        L.Plus _ -> return $ IntCT (v1 + v2)
        L.Minus _ -> return $ IntCT (v1 - v2)
evalSimExpr (L.ERel pos e1 op e2) = do
    IntCT v1 <- evalSimExpr e1
    IntCT v2 <- evalSimExpr e2

    let res = case op of
                L.LTH _ -> v1 < v2
                L.LE _ -> v1 <= v2
                L.GTH _ -> v1 > v2
                L.GE _ -> v1 >= v2
                L.NE _ -> v1 /= v2
                L.EQU _ -> v1 == v2

    return $ BoolCT res

evalSimExpr (L.EMul pos e1 op e2) = do
    IntCT v1 <- evalSimExpr e1
    IntCT v2 <- evalSimExpr e2

    case (op, v2) of
        (L.Times _, _) -> return $ IntCT (v1 * v2)
        (L.Div _, _) -> return $ IntCT (v1 `div` v2)
        (L.Mod _, _) -> return $ IntCT (v1 `rem` v2)
evalSimExpr _ = Nothing

-- Typechecking

typeOfL :: L.LValue -> TCM Type
typeOfL (L.Var pos ident) = do
    t <- asks $ M.lookup ident . varTypes
    case t of
        -- if it's not in scope, scan the class hierarchy
        Nothing -> do 
            enclosingClass <- asks inClass
            t <- case enclosingClass of
                Nothing -> return Nothing
                Just c -> do
                    ta <- getAttributeType (ClassT c) ident pos
                    case ta of
                        Nothing -> return Nothing
                        Just ta -> return $ Just ta
            case t of
                Nothing -> throwError $ Error ("Trying to access undeclared variable: " ++ showIdent ident)  pos
                Just t -> return t
        Just t -> return t
typeOfL (L.ArrEl pos eArr eIdx) = do
    tIdx <- typeOf eIdx
    checkTypeMatchesList tIdx [IntT] pos "Array access"
    tArr <- typeOf eArr
    case tArr of
        ArrT t -> return t
        other -> throwError $ Error ("Invalid access - only arrays allow operator []. Tried to use [] on " ++ show other) pos
typeOfL (L.Attr pos ec ident) = do
    tc <- typeOf ec
    ta <- getAttributeType tc ident pos
    case ta of
        Nothing -> throwError $ Error ("Attribute " ++ showIdent ident ++ " is not a member of the given class or any superclasses.") pos
        Just ta -> return ta

typeOf :: L.Expr -> TCM Type
typeOf (L.ELitTrue _) = return BoolT
typeOf (L.ELitFalse _) = return BoolT
typeOf (L.ELitInt pos i) = do
    if -2147483648 <= i && i <= 2147483647 then
        return IntT
    else throwError $ Error ("Integer literal out of bounds for Int. Must be in range [-2147483648, 2147483647]. Got: " ++ show i) pos
typeOf (L.EString _ _) = return StrT
typeOf (L.ELValue pos lval) = typeOfL lval
typeOf (L.Neg pos e) = do
    t <- typeOf e
    checkTypeMatchesList t [IntT] pos "Negation"
    return t
typeOf (L.Not pos e) = do
    t <- typeOf e
    checkTypeMatchesList t [BoolT] pos "Not"
    return t
typeOf (L.EAdd pos e1 (L.Plus _) e2) = do
    checkBinOperandsHaveSameTypeMatchingFrom [IntT, StrT] pos e1 e2 "Addition"
typeOf (L.EAdd pos e1 (L.Minus _) e2) = do
    checkBinOperandsHaveSameTypeMatchingFrom [IntT] pos e1 e2 "Subtraction"
typeOf (L.EMul pos e1 op e2) = do
    checkBinOperandsHaveSameTypeMatchingFrom [IntT] pos e1 e2 "Multiplicative operation"
typeOf (L.ERel pos e1 (L.EQU _) e2) = do
    checkBinOperandsHaveMatchingType pos e1 e2 "Equality"
    return BoolT
typeOf (L.ERel pos e1 (L.NE _) e2) = do
    checkBinOperandsHaveMatchingType pos e1 e2 "Inequality"
    return BoolT
typeOf (L.ERel pos e1 op e2) = do
    checkBinOperandsHaveSameTypeMatchingFrom [IntT] pos e1 e2 "Comparison"
    return BoolT
typeOf (L.EAnd pos e1 e2) = do
    checkBinOperandsHaveSameTypeMatchingFrom [BoolT] pos e1 e2 "And"
    return BoolT
typeOf (L.EOr pos e1 e2) = do
    checkBinOperandsHaveSameTypeMatchingFrom [BoolT] pos e1 e2 "Or"
    return BoolT
typeOf (L.ECrtArr pos t e) = do
    t <- parseArrayElemType t
    tSize <- typeOf e
    checkTypeMatchesList tSize [IntT] pos "Create array"
    return $ ArrT t
typeOf (L.ENullRef pos ident) = do
    classExists <- asks $ M.member ident . classes
    if classExists then return $ ClassT ident else throwError $ Error ("Trying to obtain nullref of undeclared class type: " ++ showIdent ident) pos
typeOf (L.ECrtClass pos t) = do
    t <- parseType t
    case t of
        ct@(ClassT ident) -> return ct
        _ -> throwError $ Error ("Invalid use of 'new' keyword. Tried to use 'new' on " ++ show t) pos
typeOf (L.EApp pos id args) = do
    funT <- asks $ M.lookup id . funcTypes
    enclosingClass <- asks inClass

    funT <- case enclosingClass of
        Nothing -> return funT
        Just c -> do
            mT <- getMethodType (ClassT c) id pos
            case mT of
                Nothing -> return funT
                Just mT -> return $ Just mT
    case funT of
        Nothing -> throwError $ Error ("Trying to call an undeclared function or method " ++ showIdent id) pos
        Just funT -> typeOfFnApp funT args pos
typeOf (L.EMethApp pos e_class meth args) = do
    t <- typeOf e_class
    methT <- getMethodType t meth pos
    case methT of
        Nothing -> throwError $ Error ("Method " ++ showIdent meth ++ " is not a member of " ++ show t ++ " class or any superclasses.") pos
        Just methT -> typeOfFnApp methT args pos
typeOf (L.ESelfRef pos) = do
    t <- asks inClass
    case t of
        Nothing -> throwError $ Error "'self' used outside of class" pos
        Just t -> return $ ClassT t

typeOfFnApp :: FunT -> [L.Expr] -> L.BNFC'Position -> TCM Type
typeOfFnApp fn@(FunT tRet params) args pos = do
    tp <- go fn args pos
    case tp of 
        Nothing -> do
            tArgs <- mapM typeOf args
            throwError $ Error ("Invalid function arguments.\nExpected: " ++ show params ++ "\nGot:" ++ show tArgs) pos

        Just tp -> return tp
    where
        go :: FunT -> [L.Expr] -> L.BNFC'Position -> TCM (Maybe Type)
        go (FunT tRet (tParam:restParams)) (eArg:restArgs) pos = do
            tArg <- typeOf eArg
            match <- doesTypeMatch tArg tParam pos
            if not match then throwError $ Error ("Argument type doesn't match parameter type.\nExpected " ++ show tParam ++ "\nGot: " ++ show tArg ) pos
            else go (FunT tRet restParams) restArgs pos
        go (FunT tRet []) [] pos = return $ Just tRet
        go (FunT tRet []) _ pos = return Nothing
        go (FunT tRet _) [] pos = return Nothing

checkBlock :: L.Block -> TCM TCEnv
checkBlock (L.Block pos []) = ask
checkBlock (L.Block pos (st:stmts)) = do
    newEnv <- checkStmt st
    local (const newEnv) (checkBlock (L.Block pos stmts))

checkStmt :: L.Stmt -> TCM TCEnv
checkStmt (L.Empty pos) = ask
checkStmt (L.Incr pos lval) = do
    t <- typeOfL lval
    checkTypeMatchesList t [IntT] pos $ "Increment" ++ show t
    ask
checkStmt (L.Decr pos lval) = do
    t <- typeOfL lval
    checkTypeMatchesList t [IntT] pos $ "Decrement" ++ show t
    ask
checkStmt (L.Ass pos lval e_val) = do
    tVal <- typeOf e_val
    tLval <- typeOfL lval
    checkTypeMatchesList tVal [tLval] pos "Assignment"
    ask
checkStmt (L.SExp pos e) = do
    typeOf e
    ask
checkStmt (L.BStmt pos block) = do
    env <- ask
    afterBlock <- local (const env {blockVars = S.empty}) $ checkBlock block
    return env {allPathsReturn = allPathsReturn afterBlock}
checkStmt (L.Decl pos t []) = ask
checkStmt (L.Decl pos tp (item:rest)) = do
    env <- ask
    t <- parseType tp
    if t == VoidT then throwError $ Error "Cannot declare a variable of void type" pos else
        case item of
            L.NoInit posDec ident -> if S.member ident $ blockVars env then
                                        throwError $ Error ("Cannot redeclare a variable in the same block: " ++ showIdent ident) posDec
                                    else
                                        local (const env {varTypes = M.insert ident t $ varTypes env, blockVars = S.insert ident $ blockVars env}) $ checkStmt (L.Decl pos tp rest)
            L.Init posDec ident e -> if S.member ident $ blockVars env then
                                        throwError $ Error ("Cannot redeclare a variable in the same block: " ++ showIdent ident) posDec
                                    else do
                                        eType <- typeOf e
                                        checkTypeMatchesList eType [t] posDec "Declaration"
                                        local (const env {varTypes = M.insert ident t $ varTypes env, blockVars = S.insert ident $ blockVars env}) $ checkStmt (L.Decl pos tp rest)
checkStmt (L.Ret pos e) = do
    fname <- asks inFunc
    f <- asks (M.lookup (fromJust fname) . funcTypes) -- should panic if fname is Nothing, syntax doesn't allow it
    tE <- typeOf e
    case f of
        Nothing -> throwError $ Error "Return called outside of function" pos
        Just (FunT rt pt) -> checkTypeMatchesList tE [rt] pos "return"
    env <- ask
    return $ env {allPathsReturn = True}
checkStmt (L.VRet pos) = do
    fname <- asks inFunc
    f <- asks (M.lookup (fromJust fname) . funcTypes)
    case f of
        Nothing -> throwError $ Error "Return called outside of function" pos
        Just (FunT rt pt) -> checkTypeMatchesList VoidT [rt] pos "return"
    env <- ask
    return $ env {allPathsReturn = True}
checkStmt (L.While pos e stmt) = do
    checkStmt (L.Cond pos e stmt)
checkStmt (L.ForEach pos tp ident e body) = do
    arr_t <- typeOf e
    env <- ask
    case arr_t of
        ArrT t -> do
            tp <- parseType tp
            checkTypeMatchesList t [tp] pos "ForEach"
            local (const env {varTypes = M.insert ident t $ varTypes env}) $ checkStmt body
        t -> throwError $ Error ("Only arrays can be iterated over. Tried it on " ++ show t)  pos
    return env

checkStmt (L.CondElse pos e st sf) = do
    tc <- typeOf e
    checkTypeMatchesList tc [BoolT] pos "Condition must be of type BoolT"
    let condVal = evalSimExpr e

    envt <- checkStmt st
    envf <- checkStmt sf

    alreadyReturns <- asks allPathsReturn -- return was before, don't care now
    env <- ask

    if alreadyReturns then return env else
        case condVal of
            Just (BoolCT False) -> return env {allPathsReturn = allPathsReturn envf}
            Just (BoolCT True) -> return env {allPathsReturn = allPathsReturn envt}
            Nothing -> return env {allPathsReturn = allPathsReturn envt && allPathsReturn envf}
            _ -> throwError $ Error "Catastrophe! How did I get here?" pos

checkStmt (L.Cond pos e stmt) = do
    checkStmt (L.CondElse pos e stmt (L.Empty pos))

-- reads class names from topdef and adds to env
checkClassNames :: [L.TopDef] -> TCM TCEnv
checkClassNames [] = ask
checkClassNames ((L.ClassDef pos ident super members):defs) = do
    exists <- asks (M.member ident . classes)
    if exists then throwError $ Error ("Multiple definitions of the same class " ++ showIdent ident) pos
    else do
        super_exists <- asks (M.member super . classes)
        if not super_exists && super /= L.Ident "Object" then throwError $ Error ("Superclass " ++ showIdent super ++ " must be declared before inheritance") pos
        else do
            env <- ask
            let s = if super == L.Ident "Object" then Nothing else Just super
            local (const env {classes = M.insert ident (ClassMembers M.empty M.empty s) (classes env)}) (checkClassNames defs)
checkClassNames (_:defs) = checkClassNames defs

checkParamTypes :: [L.Arg] -> TCM [Type]
checkParamTypes = mapM go
    where
    go :: L.Arg -> TCM Type
    go (L.Arg pos t id) = do
        t <- parseType t
        if t == VoidT then throwError $ Error ("Cannot declare parameters of type void: " ++ showIdent id) pos else return t

checkParamNames :: [L.Arg] -> TCM [L.Ident]
checkParamNames = go S.empty where
    go :: Set L.Ident -> [L.Arg] -> TCM [L.Ident]
    go acc ((L.Arg pos t id):rest) = if S.member id acc then throwError $ Error ("Parameter names duplicated: " ++ showIdent id) pos else do
        tail <- go (S.insert id acc) rest
        return $ id : tail
    go acc [] = return []

checkFnSignatures :: [L.TopDef] -> TCM TCEnv
checkFnSignatures [] = ask
checkFnSignatures ((L.FnDef pos rt ident params block):rest) = do
    exists <- asks (M.member ident . funcTypes)
    if exists then throwError $ Error ("Trying to redeclare an existing function " ++ showIdent ident) pos
    else do
        checkParamNames params
        paramTypes <- checkParamTypes params
        rt <- parseType rt
        env <- ask
        local (const env {funcTypes = M.insert ident (FunT rt paramTypes) (funcTypes env)}) (checkFnSignatures rest)
checkFnSignatures (_:rest) = checkFnSignatures rest

-- only adds/checks attributes and method signatures
checkCStmtSignature :: L.Ident -> L.CStmt -> TCM TCEnv
checkCStmtSignature className (L.CEmpty pos) = ask
checkCStmtSignature className (L.CDecl _ tp []) = ask
checkCStmtSignature className (L.CDecl _ tp ((L.CNoInit pos var):items)) = do
    t <- parseType tp
    if t == VoidT then throwError $ Error ("Cannot declare an attribute of void type: " ++ showIdent var) pos else do
        cmembers <- getCMembers className pos
        if M.member var (attrs cmembers) then throwError $ Error ("Cannot redeclare attributes within a class: " ++ showIdent var) pos
        else do
            let new_attrs = M.insert var t (attrs cmembers)
            let new_cmembers = cmembers {attrs = new_attrs}
            env <- ask
            local (const env {classes = M.insert className new_cmembers (classes env)}) $ checkCStmtSignature className (L.CDecl pos tp items)
checkCStmtSignature className (L.CMethDef pos rt meth params body) = do
    cmembers <- getCMembers className pos
    if M.member meth (methods cmembers) then throwError $ Error ("Cannot redeclare a method in the same class: " ++ showIdent meth ++ " in " ++ showIdent className) pos
    else do
        checkParamNames params
        paramTypes <- checkParamTypes params
        rt <- parseType rt
        let ft = FunT rt paramTypes
        let superClass  = super cmembers
        case superClass of
            Nothing -> return ()
            Just superClass -> do
                superFt <- getMethodType (ClassT superClass) meth pos
                case superFt of
                    Just superFt -> do
                        if superFt /= ft then
                            throwError $ Error ("Cannot change a signature of a virtual method in a subclass\nTried to override " ++ showIdent meth ++ " of " ++ showIdent className) pos
                        else
                            return ()
                    _ -> return ()
                
        let new_methods = M.insert meth (FunT rt paramTypes) (methods cmembers)
        let new_cmembers = cmembers {methods = new_methods}
        env <- ask
        return env {classes = M.insert className new_cmembers (classes env)}

checkCBlockSignatures :: L.Ident -> L.CBlock -> TCM TCEnv
checkCBlockSignatures className (L.CBlock p (cstmt:rest)) = do
    env <- checkCStmtSignature className cstmt
    local (const env) $ checkCBlockSignatures className (L.CBlock p rest)
checkCBlockSignatures className (L.CBlock p []) = ask

-- only "signatures" without method bodies
checkClassMembers :: [L.TopDef] -> TCM TCEnv
checkClassMembers [] = ask
checkClassMembers ((L.ClassDef pos ident super cblock):rest) = do
    env <- checkCBlockSignatures ident cblock -- could also pass inclass but not needed
    local (const env) $ checkClassMembers rest
checkClassMembers (_:rest) = checkClassMembers rest

-- -- class names -> func sig -> class members -> func body -> class meth body
checkFuncBody :: L.TopDef -> TCM ()
checkFuncBody (L.FnDef pos rt ident params body) = do
    paramNames <- checkParamNames params
    paramTypes <- checkParamTypes params
    let shadowingVarTypes = M.fromList $ zip paramNames paramTypes
    env <- ask
    rt <- parseType rt
    newEnv <- local (const env {varTypes = M.union shadowingVarTypes (varTypes env), inFunc = Just ident}) $ checkBlock body
    if not (rt == VoidT) && not (allPathsReturn newEnv) then throwError $ Error ("Function/method " ++ showIdent ident ++ " does not return on all paths") pos else return ()
checkFuncBody _ = return ()

checkClassMethBodies :: L.CBlock -> TCM ()
checkClassMethBodies (L.CBlock _ []) = return ()
checkClassMethBodies (L.CBlock p ((L.CMethDef pos rt ident params body):rest)) = do
    checkFuncBody (L.FnDef pos rt ident params body)
    checkClassMethBodies (L.CBlock p rest)
checkClassMethBodies (L.CBlock p (s:rest)) = checkClassMethBodies $ L.CBlock p rest


checkFnAndMethBodies :: [L.TopDef] -> TCM ()
checkFnAndMethBodies [] = return ()
checkFnAndMethBodies (fn@(L.FnDef pos rt ident params body):rest) = do
    checkFuncBody fn
    checkFnAndMethBodies rest
checkFnAndMethBodies ((L.ClassDef pos ident super cblock):rest) = do
    env <- ask
    cmembers <- getCMembers ident pos
    local (const env {inClass = Just ident, funcTypes = M.union (methods cmembers) (funcTypes env)}) $ checkClassMethBodies cblock
    checkFnAndMethBodies rest

checkMainCorrect :: TCEnv -> TCM()
checkMainCorrect tcenv = do
    let main = M.lookup (L.Ident "main") (funcTypes tcenv)
    case main of
        Nothing -> throwError $ Error "Main function doesn't exist." Nothing
        Just (FunT IntT []) -> return ()
        Just other -> throwError $ Error ("Main function has wrong signature.\nExpected int main();\nGot: " ++ show other) Nothing

checkProgram :: L.Program -> TCM ()
checkProgram (L.Program pos defs) = do
    envWithClassNames <- checkClassNames defs
    envWithFuncSigsAndClassNames <- local (const envWithClassNames) $ checkFnSignatures defs

    checkMainCorrect envWithFuncSigsAndClassNames

    envWithFuncAndClassSigs <- local (const envWithFuncSigsAndClassNames) $ checkClassMembers defs
    local (const envWithFuncAndClassSigs) $ checkFnAndMethBodies defs

runTypeCheck :: L.Program -> Either Error ()
runTypeCheck program = runIdentity (runExceptT (runReaderT (checkProgram program) emptyEnv))