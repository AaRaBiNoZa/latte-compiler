module Ssa where
import Instr
import Data.Map(Map)
import Data.Set(Set)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Data.Maybe (fromJust, catMaybes, fromMaybe)
import System.FilePath
import Data.List (nub, sortOn)
import Liveness (Liveness, FuncLiveness, incoming, outgoing)
import Data.Char (isDigit)


data SState = SState {blockDefs :: Map BlockName BlockDefs, graph :: Cfg, newloc :: Loc, funcLiveness :: FuncLiveness, renumbered :: Set BlockName}

type SM a = StateT SState Identity a

freshState :: Cfg -> FuncLiveness -> [Name] -> SState
freshState graph lv params = SState {blockDefs = d, graph = graph, newloc = length params, funcLiveness = lv, renumbered = S.empty} where
    d = M.fromList [("entry", M.fromList (zip params (map Var params)))]

freshVar :: Type -> SM Name
freshVar tp = do
    newLocation <- gets newloc
    modify (\old -> old {newloc = newloc old + 1})
    return (Local LL tp newLocation)

readVal :: BlockName -> Val -> SM Val
readVal bname (Var v) = do
    res <- gets (M.lookup v . fromJust . M.lookup bname . blockDefs)
    case res of
        Nothing -> error (show v)
        Just r -> return r
readVal bname val = return val

addMapping :: BlockName -> Name -> Val -> SM ()
addMapping bname key val = do
    oldBlockDefs <- gets (fromMaybe M.empty . M.lookup bname . blockDefs)
    let newBlockDefs = M.insert key val oldBlockDefs
    modify (\old -> old {blockDefs = M.insert bname newBlockDefs (blockDefs old)})


writeVar :: BlockName -> Name -> SM Name
writeVar bname v = do
    newV <- freshVar (getType v)
    addMapping bname v (Var newV)
    return newV

foldBinOp :: Val -> Val -> Bop -> Maybe Val
foldBinOp (ImmI i1) (ImmI i2) bop = do
    case bop of
        Add -> return (ImmI (i1 + i2))
        Sub -> return $ ImmI (i1 - i2)
        Mul -> return $ ImmI (i1 * i2)
        Sdiv -> return $ ImmI (i1 `div` i2)
        Srem -> return $ ImmI (i1 `rem` i2)
        Slt -> return $ ImmB (i1 < i2)
        Sgt -> return $ ImmB (i1 > i2)
        Sle -> return $ ImmB (i1 <= i2)
        Sge -> return $ ImmB (i1 >= i2)
        Eq -> return $ ImmB (i1 == i2)
        Ne -> return $ ImmB (i1 == i2)
foldBinOp (ImmB b1) (ImmB b2) bop = do
    case bop of
        Slt -> return $ ImmB (b1 < b2)
        Sgt -> return $ ImmB (b1 > b2)
        Sle -> return $ ImmB (b1 <= b2)
        Sge -> return $ ImmB (b1 >= b2)
        Eq -> return $ ImmB (b1 == b2)
        Ne -> return $ ImmB (b1 == b2)
        _ -> Nothing
foldBinOp _ _ _ = Nothing


renumberInstr :: BlockName -> Instr -> SM (Maybe Instr)
renumberInstr bname (BinOp res op v1 v2) = do
    v1Def <- readVal bname v1
    v2Def <- readVal bname v2
    let folded = foldBinOp v1Def v2Def op
    case folded of
        Nothing -> do
            newRes <- writeVar bname res
            return $ Just (BinOp newRes op v1Def v2Def)
        Just imm -> do
            addMapping bname res imm
            return Nothing
renumberInstr bname (Call res name params) = do
    paramDefs <- mapM (readVal bname) params
    newRes <- writeVar bname res
    return $ Just (Call newRes name paramDefs)
renumberInstr bname (VCall name params) = do
    paramDefs <- mapM (readVal bname) params
    return $ Just (VCall name paramDefs)
renumberInstr bname (Neg res val) = do
    valDef <- readVal bname val
    newRes <- writeVar bname res
    return $ Just (Neg newRes valDef)
renumberInstr bname (Copy res val) = do
    rval <- readVal bname val
    addMapping bname res rval
    return Nothing
renumberInstr bname (Ret val) = do
    newVal <- readVal bname val
    return $ Just (Ret newVal)
renumberInstr bname (CondJump val b1 b2) = do
    newVal <- readVal bname val
    return $ Just (CondJump newVal b1 b2)
renumberInstr bname i@(Jump b) = return $ Just i
renumberInstr bname VRet = return $ Just VRet
renumberInstr bname (Store from to) = do
    fromDef <- readVal bname from
    toDef <- readVal bname (Var to)
    case toDef of
        Var n -> return $ Just (Store fromDef n)
        _ -> error "Panic!"

renumberInstr bname (Load n v) = do
    vDef <- readVal bname v
    newRes <- writeVar bname n
    return $ Just (Load newRes vDef)
renumberInstr bname (ObjAttr n v s) = do
    vDef <- readVal bname v
    newRes <- writeVar bname n
    return $ Just (ObjAttr newRes vDef s)
renumberInstr bname (PtrOffset r n v) = do
    vDef <- readVal bname v
    nDef <- readVal bname n
    newRes <- writeVar bname r
    return $ Just (PtrOffset newRes nDef vDef)
renumberInstr bname (BitCast r v) = do
    vDef <- readVal bname v
    newRes <- writeVar bname r
    return $ Just (BitCast newRes vDef)


renumberBlock :: BlockName -> SM ()
renumberBlock bname = do
    was_renumbered <- gets (S.member bname . renumbered)
    if was_renumbered then
        return ()
    else do
        block <- gets (fromJust . M.lookup bname . graph)
        newCode <- mapM (renumberInstr bname) (blockCode block)

        let newBlock = block {blockCode = catMaybes newCode}
        modify (\old -> old {graph = M.insert bname newBlock (graph old), renumbered = S.insert bname (renumbered old)})

paddedZip :: [a] -> b -> [(a,b)]
paddedZip l def = zip l (replicate (length l) def)

createPhiForVar :: BlockName -> Name -> SM PhiNode
createPhiForVar bname var = do
    newV <- writeVar bname var
    return Ph {definitions = M.empty, oldVar = var, newVar = newV}

insertDummyPhisForAlive :: BlockName -> SM ()
insertDummyPhisForAlive bname = do
    aliveInBeg <- gets (S.toList . incoming . fromJust . M.lookup bname . funcLiveness)
    phiNodes <- mapM (createPhiForVar bname) aliveInBeg
    oldBlock <- gets (fromJust . M.lookup bname . graph)
    let updatedBlock = oldBlock {phiNodes = phiNodes}
    modify (\old -> old {graph = M.insert bname updatedBlock (graph old)})

updateSinglePhi :: (BlockName, BlockDefs) -> PhiNode -> PhiNode
updateSinglePhi (pred, predDefs) oldNode = oldNode {definitions = M.insert pred (fromJust (M.lookup (oldVar oldNode) predDefs)) (definitions oldNode)}

updatePhiFromPred :: BlockName -> (BlockName, BlockDefs) -> SM ()
updatePhiFromPred bname p@(pred, predDefs) = do
    oldBlock <- gets (fromJust . M.lookup bname .graph)
    let updatedBlockPhiNodes = map (updateSinglePhi p) (phiNodes oldBlock)
    let updatedBlock = oldBlock {phiNodes = updatedBlockPhiNodes}
    modify (\old -> old {graph = M.insert bname updatedBlock (graph old)})

updateDummyPhis :: BlockName -> [(BlockName, BlockDefs)] -> SM ()
updateDummyPhis bname = mapM_ (updatePhiFromPred bname)

prunedPhiVal :: PhiNode -> Maybe Val
prunedPhiVal node = if length uniqueElems == 1 then Just (head uniqueElems) else Nothing where
    uniqueElems = nub (filter (\x -> x /= Var (newVar node)) (M.elems (definitions node)))

tryPrunePhiNode :: BlockName -> PhiNode -> SM (Maybe PhiNode)
tryPrunePhiNode bname node = do
    case prunedPhiVal node of
        Just v -> do
            addMapping bname (oldVar node) v
            return Nothing
        Nothing -> return (Just node)


prunePhis :: BlockName -> SM ()
prunePhis bname = do
    oldBlock <- gets (fromJust . M.lookup bname . graph)
    let phis = phiNodes oldBlock
    newPhis <- mapM (tryPrunePhiNode bname) phis
    let newBlock = oldBlock {phiNodes = catMaybes newPhis}
    modify (\old -> old {graph = M.insert bname newBlock (graph old)})


visit :: BlockName -> SM (BlockName, BlockDefs)
visit bname = do
    curBlockDef <- gets (M.lookup bname . blockDefs)
    case curBlockDef of
        Just cBDef -> return (bname, cBDef) -- was visited before
        Nothing -> transformBlock bname


transformBlock :: BlockName -> SM (BlockName, BlockDefs)
transformBlock bname = do
    oldBlock <- gets (fromJust . M.lookup bname . graph)
    aliveIn <- gets (incoming . fromJust . M.lookup bname . funcLiveness)
    aliveOut <- gets (outgoing . fromJust . M.lookup bname . funcLiveness)
    case predecessors oldBlock of
        [] -> renumberBlock bname
        [single] -> do
            (p, predDefs) <- visit single
            let blockDef = M.filterWithKey (\k _ -> S.member k aliveIn) predDefs
            modify (\old -> old {blockDefs = M.insert bname blockDef (blockDefs old)})
            renumberBlock bname
        multi -> do
            insertDummyPhisForAlive bname -- updates blockdef
            predBlockDefs <- mapM visit multi
            updateDummyPhis bname predBlockDefs
            -- prunePhis bname -- removes unnecessary phis (doesn't work for now since it's not a local change...)
            renumberBlock bname
    oldDefs <- gets (fromJust . M.lookup bname . blockDefs )
    let newBlockDefs = M.filterWithKey (\k _ -> S.member k aliveOut) oldDefs
    modify (\old -> old {blockDefs = M.insert bname newBlockDefs (blockDefs old)})
    return (bname, newBlockDefs)

ssaForCfg :: SM ()
ssaForCfg = do
    transformBlock "entry"
    g <- gets graph
    -- the lines below probably makes "renumbered" attribute above redundant, but better be safe than sorry :)
    mapM_ visit (sortBlockNames (M.keys g))

runSsaForCfg :: [Name] -> Cfg -> FuncLiveness -> Cfg
runSsaForCfg params g liveness = graph r where
    r = runIdentity (execStateT ssaForCfg (freshState g liveness params))

runSsaTransform :: Tac -> Liveness -> Tac
runSsaTransform tac lv = tac {functions = M.fromList results} where
    results = map go fnames
    go :: FuncName -> (FuncName, Fun)
    go funcName = (funcName, f {funGraph = r})
        where
            f = fromJust $ M.lookup funcName (functions tac)
            r = runSsaForCfg (funParams f) (funGraph f) (fromJust $ M.lookup funcName lv)

    fnames :: [FuncName]
    fnames = M.keys (functions tac)