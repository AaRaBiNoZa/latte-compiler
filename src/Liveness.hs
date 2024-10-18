module Liveness where
import Instr
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Map (Map)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import System.FilePath
import Data.Maybe (isNothing, fromJust)

data BlockLiveness = Bl {incoming :: Set Name, outgoing :: Set Name } deriving (Eq)
type FuncLiveness = Map BlockName BlockLiveness
type Liveness = Map FuncName FuncLiveness

data FlowState = Fs {changed :: Bool, live :: FuncLiveness, visited :: Set BlockName}

type FM a = StateT FlowState (ReaderT Cfg Identity) a

emptyFuncLiveness :: Cfg -> FuncLiveness
emptyFuncLiveness = M.map (const Bl {incoming = S.empty, outgoing = S.empty})

namesFromVals :: [Val] -> [Name]
namesFromVals [] = []
namesFromVals ((Var v):rest) = v:namesFromVals rest
namesFromVals (_:rest) = namesFromVals rest

getKillUse :: Instr -> (Set Name, Set Name) -- kill, use
getKillUse (BinOp r _ v1 v2) = (S.fromList [r], S.fromList (namesFromVals [v1,v2]))
getKillUse (Call r  _ params) = (S.fromList [r], S.fromList (namesFromVals params))
getKillUse (VCall _ params) = (S.empty, S.fromList (namesFromVals params))
getKillUse (Neg r v) = (S.fromList [r], S.fromList (namesFromVals [v]))
getKillUse (Copy r v) = (S.fromList [r], S.fromList (namesFromVals [v]))
getKillUse (Ret v) = (S.empty, S.fromList (namesFromVals [v]))
getKillUse VRet = (S.empty, S.empty)
getKillUse (CondJump v _ _) = (S.empty, S.fromList (namesFromVals [v]))
getKillUse (Jump _) = (S.empty, S.empty)
getKillUse (Store from to) = (S.empty, S.fromList $ namesFromVals [from, Var to])
getKillUse (Load n v) = (S.singleton n, S.fromList $ namesFromVals [v])
getKillUse (ObjAttr n v s) = (S.singleton n, S.fromList $ namesFromVals [v])
getKillUse (PtrOffset r n v) = (S.singleton r, S.fromList $ namesFromVals [n, v])
getKillUse (BitCast r v) = (S.singleton r, S.fromList $ namesFromVals [v])

analyzeFlow :: Code -> Set Name -> Set Name -- get incoming from outgoing
analyzeFlow [] out = out
analyzeFlow (i:rest) out = S.union (S.difference (analyzeFlow rest out) kill) use where
    (kill, use) = getKillUse i

visit :: BlockName -> FM () -- returns alive incoming
visit bname = do
    wasVisited <- gets (S.member bname . visited)
    unless wasVisited $ do
        modify (\old -> old {visited = S.insert bname (visited old)})
        analyzeLiveness bname

analyzeLiveness :: BlockName -> FM () -- returns alive incoming
analyzeLiveness bname = do
    cBlock <- asks (fromJust . M.lookup bname)
    mapM_ visit (successors cBlock) -- first visit successors
    oldBlockLiveness <- gets (fromJust . M.lookup bname . live)

    let newIncoming = analyzeFlow (blockCode cBlock) (outgoing oldBlockLiveness)
    modify (\old -> old {live = M.insert bname (oldBlockLiveness {incoming = newIncoming}) (live old)})

    succ_in <- mapM (\bname -> gets (incoming . fromJust . M.lookup bname . live)) (successors cBlock)
    let newOutgoing = S.unions succ_in

    let newBlockLiveness = Bl {incoming = newIncoming, outgoing = newOutgoing}
    when (newBlockLiveness /= oldBlockLiveness) $ modify (\old -> old {changed = True})
    modify (\old -> old {live = M.insert bname newBlockLiveness (live old)})

fullAnalyzeLiveness :: FM ()
fullAnalyzeLiveness = do
    graph <- ask
    modify (\old -> old {changed = False, visited = S.empty})
    mapM_ visit (M.keys graph)
    didChange <- gets changed
    when didChange fullAnalyzeLiveness

runFlowAnalysisForCfg :: Cfg -> FuncLiveness
runFlowAnalysisForCfg graph = live $ runIdentity (runReaderT (execStateT fullAnalyzeLiveness (Fs {changed = False, live = emptyFuncLiveness graph, visited = S.empty})) graph)

runFlowAnalysis :: Tac -> Liveness
runFlowAnalysis tac = M.map (runFlowAnalysisForCfg . funGraph) (functions tac)

instance Show BlockLiveness where
    show bl = unlines $ ["incoming: " ++ show (S.toList $ incoming bl),  "\noutgoing: " ++ show (S.toList $ outgoing bl)]

prettyPrintFuncLiveness :: FuncLiveness -> String
prettyPrintFuncLiveness funcLiveness = unlines $ map forBlock (M.toList funcLiveness) where
    forBlock (name, bl) = name ++ "\n" ++ show bl

prettyPrintLiveness :: Liveness -> String
prettyPrintLiveness l = unlines $ map forFunc (M.toList l) where
    forFunc (fName, fLiveness) = fName ++ "\n" ++ prettyPrintFuncLiveness fLiveness


saveAliveInfoToFile :: FilePath -> Liveness -> IO ()
saveAliveInfoToFile fpath ai = do
    let aiFileName = fpath -<.> ".ai"
    writeFile aiFileName  (prettyPrintLiveness ai)
    return ()
