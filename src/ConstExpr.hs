module ConstExpr where
import qualified Npos.Latte.Abs as L
import Instr


evalConstExpr :: L.Expr -> Maybe Val
evalConstExpr L.ELitFalse = return $ ImmB False
evalConstExpr L.ELitTrue = return $ ImmB True
evalConstExpr (L.ELitInt i) = return $ ImmI $ fromInteger i
evalConstExpr (L.Neg expr) = do
    ImmI i <- evalConstExpr expr
    return $ ImmI (-i)
evalConstExpr (L.Not expr) = do
    ImmB b <- evalConstExpr expr
    return $ ImmB (not b)
evalConstExpr (L.EAnd e1 e2) = do
    ImmB b1 <- evalConstExpr e1
    if not b1 then return $ ImmB False else do
        ImmB b2 <- evalConstExpr e2
        if not b2 then return $ ImmB False else return $ ImmB True
evalConstExpr (L.EOr e1 e2) = do
    ImmB b1 <- evalConstExpr e1
    if b1 then return $ ImmB True else do
        ImmB b2 <- evalConstExpr e2
        if b2 then return $ ImmB True else return $ ImmB False
evalConstExpr (L.EAdd e1 op e2) = do
    ImmI v1 <- evalConstExpr e1
    ImmI v2 <- evalConstExpr e2

    case op of
        L.Plus -> return $ ImmI (v1 + v2)
        L.Minus -> return $ ImmI (v1 - v2)
evalConstExpr (L.ERel e1 op e2) = do
    v1 <- evalConstExpr e1
    v2 <- evalConstExpr e2

    res <- case (v1, v2) of
        (ImmI i1, ImmI i2) -> case op of
            L.LTH  -> return $ i1 < i2
            L.LE  -> return $ i1 <= i2
            L.GTH  -> return $ i1 > i2
            L.GE  -> return $ i1 >= i2
            L.NE  -> return $ i1 /= i2
            L.EQU -> return $ i1 == i2
        (ImmB b1, ImmB b2) -> case op of
            L.NE -> return $ b1 /= b2
            L.EQU -> return $ b1 == b2
            _ -> Nothing
        _ -> Nothing

    return $ ImmB res

evalConstExpr (L.EMul e1 op e2) = do
    ImmI v1 <- evalConstExpr e1
    ImmI v2 <- evalConstExpr e2

    case (op, v2) of
        (L.Times , _) -> return $ ImmI (v1 * v2)
        (L.Div , _) -> return $ ImmI (v1 `div` v2)
        (L.Mod , _) -> return $ ImmI (v1 `rem` v2)
evalConstExpr _ = Nothing