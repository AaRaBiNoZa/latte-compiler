module Instr where

import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Data.List (intercalate, sortOn)
import Data.Maybe (fromMaybe, fromJust)
import Data.Char (ord, isPrint, isDigit)
import Numeric (showHex)
import System.FilePath

-- type definitions and utilities ---- 
type Loc = Int
type BlockName = String
type FuncName = String
type ClassName = String
type Code = [Instr]
type Cfg = Map BlockName BasicBlock
data Stage = IR | LL deriving (Eq, Ord)

data PhiNode = Ph {definitions :: Map BlockName Val, oldVar :: Name, newVar :: Name}
type BlockDefs = Map Name Val
type FuncPhis = Map BlockName [PhiNode]

data Attribute = Attr {tp :: Type, idx :: Int}
data ClassMembers = CMembers {attrs :: Map String Attribute, size :: Int, typ :: Type}

data BasicBlock = Bb {
    blockCode :: Code,
    phiNodes :: [PhiNode],
    predecessors :: [BlockName],
    successors :: [BlockName]
}

-- arrref and classref are both similar. Technically both are pointers to some custom types, but I want to have this distinction that
-- "ClassRef class" is a different kind of being than Ptr (ClassRef class). At no place will "class" (without classref) be used.
data Type
    = IntT
    | BoolT
    | StringT
    | Ptr Type
    | ArrRef Type
    | ClassRef ClassName
    | VoidT deriving (Eq, Ord)

data Fun = Fn {funRetType :: Type, funName :: FuncName, funParams :: [Name], funGraph :: Cfg}
data Tac = Tac {
    functions :: Map FuncName Fun,
    classes :: Map ClassName ClassMembers,
    stringPool :: Map String Val
}

data Name = Local Stage Type Loc deriving  (Eq, Ord)

data Val = Var Name | ImmI Int | ImmB Bool | ImmS Int Loc | Nullptr Type deriving (Eq)

data Instr
    = BinOp Name Bop Val Val
    | Call Name FuncName [Val]
    | VCall FuncName [Val]
    | ObjAttr Name Val Loc -- res = name.string, but translated to field index already
    | PtrOffset Name Val Val -- res = name[val]
    | Load Name Val
    | Store Val Name -- from to
    | BitCast Name Val
    | Neg Name Val
    | Copy Name Val
    | Ret Val
    | VRet
    | CondJump Val BlockName BlockName
    | Jump BlockName deriving (Eq)

data Bop
    = Add
    | Sub
    | Mul
    | Sdiv
    | Srem
    | Slt
    | Sgt
    | Sle
    | Sge
    | Eq
    | Ne deriving (Eq)

emptyBlock :: BasicBlock
emptyBlock = Bb {
    blockCode = [],
    phiNodes = [],
    predecessors = [],
    successors = []
}

sortBlockNames :: [BlockName] -> [BlockName]
sortBlockNames = sortOn idx where
    idx label = if null digits then 0 else (read digits :: Int) + 1 where
            digits = filter isDigit label

getArrElemType :: Type -> Type
getArrElemType (ArrRef t) = t
getArrElemType _ = error "Not an array!"

sizeOf :: Type -> Int 
sizeOf IntT = 4
sizeOf BoolT = 1
sizeOf StringT = 8
sizeOf VoidT = error "Trying to get size of void!"
sizeOf _ = 8 -- ptr

deref :: Type -> Type
deref (Ptr tp) = tp
deref _ = error "Not a pointer"

getType :: Name -> Type
getType (Local _ t _ ) = t

getValType :: Val -> Type
getValType (Var v) = getType v
getValType (ImmI _) = IntT
getValType (ImmB _) = BoolT
getValType (ImmS _ _) = StringT
getValType (Nullptr t) = t

isOpResBool :: Bop -> Bool
isOpResBool Slt = True
isOpResBool Sgt = True
isOpResBool Sle = True
isOpResBool Sge = True
isOpResBool Eq = True
isOpResBool Ne = True
isOpResBool _ = False

showRefereeType :: Type -> String
showRefereeType arr@(ArrRef t) = '%':getLLClassName arr
showRefereeType cls@(ClassRef c) = '%':getLLClassName cls
showRefereeType _ = error "Not a reference"

getLLClassName :: Type -> String
getLLClassName (ArrRef t) = "arr_" ++ getLLClassName t
getLLClassName (ClassRef name) = "class_" ++ name
getLLClassName StringT = "string"
getLLClassName t = show t

getStringName :: Val -> String
getStringName (ImmS len loc) = "@str." ++ show loc
getStringName _ = error "Not a string"

getMangledName :: String -> String
getMangledName "main" = "main"
getMangledName name = "_" ++ name

-- translation to string ----
instance Show Type where
    show IntT = "i32"
    show BoolT = "i1"
    show StringT = "i8*"
    show (Ptr t) = show t ++ "*"
    show arr@(ArrRef t) = showRefereeType arr ++ "*"
    show cls@(ClassRef c) = showRefereeType cls ++ "*"
    show VoidT = "void"

instance Show Stage where
    show IR = "ir_"
    show LL = "ll_"

instance Show Name where
    show (Local s tp loc) = "%"++ show s ++ "_" ++ show loc
instance Show Val where
    show (Var v) = show v
    show (ImmI i) = show i
    show (ImmB b) = if b then "true" else "false"
    show s@(ImmS len loc ) = "bitcast ([" ++ show len ++ " x i8]* " ++ getStringName s ++ " to i8*)"
    show (Nullptr t) = "null"

instance Show Instr where
    show (BinOp result op v1 v2) = show result ++ " = " ++ show op ++ " " ++  show (getValType v1) ++ " " ++ show v1 ++ ", " ++ show v2
    show (Call result name params) = show result ++ " = call " ++ show (getType result) ++ " @" ++ name ++ "(" ++ compileArgs params ++ ")"
    show (VCall name params) = "call void @" ++ name ++ "(" ++ compileArgs params ++ ")"
    show (Neg result v) = show result ++ " = sub i32 0, " ++ show v
    show (Copy result v) = show result ++ " = " ++ show v
    show (Ret v) = "ret " ++ show (getValType v) ++ " " ++ show v
    show VRet = "ret void"
    show (CondJump v b1 b2) = "br i1 " ++ show v ++ ", label %" ++ b1 ++ ", label %" ++ b2
    show (Jump b) = "br label %" ++ b
    show (BitCast result val) = show result ++ " = bitcast " ++ show (getValType val) ++ " " ++ show val ++ " to " ++ show (getType result)
    show (ObjAttr result v idx) = show result ++ " = " ++ "getelementptr " ++ refT ++ ", " ++ refT ++ "* " ++ show v ++ ", i32 0, i32 " ++ show idx where
        refT = showRefereeType (getValType v)
    show (PtrOffset result ptr v) = show result ++ " = getelementptr " ++ derefT ++ ", " ++ derefT ++ "* " ++ show ptr ++ ", " ++ show (getValType v) ++ " " ++ show v where
        derefT = show (deref (getValType ptr))
    show (Store from to) = "store  " ++ show (getValType from) ++ " " ++ show from ++ ", " ++ show (getType to) ++ " " ++ show to
    show (Load to from) = show to ++ " = load " ++ show (getType to) ++ ", " ++ show (getValType from) ++ " " ++ show from

instance Show Bop where
    show Add =  "add"
    show Sub =  "sub"
    show Mul =   "mul"
    show Sdiv =  "sdiv"
    show Srem =  "srem"
    show Slt =  "icmp slt"
    show Sgt =  "icmp sgt"
    show Sle =  "icmp sle"
    show Sge =  "icmp sge"
    show Eq =  "icmp eq"
    show Ne =  "icmp ne"

instance Show PhiNode where
    show node = "\t" ++ show nv ++ " " ++  " = phi " ++ show (getType nv) ++ " " ++ intercalate "," ds where
        nv = newVar node
        ds = map peel (M.toList (definitions node))
        peel (bname, val) = "[" ++ show val ++ ", " ++ "%" ++ bname ++ "]"

instance Show Fun where
    show (Fn retT name params cfg) = unlines ["define " ++ show retT ++ " @" ++ name ++ "(" ++ compileParams params ++ ") {"] ++ body ++ "\n}\n" where
        body = intercalate "\n" $ map go (sortBlockNames (M.keys cfg))
        go bname = bname ++ ": ;" ++ show preds ++ "\n" ++ compilePhis p ++ compileCode c where
            p = phiNodes block
            c = blockCode block
            preds = predecessors block
            block = fromJust $ M.lookup bname cfg

instance Show Tac where
    show tac = unlines [compileStringPool (stringPool tac), prologue, cdefs, code] where
        cdefs = compileClassDefs (classes tac)
        code = unlines $ map show (M.elems (functions tac))

compileCode :: Code -> String
compileCode code = intercalate "\n" (map (("\t" ++ ) . show) code)

compilePhis :: [PhiNode] -> String
compilePhis nodes = unlines $ map show nodes

compileParams :: [Name] -> String
compileParams v = intercalate ", " $ map (\v -> show (getType v) ++ " " ++ show v) v

compileArgs :: [Val] -> String
compileArgs v = intercalate ", " $ map (\v -> show (getValType v) ++ " " ++ show v) v

compileClassDefs :: Map ClassName ClassMembers -> String
compileClassDefs cs = unlines $ map compileClassDef (M.toList cs) where
    compileClassDef (name, members) = "%" ++ name ++ " = type {\n" ++ intercalate ",\n" (map go (M.toAscList (attrs members))) ++ "\n}" where
        go (name, attr) = "\t" ++ show (tp attr)

prologue :: String
prologue = unlines [
    "declare void @_printInt(i32)", 
    "declare void @_error()", 
    "declare i32 @_readInt()", 
    "declare void @_printString(i8*)", 
    "declare i8* @_readString()", 
    "declare i8* @addStrings(i8*, i8*)",
    "declare i32* @malloc(i32)"
    ]

-- Convert a single character to LLVM-style escaped representation
-- remark -- the next two functions were written with the help of chatgpt
toLLVMEscaped :: Char -> String
toLLVMEscaped c
  | c == '"'  = "\\22"                          -- Escape double quote
  | c == '\\' = "\\5C"                          -- Escape backslash
  | not (isPrint c) || ord c < 32 || ord c > 126 = "\\" ++ pad (showHex (ord c) "") -- Escape non-printable
  | otherwise = [c]                             -- Keep printable characters as they are
  where
    pad s = if length s == 1 then '0' : s else s -- Ensure two-digit hex

-- Convert a Haskell string to an LLVM string literal
toLLVMString :: String -> String
toLLVMString s = "\"" ++ concatMap toLLVMEscaped s ++ "\""

compileStringPool :: Map String Val -> String
compileStringPool spool = unlines (map go (M.toList spool)) where
    go (s, n) = getStringName n ++ " = constant [" ++ show (length s + 1) ++ " x i8] c" ++ init (toLLVMString s) ++ "\\00\""