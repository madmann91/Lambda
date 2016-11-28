module Lambda.AST where

type VarID  = String
type TypeID = String

data Type = Forall [TypeID] Type
          | Lambda Type Type
          | TypeVar TypeID
          deriving (Show, Eq, Ord)

data Expr = Let [(VarID, Expr)] Expr
          | App Expr Expr
          | Abs VarID (Maybe Type) Expr
          | Var VarID
          deriving (Show, Eq, Ord)
