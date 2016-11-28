import Lambda.AST
import Lambda.Infer

import Control.Monad.State

main = print t
    where
        id = Abs "x" Nothing $ Var "x"
        const = Abs "x" Nothing (Abs "y" Nothing $ Var "x")
        ast = Let [("const", const), ("id", id)] $ App (Var "const") (Var "id")
        ((s, t), _) = runState (infer emptyEnv ast) 1
