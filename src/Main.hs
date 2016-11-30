import Lambda.AST
import Lambda.Infer

import Control.Monad.State

main = print t
    where
        -- Identity function: \x -> x
        id = Abs "x" Nothing $ Var "x"
        -- Constant function: \x -> (\y -> x)
        const = Abs "x" Nothing (Abs "y" Nothing $ Var "x")
        -- Application function: \f . \x . f x
        apply = Abs "f" Nothing (Abs "x" Nothing $ App (Var "f") (Var "x"))

        ast = Let [("const", const), ("id", id), ("apply", apply)] $ App (Var "apply") $ App (Var "const") (Var "id")
        -- The inferred type should be: forall a b . a -> b -> b
        ((s, t), _) = runState (infer emptyEnv ast) 1
