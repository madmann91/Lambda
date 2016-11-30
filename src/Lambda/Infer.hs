module Lambda.Infer where

import Lambda.AST
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State

-- | Type inference state: an integer to generate fresh type variables
type InferState = Int

type Env   = M.Map VarID Type
type Subst = M.Map TypeID Type

-- An empty environment
emptyEnv :: Env
emptyEnv = M.empty

-- | Applies a substitution to a type
applySubstToType :: Subst -> Type -> Type
applySubstToType s (Forall typeVars body) = Forall (filter (\t -> M.notMember t s) typeVars) (applySubstToType s body)
applySubstToType s (TypeVar var) =
    case M.lookup var s of
        Just t -> t
        _ -> TypeVar var
applySubstToType s (Lambda t1 t2) = Lambda (applySubstToType s t1) (applySubstToType s t2)

-- | Applies a substitution to an environment
applySubstToEnv :: Subst -> Env -> Env
applySubstToEnv s env = M.map (applySubstToType s) env

-- | Computes the union of two substitutions
unionSubst :: Subst -> Subst -> Subst
unionSubst s1 s2 = M.union s1' s2'
    where
        -- Normalizes substitutions first
        s1' = M.map (applySubstToType s2 ) s1
        s2' = M.map (applySubstToType s1') s2

-- | Returns the set of free type variables in a type
freeTypeVars :: Type -> S.Set VarID
freeTypeVars (TypeVar var) = S.singleton var
freeTypeVars (Lambda t1 t2) = S.union (freeTypeVars t1) (freeTypeVars t2)
freeTypeVars (Forall bindings body) = S.filter (\k -> not $ elem k bindings) (freeTypeVars body)

-- | Generate a fresh new name
genName :: State InferState TypeID
genName = do
    n <- get
    put (n + 1)
    return ('?' : show n)

-- | Renames one type variable with a fresh skolem constant
rename :: TypeID -> State InferState (TypeID, Type)
rename var = do
    name <- genName
    return (var, TypeVar name)

-- | Skips the first "forall" in a type
skipForall :: Type -> Type
skipForall (Forall _ t) = t
skipForall t = t

-- | Abstracts over a type variable
makeForall :: [VarID] -> Type -> Type
makeForall newVars (Forall vars body) = Forall (vars ++ newVars) body
makeForall newVars t = Forall newVars t

-- | Returns the substitution that unifies two types
unify :: Type -> Type -> State InferState Subst
unify (TypeVar var1) t2 =
    case t2 of
        TypeVar _ -> return M.empty
        _         -> if S.member var1 (freeTypeVars t2)
            then error "Type variable occurs in right hand side"
            else return $ M.fromList [(var1, t2)]
unify t1 (TypeVar var2) = unify (TypeVar var2) t1
unify (Lambda t1 t2) (Lambda u1 u2) = do
    s1 <- unify t1 u1
    s2 <- unify (applySubstToType s1 t2) (applySubstToType s1 u2)
    return s2
unify (Forall vars1 body1) (Forall vars2 body2) = do
    (s1, rest1, s2, rest2) <- renameBoth vars1 vars2
    let renamed1 = abstract rest1 (applySubstToType (M.fromList s1) body1)
    let renamed2 = abstract rest2 (applySubstToType (M.fromList s2) body2)
    -- TODO: Escape check
    unify renamed1 renamed2
    where
        abstract [] t = t
        abstract vars t = makeForall vars t
        -- Rename both variables with the same fresh type constant.
        -- Returns the non-renamed variables as well as the substitution.
        renameBoth :: [TypeID] -> [TypeID] -> State InferState ([(TypeID, Type)], [TypeID], [(TypeID, Type)], [TypeID])
        renameBoth (v:v1) (w:v2) = do          
            (_, t) <- rename v
            (s1, _, s2, _) <- renameBoth v1 v2
            return $ ((v, t) : s1, [], (w, t) : s2, [])
        renameBoth v1 [] = return ([], v1, [], [])
        renameBoth [] v2 = return ([], [], [], v2)
unify t1 t2 = error $ "Cannot unify " ++ (show t1) ++ " and " ++ (show t2)

-- | Returns the substitution that makes two polymorphic types equal
subsume :: Type -> Type -> State InferState Subst
subsume (Forall vars1 body1) t = do
    renamed <- mapM rename vars1
    let subst = M.fromList renamed
    case t of
        Forall vars2 body2 -> do
            s <- unify (applySubstToType subst body1) body2
            -- TODO: Escape check
            return $ M.filterWithKey (\k _ -> not $ elem k vars2) s
        _ -> unify (applySubstToType subst body1) t
subsume t1 t2 = unify t1 (skipForall t2)

-- | Generalizes a type by abstracting over its free type variables
generalize :: Env -> Type -> Type
generalize env t = if vars == [] then t else makeForall vars t
    where
        vars = S.toList $ S.filter (\v -> not $ M.member v env) (freeTypeVars t)

-- | Creates a substitution to make the given type a lambda type
funMatch :: Type -> State InferState (Subst, Type)
funMatch t@(Lambda _ _) = return (M.empty, t)
funMatch (TypeVar var) = do
    t1 <- genName
    t2 <- genName
    let t = Lambda (TypeVar t1) (TypeVar t2)
    return (M.singleton var t, t)
funMatch t = error $ "Cannot make " ++ (show t) ++ " a lambda type"

-- | Splits a substitution in its monorphic and polymorphic counterparts
split :: Subst -> (Subst, Subst)
split s = (poly2, mono)
    where
        (poly1, mono) = M.partition isPoly s
        poly2 = M.map (\v -> skipForall v) poly1
        isPoly (Forall _ _) = True
        isPoly (Lambda from to) = (isPoly from) || (isPoly to)
        isPoly _ = False

-- | Infers the type of an expression
infer :: Env -> Expr -> State InferState (Subst, Type)
infer env (Var var) = return $
    case M.lookup var env of
        Just t -> (M.empty, t)
        _      -> error ("Cannot infer type of " ++ var)
-- Let statements
infer env (Let bindings body) = do
    (s1, t1) <- foldM processBinding (M.empty, []) bindings
    let bodyEnv = foldl (\curEnv (varId, varType) -> M.insert varId varType curEnv) (applySubstToEnv s1 env) t1
    (s2, t2) <- infer bodyEnv body
    return (unionSubst s1 s2, t2)
    where
        processBinding (subst, varTypes) (var, expr) = do
            (curSubst, curType) <- infer env expr
            return (unionSubst subst curSubst, (var, curType) : varTypes)
-- Lambda abstraction
infer env (Abs var optType body) = do
    varType <- case optType of
        Just t -> return t
        _      -> genName >>= (return . TypeVar)
    (s, typeBody) <- infer (M.insert var varType env) body
    let t = generalize (applySubstToEnv s env) (applySubstToType s (Lambda varType (skipForall typeBody)))
    return (s, t)
-- Lambda application
infer env (App e1 e2) = do
    (_, t0) <- infer env e1
    (s1, Lambda from to) <- funMatch $ skipForall t0
    (s2, t2) <- infer (applySubstToEnv s1 env) e2
    subsumed <- subsume (applySubstToType s2 from) t2
    let (poly3, mono3) = split subsumed 
    let s4 = unionSubst mono3 $ unionSubst s2 s1
    -- TODO: Check for polymorphic parameters
    let t = applySubstToType poly3 $ applySubstToType s4 to
    return (s4, generalize (applySubstToEnv s4 env) t)

