{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module InhabTree where

import Data.List
import Text.ParserCombinators.ReadP

-- Base data types
infixl 2 :@
infixr 3 :->

-- For readability purpose
type Symb = String 

-- Lambda term
data Expr = 
    Var Symb 
    | Expr :@ Expr
    | Lam Symb Expr
        deriving Eq

-- to show the resulting expressions
instance Show Expr where
    showsPrec _ = showsLambdaTerm basePrec where
        basePrec = 0
        leftPrec = 1
        rightPrec = 2
        lamPrec = 3

        showsLambdaTerm d (Var c)
            | d == lamPrec   = showString "-> " .
                showString c
            | otherwise      = showString c
        showsLambdaTerm d m@(l :@ r) 
            | d == lamPrec   = showString "-> " .
                showsLambdaTerm basePrec m
            | otherwise      = showParen (d == rightPrec) $
                showsLambdaTerm leftPrec l .
                showChar ' ' .
                showsLambdaTerm rightPrec r
        showsLambdaTerm d (Lam c b)
            | d == lamPrec  = showString c .
                showChar ' ' .
                showsLambdaTerm lamPrec b
            | otherwise     = showParen (d == leftPrec) $
                showChar '\\' .
                showString c .
                showChar ' ' .
                showsLambdaTerm lamPrec b


-- Type variable
data Type = 
    TVar Symb 
    | Type :-> Type
        deriving Eq

-- instantiating Read for types so we have an okay text input
skipWhitespaces = do 
    many (choice (map char [' ', '\n'])) 
    return ()
addBrackets p = do 
    skipWhitespaces
    char '('
    r <- p
    skipWhitespaces
    char ')'
    return r
parseTVar = do 
    skipWhitespaces
    s <- many1 (choice (map char $ ['a'..'z'] ++ ['0'..'9']))
    return (TVar s)
parseArrowType = do 
    a <- (parseTVar +++ addBrackets parseType)
    skipWhitespaces
    char '-'
    char '>'
    b <- parseType
    return (a :-> b)
parseType = parseTVar +++ parseArrowType +++ addBrackets parseType

instance Read Type where
    readsPrec _ = readP_to_S parser where
        parser = do 
            res <- parseTVar +++ parseArrowType +++ addBrackets parseType
            skipWhitespaces
            return res

-- Context
newtype Env = Env [(Symb,Type)]
  deriving Eq

-- Empty context
emptyEnv :: Env
emptyEnv = Env []

-- Making types orderable so the context will be length-sorted
instance Ord Type where
    compare (TVar a)  (TVar b)    = compare a b
    compare x        (TVar _)     = GT
    compare (TVar _)  y           = LT
    compare (a :-> b) (a' :-> b') = 
        let compareArg = compare a a'
            compareRes = compare b b' 
        in if compareArg == EQ 
            then compareRes
            else compareArg

-- Context extension
extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env cs) s t = Env $ insertBy cmpTypes (s,t) cs
   where cmpTypes (_,t1) (_,t2) = compare t1 t2

-- Inhabitation-related functions

-- Get fresh var
getFreshVar :: Integer -> (Integer, Expr)
getFreshVar n = (n + 1, Var $ "x" ++ show n)

-- Get terms from context that have return type, matching pattern
properEnvTypes :: Env -> Type -> Env
properEnvTypes (Env cs) tau = 
    Env $ filter (\(x,t) -> hasPartialRetTypeVar tau t) cs

-- Check whether the type variable got as the first argument
-- is a partial return type for the second
hasPartialRetTypeVar :: Type -> Type -> Bool
hasPartialRetTypeVar pattern t@(t1 :-> t2) = 
    pattern == t 
        || pattern == t2 
        || hasPartialRetTypeVar pattern t2
hasPartialRetTypeVar pattern t = 
    pattern == t

-- Get argument type variable which we need to apply to the second argument
-- to get the pattern from the first argument
getArgTypeVars :: Type -> Type -> [Type]
getArgTypeVars p (TVar _) = []
getArgTypeVars p t@(t1 :-> t2) 
    | hasPartialRetTypeVar p t2 = (t1:getArgTypeVars p t2)
    | otherwise                 = []

-- Inhabitation itself
-- Algorithm: 
-- inhab (env, a :-> b) = {forall e in (inhab (env + {a : a'}, b))}
-- inhab (env, a) -- we find terms x in our context of type 
-- (x1 :-> x2 :-> ... :-> xn :-> a) and inhabit each argument type. For each term ti of 
-- type xi we then costruct term of type a in the following manner: 
-- x t1 t2 ... tn

-- Inhabitation process will be in form of BFS over inhabitation tree so it
-- will produce shortest terms first --- needed because of infinite terms
-- We will store information about current state of inhabitation in a tree-like
-- structure
data GenTree =
    Nil                                 -- represents empty tree
    | Path Env Type (Expr -> Expr)      -- represents an abstraction
    | Union [GenTree] (Expr -> Expr)    -- represents union of generation trees
                                        -- implemented for convenience
    | GenArgs [GenTree] Expr            -- represents generation of argument 
                                        -- types

-- utility function
pathMap :: (Expr -> Expr) -> GenTree -> GenTree
pathMap f (Path gamma alpha g) = Path gamma alpha (f . g)
pathMap _ _ = undefined

-- because we cannot instantiate Eq GenTree because of having functions inside
isNil :: GenTree -> Bool
isNil Nil = True
isNil _ = False

-- proceed to the next state of our generation tree
nxt :: GenTree -> Integer -> (Integer, [Expr], GenTree)
nxt Nil s = (s, [], Nil)
nxt (Path env (t1 :-> t2) f) s = (s', [], Path env' t2 f') where 
    (s', Var x) = getFreshVar s
    env' = extendEnv env x t1
    f' = f . Lam x
nxt (Path gamma alpha f) s = (s, [], Union trees f) where 
    Env propers = properEnvTypes gamma alpha
    processProper (x, tau) = gt where
        args = map (flip (Path gamma) id) (getArgTypeVars alpha tau)
        gt = case args of 
            [arg] -> pathMap ((Var x) :@) arg 
            _ -> GenArgs args (Var x)
    trees = map processProper propers
nxt (Union trees f) s = (s', exprs, gt) where
    (s', exprs, nxtTrees) = foldl helper (s, [], []) (filter (not . isNil) trees)
    helper (s, l, ts) gt = (s', l ++ map f exprs, gt':ts) where
        (s', exprs, gt') = nxt gt s
    gt = if null nxtTrees then Nil else Union nxtTrees f
nxt (GenArgs [] e) s = (s, [e], Nil)
nxt (GenArgs (t:ts) e) s = (s', [], gt) where
    (s', exprs1, t') = nxt t s
    ts' = (if isNil t' then [] else [GenArgs (t':ts) e]) 
        ++ map ((GenArgs ts) . (e :@)) exprs1
    gt = case ts' of [t'] -> t'
                     ts' -> Union ts' id

-- repeat nxt (possibly infinitey) to get list of terms generated by tree
nxtRepeated :: GenTree -> Integer -> [Expr]
nxtRepeated Nil _ = []
nxtRepeated gt s = exprs ++ nxtRepeated gt' s' where
    (s', exprs, gt') = nxt gt s

-- inhabitation using generation trees
inhabTree :: Env -> Type -> [Expr]
inhabTree gamma alpha = nxtRepeated (Path gamma alpha id) 1

-- inhabitation on empty context (we get closed terms in that case)
inhabTree0 :: Type -> [Expr]
inhabTree0 alpha = inhabTree (Env []) alpha

-- examples
{-
> inhabTree0 (TVar "a")
[]
> inhabTree0 (TVar "a" :-> TVar "a")
[(\x1 -> x1)]
> inhabTree0 (TVar "a" :-> TVar "b")
[]
> inhabTree0 (TVar "a" :-> TVar "a" :-> TVar "a")
[(\x1 x2 -> x2),(\x1 x2 -> x1)]
> inhabTree0 (TVar "a" :-> TVar "a" :-> TVar "a" :-> TVar "a")
[(\x1 x2 x3 -> x3),(\x1 x2 x3 -> x2),(\x1 x2 x3 -> x1)]
> inhabTree0 (TVar "a" :-> TVar "b" :-> TVar "a" :-> TVar "a")
[(\x1 x2 x3 -> x3),(\x1 x2 x3 -> x1)]
-- Church numbers
> take 5 $ inhabTree0 $ (TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"
[(\x1 x2 -> x2),(\x1 x2 -> x1 x2),(\x1 x2 -> x1 (x1 x2)),(\x1 x2 -> x1 (x1 (x1 x2))),(\x1 x2 -> x1 (x1 (x1 (x1 x2))))]
-- everything ok --- x1 found
> take 5 $ inhabTree0 $ (TVar "a" :-> TVar "a") :-> (TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"
[(\x1 x2 x3 -> x3),(\x1 x2 x3 -> x2 x3),(\x1 x2 x3 -> x1 x3),(\x1 x2 x3 -> x2 (x2 x3)),(\x1 x2 x3 -> x2 (x1 x3))]
-- binary trees type
> take 6 $ inhabTree0 $ (TVar "a" :-> TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"
[(\x1 x2 -> x2),(\x1 x2 -> x1 x2 x2),(\x1 x2 -> x1 ((x1 x2) x2) x2),(\x1 x2 -> x1 x2 ((x1 x2) x2)),(\x1 x2 -> x1 x2 ((x1 ((x1 x2) x2)) x2)),(\x1 x2 -> x1 x2 ((x1 x2) ((x1 x2) x2)))]
-- Third order types: number of abstractions grows infinitely 
> take 6 $ inhabTree0 $ ((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a"
[(\x1 -> x1 \x2 -> x2),(\x1 -> x1 \x2 -> x1 \x3 -> x3),(\x1 -> x1 \x2 -> x1 \x3 -> x2),(\x1 -> x1 \x2 -> x1 \x3 -> x1 \x4 -> x4),(\x1 -> x1 \x2 -> x1 \x3 -> x1 \x4 -> x3),(\x1 -> x1 \x2 -> x1 \x3 -> x1 \x4 -> x2)]
-- fmap for Cont monad
> inhabTree0 $ (TVar "a" :-> TVar "b") :-> ((TVar "a" :-> TVar "c") :-> TVar "d") :-> (TVar "b" :-> TVar "c") :-> TVar "d"
[(\x1 x2 x3 -> x2 \x4 -> x3 (x1 x4))]
-- fmap for Sel monad
> take 3 $ inhabTree0 $ (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "a") :-> (TVar "b" :-> TVar "c") :-> TVar "b"
[(\x1 x2 x3 -> x1 (x2 \x4 -> x3 (x1 x4))),(\x1 x2 x3 -> x1 (x2 \x4 -> x3 (x1 (x2 \x5 -> x3 (x1 x5))))),(\x1 x2 x3 -> x1 (x2 \x4 -> x3 (x1 (x2 \x5 -> x3 (x1 x4)))))]
-- "monster" type is also handled correctly
> take 5 $ inhabTree0 $ (((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a") :-> TVar "a" :-> TVar "a"
[(\x1 x2 -> x2),(\x1 x2 -> x1 \x3 -> x2),(\x1 x2 -> x1 \x3 -> x3 x2),(\x1 x2 -> x1 \x3 -> x1 \x4 -> x2),(\x1 x2 -> x1 \x3 -> x3 (x3 x2))]
-}
