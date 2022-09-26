module Main where

import Choice
import Control.Monad.State.Lazy
import Data.Map (Map)
import qualified Data.Map as Map

type Memo a b = State (Map a b)
-- type FMemo a b = a -> Memo a b

-- não dá pra memoizar (a -> b) !!
-- fmapM :: (a -> b, List a) -> Memo (a -> b, List a) (List b)

-- incmapM :: (Int -> Int) -> [Int] -> Memo [Int] [Int]
incmapM [] = pure [] 
incmapM f (x : xs) = pure (:) <*> pure (f x) <*> (incmapM xs)

-- Observação interessante: eu só uso do notation abaixo
-- então é possível que funcione pra outros monads, não só V! 

data Op = Plus | Times
applyOp op x y = do
    x' <- x
    y' <- y
    return (case op of
            Plus -> x' + y'
            Times -> x' * y')

data Expr
    = Lit Int
    | Op Op Expr Expr
    | VCase (V Expr)

eval' :: Expr -> Memo Expr (V Int)
eval' e = case e of
    Lit x -> do return x
    Op op x y -> applyOp op (eval x) (eval y)

eval :: Expr -> V Int
eval e = case e of
    Lit x -> do return x
    Op op x y -> applyOp op (eval x) (eval y)
    VCase v -> eval =<< v

-- cached :: (a -> Memo a r -> Memo a r) -> a -> Memo a r -> Memo a r
-- cached fn input cache = do
--     cache' <- get cache
--     case Map.lookup input cache' of
--     Just x -> -- no changes to the cache
--         return x
--     Nothing -> -- let `fn` make changes to the cache
--         res <- fn input cache
--         return res

-- evalM :: Expr -> Memo Expr (V Int) -> Memo Expr (V Int)
-- evalM = cached $ \e cache ->
--     case e of
--     Lit x ->

-- exp1 = Op Times (Lit 10) (VCase
--      $ Dim "A" ["2", "5"]
--      $ Chc "A" [Obj (Lit 2), Obj (Lit 5)])

main = putStrLn "Hello World!"


