module V1 where

--------------------------------------------------------------------------------
--      Implementação mais simples de evolução e avaliação de expressões      --
--       evolution-aware, mas a maioria das operações funciona em O(N²)       --
--------------------------------------------------------------------------------

import Data.Map (Map, (!))
import qualified Data.Map as Map

data Expr
    = Lit Integer
    | Plus Expr Expr
    | Times Expr Expr
    deriving (Show, Eq, Ord)

subtreeSize :: Expr -> Int
subtreeSize (Lit x) = 1
subtreeSize (Plus x y) = 1 + subtreeSize x + subtreeSize y
subtreeSize (Times x y) = 1 + subtreeSize x + subtreeSize y

evolExpr :: Expr -> Int -> Expr -> Expr
evolExpr exp pos replacement =
    if pos == 1 then
        replacement
    else
        case exp of
        Lit x ->
            error "Posição inválida"

        Plus x y ->
            let xSz = subtreeSize x in
            if pos-1 <= xSz then
                Plus (evolExpr x (pos-1) replacement) y
            else
                Plus x (evolExpr y (pos-1-xSz) replacement)

        Times x y ->
            let xSz = subtreeSize x in
            if pos-1 <= xSz then
                Times (evolExpr x (pos-1) replacement) y
            else
                Times x (evolExpr y (pos-1-xSz) replacement)

eval :: Expr -> Integer
eval (Lit x) = x
eval (Plus x y) = eval x + eval y
eval (Times x y) = eval x * eval y

evalEA :: Map Expr Integer -> Expr -> Map Expr Integer
evalEA memo exp =
    case Map.lookup exp memo of
    Just answer -> memo -- sem mudanças ao memo
    Nothing ->
        case exp of
        Lit x ->
            Map.insert (Lit x) x memo
        
        Plus x y ->
            let memo1 = evalEA memo x in
            let memo2 = evalEA memo1 y in
            let ans = (memo2 ! x) + (memo2 ! y) in
            Map.insert (Plus x y) ans memo2

        Times x y ->
            let memo1 = evalEA memo x in
            let memo2 = evalEA memo1 y in
            let ans = (memo2 ! x) * (memo2 ! y) in
            Map.insert (Times x y) ans memo2

exp1 = (Lit 1 `Plus` Lit 2) `Times` (Lit 3 `Plus` Lit 4)
map = evalEA Map.empty exp1
exp2 = evolExpr exp1 5 (Lit 100)
evalEA map exp2

exp3 = foldl (\x y -> x `Plus` (Lit y)) (Lit 0) [1..10000]
