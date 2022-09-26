module Expression where 

import Data.Map (Map, (!))
import qualified Data.Map as Map

data Expr
    = EVal Integer
    | EVar String
    | EAdd Expr Expr
    | ESub Expr Expr
    | EMul Expr Expr
    | EDiv Expr Expr
    | ECond Expr Expr Expr

type Context = Map String Integer

eval :: Context -> Expr -> Integer
eval ctx (EVal v) = v
eval ctx (EVar x) = ctx ! x
eval ctx (EAdd l r) = eval ctx l + eval ctx r
eval ctx (ESub l r) = eval ctx l - eval ctx r
eval ctx (EMul l r) = eval ctx l * eval ctx r
eval ctx (EDiv l r) = eval ctx l `div` eval ctx r
eval ctx (ECond c l r) = if eval ctx c /= 0
                         then eval ctx l
                         else eval ctx r


expr =
    ECond (EMul (EVar "x") (EVar "y"))
            (EVal 100)
            (EVal 1234)

