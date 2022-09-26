{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

--------------------------------------------------------------------------------
--           Implementação de operações em expressões variacionais            --
--------------------------------------------------------------------------------

module Exp where

import Data.Generics
import Choice ( V(Obj, Dim, Chc) )

import Data.Map (Map)
import qualified Data.Map as Map

newtype VarName = VN String
    deriving (Eq, Ord, Show, Read, Data, Typeable)

data Exp
    = Value Int
    | Var VarName
    | Plus Exp Exp
    | Times Exp Exp
    | Pwr Exp Exp
    | EVariation (V Exp)
    deriving (Eq, Ord, Show, Read, Data, Typeable)

applyOp :: (a -> b -> c) -> V a -> V b -> V c
applyOp op l r = do
    x <- l
    y <- r
    return $ x `op` y

unwrap (Just x) = x

eval :: Map VarName (V Int) -> Exp -> V Int
eval ctx (Value x) = Obj x
eval ctx (Var x) = unwrap $ Map.lookup x ctx
eval ctx (Plus l r) = applyOp (+) (eval ctx l) (eval ctx r)
eval ctx (Times l r) = applyOp (*) (eval ctx l) (eval ctx r)
eval ctx (Pwr l r) = applyOp (^) (eval ctx l) (eval ctx r)
eval ctx (EVariation v) = eval ctx =<< v

optLits (Plus (Value x) (Value y)) = Value (x + y)
optLits (Times (Value x) (Value y)) = Value (x * y)
optLits (Pwr (Value x) (Value y)) = Value (x ^ y)
optLits other = other

optTimes (Times (Value 0) r) = Value 0
optTimes (Times l (Value 0)) = Value 0
optTimes (Times (Value 1) r) = r
optTimes (Times l (Value 1)) = l
optTimes other = other

optPwr (Pwr (Value 0) _) = Value 0 
optPwr (Pwr _ (Value 0)) = Value 1
optPwr (Pwr (Value 1) _) = Value 1
optPwr (Pwr l (Value 2)) = (Times l l)
optPwr other = other

optimize :: Exp -> Exp
optimize = everywhere (mkT $ optPwr . optTimes . optLits)

sum1 :: Int -> Int
sum1 = (+1)

ex = EVariation $
    Dim "Op" ["1", "2"] $
    Chc "Op" [
        Obj $ Value 5 `Pwr` (Value 1 `Plus` Value 1),
        Obj $ Value 2 `Times` ((Value 1 `Plus` Value (-1)) `Times` (Var $ VN "x"))
    ]

