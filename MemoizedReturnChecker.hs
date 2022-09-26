{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
module ReturnChecker where

import Data.Generics (Data, Typeable, everything, extQ)
import Data.Typeable (cast)

import Data.Map (Map, (!))
import qualified Data.Map as Map

import LexLI
import ParLI
import AbsLI
import Desugar
import PrintLI
import ErrM

unwrap (Ok x) = x
unwrap (Bad y) = y

unsafeCast x =
    let (Just y) = cast x
    in y

main = do
    interact (unwrap . check)
    putStrLn ""

check :: String -> Err String
check source = do
    ast <- pProgram (myLexer source)
    let astCore = desugarP ast
        in return $
            printTree astCore ++ "\n"
            ++ show (returnDensity astCore)

--------------------------------------------------------------------------------
--                      Return Checker (Sem Memoização)                       --
--------------------------------------------------------------------------------
checkReturnS :: Stm -> Bool
checkReturnS stm = case stm of
    SReturn _ -> True
    SWhile _ stm -> checkReturnS stm
    SBlock stms -> or (map checkReturnS stms)
    SIf _ sIf sElse -> checkReturnS sIf && checkReturnS sElse
    _ -> False

checkReturnF :: Function -> (Ident, Bool)
checkReturnF fn =
    let (Fun retType name decls stms) = fn in
    if retType == Tvoid then
        (name, True)
    else
        let ok = checkReturnS (SBlock stms)
        in (name, ok)

checkReturn :: Program -> [(Ident, Bool)]
checkReturn (Prog fns) = map checkReturnF fns

--------------------------------------------------------------------------------
--                         Return Checker (Memoizado)                         --
--------------------------------------------------------------------------------
--
-- Nessa implementação, as funções que verificam os returns retornam um `Map Stm Bool`.
-- A chamada `checkReturnSEA cache stm`, por exemplo, retorna o `cache` atualizado com o
-- resultado do return checker (verdadeiro ou falso) associado ao statment `stm`.
--
-- Um modo mais elegante e menos trabalhoso de realizar a mesma tarefa é utilizar
-- um monad de estado, onde o Map Stm Bool é o estado.
-- Esse monad é descrito muito bem na seção "Tasteful stateful computations" do
-- Learn You A Haskell: https://learnyouahaskell.com/for-a-few-monads-more
--

cached :: Ord a => (Map a r -> a -> Map a r) -> Map a r -> a -> Map a r
cached fn cache input = case Map.lookup input cache of
    Just _ -> cache -- no changes to the cache
    Nothing -> fn cache input -- let `fn` make changes to the cache

(-<) :: Ord a => (a -> Map a r) -> a -> (Map a r, r)
(-<) fn input =
    let cache = fn input in
    (cache, cache ! input)

orFolder (c, r) stm =
    let (c', r') = checkReturnSEA c -< stm in
    (c', r || r')

-- checkReturn (Statement, Evolution-Aware)
checkReturnSEA :: Map Stm Bool -> Stm -> Map Stm Bool
checkReturnSEA = cached $ \cache stm ->
    case stm of
    SWhile _ stm' ->
        let (cache1, res) = checkReturnSEA cache -< stm'
        in Map.insert stm res cache1
    SBlock stms ->
        let (cache1, res) = foldl orFolder (cache, False) stms
        in Map.insert stm res cache1
    SIf _ sIf sElse ->
        let (cache1, resIf) = checkReturnSEA cache -< sIf
            (cache2, resElse) = checkReturnSEA cache1 -< sElse
        in Map.insert stm (resIf && resElse) cache2
    SReturn _ ->
        Map.insert stm True cache
    _ ->
        Map.insert stm False cache

-- checkReturn (Function, Evolution-Aware)
checkReturnFEA :: Map Stm Bool -> Function -> (Ident, Bool, Map Stm Bool)
checkReturnFEA cache fn =
    let (Fun retType name decls stms) = fn in
    if retType == Tvoid then
        (name, True, cache)
    else
        let (cache', ok) = checkReturnSEA cache -< (SBlock stms)
        in (name, ok, cache')

checkFolder (bs, c) fn =
    let (i, b, c') = checkReturnFEA c fn in
    ((i, b) : bs, c')

-- checkReturn (Evolution-Aware)
checkReturnEA :: Map Stm Bool -> Program -> ([(Ident, Bool)], Map Stm Bool)
checkReturnEA cache (Prog fns) =
    foldl checkFolder ([], cache) fns

--------------------------------------------------------------------------------
--                                  Evolução                                  --
--------------------------------------------------------------------------------
-- Representa um caminho partindo da raíz de uma árvore.
-- Cada elemento n da lista indica que devemos ir para
-- o n-ésimo filho do nó.
-- Note que `n` é indexado em 1
type Path = [Int]

replaceList :: [a] -> Int -> a -> [a]
replaceList xs n x =
    let left = take (n-1) xs
        right = drop n xs
    in left ++ (x : right)

replaceP :: Typeable a => Program -> Path -> a -> Program
replaceP program [] replacement = unsafeCast replacement
replaceP (Prog fns) (n:ns) replacement =
    let replaced = replaceF (fns !! (n-1)) ns replacement
    in Prog (replaceList fns n replaced)

replaceF :: Typeable a => Function -> Path -> a -> Function
replaceF function [] replacement = unsafeCast replacement 
replaceF (Fun typ ident decls stmts) (n:ns) replacement =
    if n <= length decls then
        Fun typ ident (replaceList decls n (unsafeCast replacement)) stmts
    else
        let n' = n - length decls
            replaced = replaceS (stmts !! (n-1)) ns replacement
        in Fun typ ident decls (replaceList stmts n' replaced)

replaceS :: Typeable a => Stm -> Path -> a -> Stm
replaceS stm [] replacement = unsafeCast replacement
replaceS stm (n:ns) replacement =
    case stm of
    SDec _ -> unsafeCast replacement
    SDecls typ ident idents ->
        SDecls typ ident (replaceList idents n (unsafeCast replacement))
    CDec _ _ _ -> unsafeCast replacement
    SAss _ _ -> unsafeCast replacement
    SBlock stms ->
        let replaced = replaceS (stms !! (n-1)) ns replacement
        in SBlock (replaceList stms n replaced)
    SWhile exp stm ->
        if n == 1 then
            SWhile (replaceE exp ns replacement) stm
        else
            SWhile exp (replaceS stm ns replacement)
    SReturn exp -> SReturn (replaceE exp ns replacement) 
    SIf exp stmIf stmElse ->
        if n == 1 then
            SIf (replaceE exp ns replacement) stmIf stmElse
        else if n == 2 then
            SIf exp (replaceS stmIf ns replacement) stmElse
        else
            SIf exp stmIf (replaceS stmElse ns replacement)

replaceBinaryExp :: Typeable a => (Exp -> Exp -> Exp) -> Exp -> Exp -> Path -> a -> Exp
replaceBinaryExp ctor l r (n:ns) replacement =
    if n == 1 then
        ctor (replaceE l ns replacement) r 
    else
        ctor l (replaceE r ns replacement)

replaceE :: Typeable a => Exp -> Path -> a -> Exp
replaceE exp [] replacement = unsafeCast replacement
replaceE exp (n:ns) replacement =
    case exp of
    EOr l r  -> replaceBinaryExp EOr l r (n:ns) replacement
    EAnd l r -> replaceBinaryExp EAnd l r (n:ns) replacement
    ENot x   -> ENot (replaceE x ns replacement)
    ECon l r -> replaceBinaryExp ECon l r (n:ns) replacement
    EAdd l r -> replaceBinaryExp EAdd l r (n:ns) replacement
    ESub l r -> replaceBinaryExp ESub l r (n:ns) replacement
    EMul l r -> replaceBinaryExp EMul l r (n:ns) replacement
    EDiv l r -> replaceBinaryExp EDiv l r (n:ns) replacement
    Call ident exps ->
        let replaced = replaceE (exps !! (n-1)) ns replacement
        in Call ident (replaceList exps n replaced)
    EInt _ -> EInt (unsafeCast replacement)
    EVar _ -> EVar (unsafeCast replacement)
    EStr _ -> EStr (unsafeCast replacement)
    ETrue  -> unsafeCast replacement
    EFalse -> unsafeCast replacement

ex1 = Prog [Fun Tvoid (Ident "main") [] [CDec Tint (Ident "x") (EInt 2),SDec (Dec Tint (Ident "y")),SDec (Dec Tint (Ident "z")),SAss (Ident "y") (EAdd (EAdd (EVar (Ident "x")) (EInt 20)) (EInt 3)),SIf (EVar (Ident "x")) (SAss (Ident "y") (EInt 200)) (SAss (Ident "y") (EInt 1000)),SAss (Ident "z") (EAdd (EAdd (EInt 1) (EInt 2)) (EVar (Ident "y")))]]

ex1' = replaceP ex1 [1,1] (SBlock [])

--------------------------------------------------------------------------------
--                   Média de Returns por Função Declarada                    --
--------------------------------------------------------------------------------
cachedSumFolder (c, s) stm =
    let (c', s') = returnDensityS c -< stm in
    (c', s + s')

returnDensityS = cached $ \cache stm ->
    case stm of
    SReturn _ -> Map.insert stm 1 cache
    SWhile _ stm' ->
        let (cache', s) = returnDensityS cache -< stm' -- '
        in Map.insert stm s cache'
    SBlock stms ->
        let (cache', s) = foldl cachedSumFolder (cache, 0) stms
        in Map.insert stm s cache'
    SIf _ sIf sElse -> 
        let (cache1, resIf) = returnDensityS cache -< sIf
            (cache2, resElse) = returnDensityS cache1 -< sElse
        in Map.insert stm (resIf + resElse) cache2
    _ -> Map.insert stm 0 cache

returnDensityF cache (Fun retType name decls stms) =
    let (cache', sum) = returnDensityS cache -< (SBlock stms)
    in (name, sum, cache')

returnDensity :: Program -> Float
returnDensity (Prog fns) =
    let rets = map (returnDensityF Map.empty) fns in
    let sum' = sum (map (\(_, s, _) -> s) rets) in
    fromIntegral sum' / fromIntegral (length rets)
