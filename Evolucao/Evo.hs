{-# LANGUAGE FlexibleInstances #-}

--------------------------------------------------------------------------------
--           Implementação de evolução e avaliação evolution-aware,           --
--           com evolução em O(N). A avaliação ainda roda em tempo            --
--          quadrático, porque cada lookup de expressão no cache/map          --
--                              executa em O(N)!                              --
--------------------------------------------------------------------------------

module Evo where

import Choice

data BinOp = Plus | Times | Pwr

-- Constraints: Se `val` é um Just, todos os `val`s da subárvore devem ser `Just`s
-- Mesma coisa para o stsize
data Memoized a b = Memoized { struct::a, val::Maybe (V b), stsize::Maybe Int }

type MemoExpr = Memoized Expr Integer
data Expr
    = Lit Integer
    | BinOp BinOp MemoExpr MemoExpr
    | Variation (V MemoExpr)

-- Show instances {{{
showMaybe Nothing = ""
showMaybe (Just x) = show x

showBinOp op = case op of
    Plus -> "+"
    Times -> "*"
    Pwr -> "^"

instance Show Expr where
    show (Lit x) = show x
    show (BinOp op x y) = "(" ++ show x ++ " " ++ showBinOp op ++ " " ++ show y ++ ")"
    show (Variation v) = "Variation ~\n" ++ (indent $ show v)

instance Show (Memoized Expr Integer) where
    show (Memoized { struct = s, val = v, stsize = sz }) =
        "{" ++ show s ++ "}[v=" ++ showMaybe v ++ ", sz=" ++ showMaybe sz ++ "]"

-- }}}

wrap :: Expr -> MemoExpr
wrap e = Memoized { struct = e, val = Nothing, stsize = Nothing }

unwrap (Just x) = x

-- Smart constructors
lit x = wrap $ Lit x
plus x y = wrap $ BinOp Plus x y
times x y = wrap $ BinOp Times x y
pwr x y = wrap $ BinOp Pwr x y

-- Evolução {{{
getStsize = unwrap . stsize

buildSubtreeSize :: MemoExpr -> MemoExpr
buildSubtreeSize m@(Memoized { struct = _, val = _, stsize = Just sz }) = m
buildSubtreeSize m@(Memoized { struct = s, val = _, stsize = Nothing }) = case s of
    Lit _ ->
        m{ stsize = Just 1 }

    BinOp op x y ->
        let x' = buildSubtreeSize x
            y' = buildSubtreeSize y
        in m{ struct = BinOp op x' y', stsize = Just $ 1 + getStsize x' + getStsize y' }

    Variation v ->
        let (v', sz) = vBuildSubtreeSize v
        in m{ struct = Variation v', stsize = Just $ 1 + sz }

vBuildSubtreeSize :: V MemoExpr -> (V MemoExpr, Int)
vBuildSubtreeSize v = case v of
    Obj x ->
        let x' = buildSubtreeSize x
        in (Obj x', getStsize x')

    Dim name chcs body ->
        let (body', sz) = vBuildSubtreeSize body
        in (Dim name chcs body', sz)

    Chc name bodies ->
        let results = vBuildSubtreeSize <$> bodies 
            combine (a, x) (b, y) = (a : b, x + y)
            (bodies', sz) = foldr combine ([], 0) results
        in (Chc name bodies', sz) 

replaceBodyInPos :: [V MemoExpr] -> Int -> MemoExpr -> ([V MemoExpr], Int)
replaceBodyInPos [] _pos _replacement =
    error "Posição inválida"
replaceBodyInPos (body : bodies) pos replacement =
    let (body', sz) = evolV body pos replacement in
    if pos <= sz then
        -- replacement made
        let bodiesSz = sum (map (snd . vBuildSubtreeSize) bodies) in
        (body' : bodies, sz + bodiesSz)
    else
        -- replacement should be made in another body
        let (rest, restSz) = replaceBodyInPos bodies (pos - sz) replacement in
        (body : rest, sz + restSz)

-- retorna (nova expressão com variabilidade, tamanho da subárvore)
evolV :: V MemoExpr -> Int -> MemoExpr -> (V MemoExpr, Int)
evolV v pos replacement =
    let (v', sz) = vBuildSubtreeSize v in -- ! não está memoizado, então fica quadrático
    case v' of
    Obj x ->
        if pos <= getStsize x then
            let x' = evolExp x pos replacement in
            (Obj x', getStsize x')
        else
            (Obj x, getStsize x)

    Dim name chcs body ->
        let (body', sz) = evolV body pos replacement in
        (Dim name chcs body', sz)

    Chc name bodies ->
        let (bodies', sz) = replaceBodyInPos bodies pos replacement
        in (Chc name bodies', sz)

evolExp :: MemoExpr -> Int -> MemoExpr -> MemoExpr
evolExp exp pos replacement =
    let exp' = buildSubtreeSize exp in
    let s = struct exp' in
    if pos == 1 then
        buildSubtreeSize replacement
    else
        case s of
        Lit x ->
            error "Posição inválida" -- agora `pos /= 1`

        BinOp op x y ->
            if getStsize x >= pos-1 then
                let newx = evolExp x (pos-1) replacement in
                exp'{ struct = BinOp op newx y, val = Nothing,
                      stsize = Just $ 1 + getStsize newx + getStsize y }
            else
                let newy = evolExp y (pos-1-(getStsize x)) replacement in
                exp'{ struct = BinOp op x newy, val = Nothing,
                      stsize = Just $ 1 + getStsize x + getStsize newy }

        Variation v ->
            let (newv, sz) = evolV v (pos-1) replacement in
            exp'{ struct = Variation newv, val = Nothing,
                  stsize = Just $ 1 + sz }

-- }}}

-- Avaliação {{{
getVal :: Memoized a b -> V b
getVal = unwrap . val

applyBinOp :: BinOp -> Integer -> Integer -> Integer
applyBinOp op = case op of
    Plus -> (+)
    Times -> (*)
    Pwr -> (^)

naiveEval :: MemoExpr -> V Integer
naiveEval (Memoized { struct = s }) = case s of
    Lit x -> Obj x
    BinOp op x y -> applyVariadicBinOp op (naiveEval x) (naiveEval y)

applyVariadicBinOp :: BinOp -> V Integer -> V Integer -> V Integer
applyVariadicBinOp op x y = do
    x' <- x
    y' <- y
    return $ applyBinOp op x' y'

eval :: MemoExpr -> MemoExpr
eval m = case m of
    Memoized { struct = _, val = Just x } ->
        m

    Memoized { struct = (Lit x), val = Nothing } ->
        m{ val = Just (Obj x) }

    Memoized { struct = (BinOp op x y), val = Nothing } ->
        let x' = eval x
            y' = eval y in
        m{ struct = (BinOp op x' y'),
           val = Just $ applyVariadicBinOp op (getVal x') (getVal y') }

    Memoized { struct = (Variation v), val = Nothing } ->
        let v' = eval <$> v in
        m{ struct = Variation v', val = Just (getVal =<< v') }

eval' :: MemoExpr -> V Integer
eval' = getVal . eval

-- }}}

-- (10 + 20) * (2 ^ 3)
exp1 = (lit 10 `plus` lit 20) `times` (lit 2 `pwr` lit 3)

exp2 = eval $ foldr (\x y -> lit x `plus` y) (lit 0) [1..10000]
exp2Changes = map (\x -> eval $ evolExp exp2 2 (lit x)) [1..10000]
naiveExp2Changes = map (\x -> naiveEval $ evolExp exp2 2 (lit x)) [1..10000]

-- sum (getVal <$> exp2Changes)
-- sum naiveExp2Changes

chcA = wrap $ Variation $ Chc "A" [ Obj (lit 1 `plus` lit 2), Obj (lit 5) ]
chcB = wrap $ Variation $ Chc "B" [ Obj (lit 10 `plus` lit 20), Obj (lit 50) ]
exp3 = wrap $ Variation
     $ Dim "A" ["1 plus 2", "5"]
     $ Dim "B" ["10 plus 20", "50"]
     $ Obj $ (lit 100) `times` (chcA `plus` chcB) 

exp3' = evolExp exp3 4 (lit 12345)

-- Desvantagem: você tem que lembrar de avaliar antes de evoluir a expressão
-- Alternativa: fazer um build só, que avalia e calcula tamanhos de subárvore

-- Desvantagem: cada valor memoizado é uma árvore, então talvez eu esteja
-- utilizando O(N²) de memória para fazer a memoização, não tenho certeza.
