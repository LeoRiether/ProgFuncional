{-# LANGUAGE FlexibleInstances, DeriveDataTypeable, StandaloneDeriving  #-}

module Choice where

import Data.Generics

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List ((!!))

-- V a {{{
type DimName = String
type ChcName = String

data V a
    = Obj a
    | Dim DimName [ChcName] (V a)
    | Chc DimName [V a]
    deriving (Eq, Ord, Show, Read, Data, Typeable)

instance Functor V where -- {{{
    fmap f (Obj x) = Obj (f x)
    fmap f (Dim name choices body) = Dim name choices (fmap f body)
    fmap f (Chc name bodies) = Chc name (map (fmap f) bodies)
-- }}}

instance Applicative V where -- {{{
    pure = Obj
    (Obj f) <*> x = f <$> x
    (Dim name choices body) <*> x =
        Dim name choices (body <*> x)
    (Chc name bodies) <*> x =
        Chc name (map (<*> x) bodies)
-- }}}

instance Monad V where -- {{{
    return = Obj
    (Obj x) >>= f = f x
    (Dim name choices body) >>= f =
        Dim name choices (body >>= f)
    (Chc name bodies) >>= f =
        Chc name (map (>>= f) bodies)
-- }}}

-- V Selectable typeclass & implementation (select) {{{
class Selectable a where
    select :: DimName -> Int -> a -> a

instance Selectable a => Selectable (V a) where
    select d i (Obj x) = Obj (select d i x)
    select d i (Dim d' choices v)
        | d == d' = select d i v
        | otherwise = Dim d' choices (select d i v)
    select d i (Chc d' vs)
        | d == d' = select d i (vs !! i)
        | otherwise = Chc d' (map (select d i) vs)

-- }}}

-- V Semantics implementation (psem) {{{
type Context = Map DimName (Int, ChcName) 
type Semantics a = [(Context, a)]

class HasSemantics a where -- needs FlexibleInstances for some reason
    psem' :: Context -> a -> Semantics a
    psem :: a -> Semantics a
    psem = psem' Map.empty

instance HasSemantics a => HasSemantics (V a) where
    psem' ctx (Obj x) = map (\(c, x) -> (c, Obj x)) $ psem' ctx x
    psem' ctx (Dim dim choices body) =
        let indexedChoices = [0..] `zip` choices
        in let updateCtx p = Map.insert dim p ctx -- insere { dim: (i, choice) } no contexto
        in let continue p = psem' (updateCtx p) body -- chama psem' para uma determinada escolha p
        in concatMap continue indexedChoices
    psem' ctx (Chc dim choices) =
        case Map.lookup dim ctx of
        Just (i, _c) -> psem' ctx (choices !! i) -- pega a i-ésima escolha
        Nothing -> concatMap (psem' ctx) choices -- unbound Chc

-- }}}

liftV :: (a -> b) -> V a -> V b
liftV = fmap

--- pretty printer for semantics {{{
prettifyContext :: Context -> [String]
prettifyContext = Map.elems . Map.mapWithKey convert
    where convert dim (_, chc) = dim ++ "." ++ chc

prettifySem' :: Show a => (Context, a) -> String
prettifySem' (ctx, obj) =
    let ctx' = prettifyContext ctx
    in show ctx' ++ " => " ++ show obj

prettifySem :: Show a => Semantics a -> String
prettifySem [] = ""
prettifySem (entry : []) = prettifySem' entry
prettifySem (entry : sem) = prettifySem' entry ++ "\n" ++ prettifySem sem

printsem :: (Show a, HasSemantics a) => V a -> IO ()
printsem = putStrLn . prettifySem . psem
-- }}}

-- Trivial instances {{{
instance Selectable String where
    select _ _ x = x
instance Selectable Char where
    select _ _ x = x
instance Selectable Integer where
    select _ _ x = x

instance HasSemantics String where
    psem' ctx s = [(ctx, s)]
instance HasSemantics Char where
    psem' ctx c = [(ctx, c)]
instance HasSemantics Integer where
    psem' ctx i = [(ctx, i)]
-- }}}

ex0 = Dim "A" ["a0", "a1"]
    $ Chc "A" [
        Dim "B" ["b0", "b1"]
        $ Chc "B" [Obj 1, Obj 2],

        Dim "C" ["c0", "c1"]
        $ Chc "C" [Obj 3, Obj 4]
    ]

chca = Chc "A" (Obj <$> [1, 2, 3])
ex2 = Dim "A" ["a0", "a1", "a2"]
    $ Dim "B" ["b0", "b1"]
    $ Chc "B" [
        fmap (+ 1) chca,
        fmap (* 10) chca
    ]

-- }}}

-- Variational List a {{{
type VList a = V (List a)
data List a
    = Empty
    | Cons a (List a)
    | Variation (VList a)
    deriving (Eq, Ord, Show, Read, Data, Typeable)

toHaskellList :: List a -> [a]
toHaskellList Empty = [] 
toHaskellList (Cons x xs) = x : (toHaskellList xs)

vlprintsem :: Show a => VList a -> IO ()
vlprintsem = putStrLn . prettifySem . map toHaskellListMap . psem
    where toHaskellListMap (ctx, (Obj x)) = (ctx, Obj (toHaskellList x))

infixr `cat`
cat :: List a -> List a -> List a
cat Empty ys = ys
cat (Cons x xs) ys = Cons x (cat xs ys)
cat (Variation v) ys = Variation $ fmap (`cat` ys) v

-- Functor, Applicative and Monad instances for List a {{{
instance Functor List where
    fmap _ Empty = Empty
    fmap f (Cons x xs) = Cons (f x) (fmap f xs)
    fmap f (Variation v) = Variation (fmap (fmap f) v) -- magic

instance Applicative List where
    pure x = Cons x Empty

    Empty <*> _ = Empty
    (Cons f fs) <*> ls = (f <$> ls) `cat` (fs <*> ls) 
    (Variation v) <*> ls = Variation $ fmap (<*> ls) v

instance Monad List where
    return = pure
    Empty >>= f = Empty
    (Cons x xs) >>= f =
        (f x) `cat` (xs >>= f)
    (Variation v) >>= f =
        Variation $ fmap (>>= f) v -- demorei um tempo pra chegar nisso! 
                                   -- ideia: v é uma "árvore de variações"
                                   -- `fmap g v` pega cada variação concreta e aplica g.
                                   -- a gente quer pegar cada variação (lista) concreta,
                                   -- aplicar f em cada elemento e dar um flatten
   
-- }}} 

-- Semigroup, Monoid instances for List na {{{
instance Semigroup (List a) where
    (<>) = cat
instance Monoid (List a) where
    mempty = Empty
-- }}}

list :: [a] -> List a
list = foldr Cons Empty

nth 1 (Cons x _) = Obj x
nth n (Cons _ xs) = nth (n-1) xs
nth n (Variation v) = nth n =<< v

fold _ x0 Empty = Obj x0
fold f x0 (Cons x xs) = (x `f`) <$> (fold f x0 xs)
fold f x0 (Variation v) = fold f x0 =<< v

-- len Empty = Obj 0
-- len (Cons _ xs) = (1 +) <$> (len xs)
-- len (Variation v) = v >>= len
len = fold (const (+1)) 0

zipL :: List a -> List b -> List (a, b)
zipL Empty _ = Empty
zipL _ Empty = Empty
zipL (Variation v) ys = Variation $ fmap (`zipL` ys) v
zipL xs (Variation v) = Variation $ fmap (xs `zipL`) v
zipL (Cons x xs) (Cons y ys) = Cons (x, y) (zipL xs ys)

instance Selectable a => Selectable (List a) where
    select d i Empty = Empty
    select d i (Cons x xs) = Cons (select d i x) (select d i xs)
    select d i (Variation v) = Variation $ select d i v

-- hard to write 
instance HasSemantics (List a) where
    psem' ctx Empty = [(ctx, Empty)]
    psem' ctx (Cons x xs) =
        let prependX (ctx, xs) = (ctx, Cons x xs)
        in prependX <$> psem' ctx xs
    psem' ctx (Variation v) =
        let sem = psem' ctx v
        in let unwrapper (ctx, (Obj x)) = (ctx, x) -- acho que ta certo
                                                   -- mas não lida bem com unbound Chcs
        in unwrapper <$> sem

v1 = Chc "Par" [Obj (list "x"), Obj (list "y")]
impl1 = Chc "Impl" [
            Obj $ (Variation v1) <> (list " + ") <> (Variation v1),
            Obj $ (list "2 * ") <> (Variation v1)
        ]
ex1 = Dim "Par" ["first", "second"]
    $ Dim "Impl" ["plus", "times"]
    $ Obj $ (list "twice ") <> (Variation v1) <> (list " = ") <> (Variation impl1)

ex3 = Dim "A" ["a0", "a1"]
    $ Obj $ Cons 1 (Variation $ Chc "A" [Obj $ list [2], Obj $ list [3]])
-- }}}

menu =
    Dim "Main" ["meat", "pasta"] $
    Chc "Main" [
        -- meat
        Obj (list ["Steak", "Fries"]),

        -- pasta
        Obj (list ["Pasta"] <> (Variation $
            Dim "Dessert" ["yes", "no"] $
            Chc "Dessert" [
                Obj (list ["Ice Cream"]), -- yes
                Obj (list [])  -- no
            ]
        ))
    ]

-- vlprintsem menu 
