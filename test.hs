{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, GADTs, LambdaCase, TypeApplications,
    ParallelListComp, ScopedTypeVariables, RankNTypes, PolyKinds, TypeInType, FlexibleContexts,
    RecordWildCards, ViewPatterns #-}
-- {-# LANGUAGE RebindableSyntax #-}

-- import Prelude hiding (return, (>>=), (*), (**), (.))

-- return :: a -> a
-- return = id

-- (>>=) :: r a -> (forall a. r a -> s) -> s
-- (>>=) x f = f x

-- (**) :: Sing1 f -> Sing1 g -> Sing1 (f `Cmp1` g)
-- (**) = Cmp1Cell

-- (.) :: f :--> g -> g :--> h -> f :--> h
-- (.) = Cmp2Cell

-- (*) :: (f :--> g) -> (f' :--> g') -> (Cmp1 f f' :--> Cmp1 g g')
-- (*) = Tensor2Cell

-- x :: ()
-- x = do
--         a <- mk0Cell "A"
--         b <- mk0Cell "B"
--         f <- mk1Cell "f" a b
--         g <- mk1Cell "g" a b
--         let alpha = mk2Cell "alpha" f g
--             beta = mk2Cell "beta" g g
--             gamma = alpha . beta
--         return ()



main :: IO ()
main = putStrLn "done"

data K a b = K a


data ZeroCell = ZeroCell

data Sing0 (a :: ZeroCell) = Sing0 String

mk0Cell :: String -> Sing0 a
mk0Cell s = Sing0 s

data A0Cell where
    A0Cell :: Sing0 a -> A0Cell

new0 :: String -> A0Cell
new0 s = A0Cell $ mk0Cell s


data (a::ZeroCell) :-> (b::ZeroCell) where
    Id1 :: a :-> a
    Cmp1 :: a :-> b -> b :-> c -> a :-> c

data Sing1 (f :: a :-> b) where
    Mk1Cell :: String -> Sing0 a -> Sing0 b -> Sing1 (f :: a :-> b)
    Cmp1Cell :: Sing1 f -> Sing1 g -> Sing1 (f `Cmp1` g)

mk1Cell :: String -> Sing0 a -> Sing0 b -> Sing1 (f :: a :-> b)
mk1Cell = Mk1Cell

data A1Cell a b where
    A1Cell :: Sing1 (f :: a :-> b) -> A1Cell a b

new1 :: String -> Sing0 a -> Sing0 b -> A1Cell a b
new1 s sa sb = A1Cell $ mk1Cell s sa sb

x :: Maybe ()
x = do
        A0Cell a <- return $ new0 "A"
        A0Cell b <- return $ new0 "B"
        A1Cell f <- return $ new1 "f" a b
        A1Cell g <- return $ new1 "g" b b
        let h = f `Cmp1Cell` g
        Nothing

data (f :: a :-> b) :--> (g :: a :-> b) where
    Mk2Cell :: String -> Sing1 f -> Sing1 g -> f :--> g
    Cmp2Cell :: f :--> g -> g :--> h -> f :--> h
    Tensor2Cell :: (f :--> g) -> (f' :--> g') -> (Cmp1 f f' :--> Cmp1 g g')

mk2Cell :: String -> Sing1 f -> Sing1 g -> f :--> g
mk2Cell = Mk2Cell
