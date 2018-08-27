{-# LANGUAGE GADTs, TypeApplications, ScopedTypeVariables, RankNTypes, PolyKinds #-}
module Stridi.TypedSeq where


data Composite f a b where
    NilCte :: Composite f a a
    CmpCte :: f a b -> Composite f b c -> Composite f a c

lastComposite :: Composite f a b -> (forall c. f c b -> r b) -> r b -> r b
lastComposite NilCte _ x = x
lastComposite (CmpCte fab NilCte) f _ = f fab
lastComposite (CmpCte _ q) f x = lastComposite q f x

foldComposite :: (forall a b c. f a b -> r b c -> r a c) -> r b b -> Composite f a b -> r a b
foldComposite _ x NilCte = x
foldComposite f x (CmpCte fab q) = f fab (foldComposite f x q)

mergeComposite :: Composite f a b -> Composite f b c -> Composite f a c
mergeComposite NilCte fbc = fbc
mergeComposite (CmpCte fab q) fbc = CmpCte fab $ mergeComposite q fbc

singComposite :: f a b -> Composite f a b
singComposite fab = CmpCte fab NilCte


data Interleaved f g a b where
    NilIntl :: g a -> Interleaved f g a a
    CmpIntl :: g a -> f a b -> Interleaved f g b c -> Interleaved f g a c

headInterleaved :: Interleaved f g a b -> g a
headInterleaved (NilIntl ga) = ga
headInterleaved (CmpIntl ga _ _) = ga

lastInterleaved :: Interleaved f g a b -> g b
lastInterleaved (NilIntl ga) = ga
lastInterleaved (CmpIntl _ _ q) = lastInterleaved q

iterInterleaved :: Interleaved f g a b -> (forall a b. (g a, f a b, g b) -> r) -> [r]
iterInterleaved (NilIntl ga) f = []
iterInterleaved (CmpIntl ga fab (NilIntl gb)) f = [f (ga, fab, gb)]
iterInterleaved (CmpIntl ga fab q@(CmpIntl gb _ _)) f = f (ga, fab, gb) : iterInterleaved q f

interleaveInComposite :: (forall a b c. f a b -> g b -> g a) -> g b -> Composite f a b -> Interleaved f g a b
interleaveInComposite f x = foldComposite (\fab intbc -> CmpIntl (f fab (headInterleaved intbc)) fab intbc) (NilIntl x)
