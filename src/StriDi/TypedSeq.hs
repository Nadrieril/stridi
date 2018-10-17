{-# LANGUAGE GADTs, TypeApplications, ScopedTypeVariables, RankNTypes, PolyKinds #-}
module StriDi.TypedSeq where


data Composite f a b where
    NilCte :: Composite f a a
    CmpCte :: f a b -> Composite f b c -> Composite f a c

headComposite :: Composite f a b -> (forall c. f a c -> r a) -> r a -> r a
headComposite NilCte _ x = x
headComposite (CmpCte fab _) f _ = f fab

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

flatMapComposite :: (forall a b. f a b -> Composite g a b) -> Composite f a b -> Composite g a b
flatMapComposite f NilCte = NilCte
flatMapComposite f (CmpCte fab q) = mergeComposite (f fab) $ flatMapComposite f q


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
iterInterleaved (CmpIntl ga fab q) f = f (ga, fab, headInterleaved q) : iterInterleaved q f

mergeInterleaved :: Interleaved f g a b -> Interleaved f g b c -> Interleaved f g a c
mergeInterleaved (NilIntl _) fbc = fbc
mergeInterleaved (CmpIntl ga fab q) fbc = CmpIntl ga fab $ mergeInterleaved q fbc

mapInterleaved :: (forall a b. f a b -> f' a b) -> Interleaved f g a b -> Interleaved f' g a b
mapInterleaved f (NilIntl ga) = NilIntl ga
mapInterleaved f (CmpIntl ga fab q) = CmpIntl ga (f fab) $ mapInterleaved f q

mapAccumInterleaved :: (forall a b. acc a -> f a b -> (acc b, f' a b)) -> (forall a. acc a -> g a -> g' a) -> acc a -> Interleaved f g a b -> (acc b, Interleaved f' g' a b)
mapAccumInterleaved mapf mapg acc (NilIntl ga) = (acc, NilIntl $ mapg acc ga)
mapAccumInterleaved mapf mapg acc (CmpIntl ga fab q) =
    let ga' = mapg acc ga
        (acc', fab') = mapf acc fab
     in CmpIntl ga' fab' <$> mapAccumInterleaved mapf mapg acc' q

flatMapInterleaved :: (forall a b. f a b -> g a -> g b -> Interleaved f' g a b) -> Interleaved f g a b -> Interleaved f' g a b
flatMapInterleaved f (NilIntl ga) = NilIntl ga
flatMapInterleaved f (CmpIntl ga fab q) = mergeInterleaved (f fab ga (headInterleaved q)) $ flatMapInterleaved f q

interleaveInComposite :: (forall a b c. f a b -> g b -> g a) -> g b -> Composite f a b -> Interleaved f g a b
interleaveInComposite f x = foldComposite (\fab intbc -> CmpIntl (f fab (headInterleaved intbc)) fab intbc) (NilIntl x)

compositeFromInterleaved :: Interleaved f g a b -> Composite f a b
compositeFromInterleaved (NilIntl _) = NilCte
compositeFromInterleaved (CmpIntl _ fab q) = CmpCte fab $ compositeFromInterleaved q
