{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.NAry.KFoldable (
  lfoldr,
  lfoldMap,
  ksequence_,
  RFold (..),
  RFolds,
  FoldMap (..),
  FoldMaps,
  KFoldable (..),
) where

import Data.Bifoldable (Bifoldable (..))
import Data.Kind (Constraint, Type)
import Data.NAry.Labels
import Generics.Kind

lfoldr ::
  forall t ss ks a c.
  (a ~ t :@@: Args0 (LMatches1 t ss ks)) =>
  (GetKList (Labels t) ss, KFoldable t) =>
  LKList (RFold c) ss ks ->
  c ->
  a ->
  c
lfoldr m = kfoldr @t (getKList @(Labels t) m)

lfoldMap ::
  forall t ss ks a m.
  (a ~ t :@@: Args0 (LMatches1 t ss ks)) =>
  (GetKList (Labels t) ss, KFoldable t) =>
  Monoid m =>
  LKList (FoldMap m) ss ks ->
  a ->
  m
lfoldMap m = kfoldMap @t (getKList @(Labels t) m)

newtype RFold c a = RF (a -> c -> c)
type RFolds c k = KList (RFold c) k

newtype FoldMap m a = FM (a -> m)
type FoldMaps m k = KList (FoldMap m) k

type KFoldable :: forall {k}. k -> Constraint
class KFoldable (f :: k) where
  kfoldMap :: (Monoid m) => FoldMaps m k ks -> f :@@: Args0 ks -> m
  kfoldr :: RFolds c k ks -> c -> f :@@: Args0 ks -> c

  default kfoldMap :: (GenericK f, GFoldable (RepK f), Monoid m) => FoldMaps m k ks -> f :@@: Args0 ks -> m
  kfoldMap m = gfoldMap m . fromK @k @f

  default kfoldr :: (GenericK f, GFoldable (RepK f)) => RFolds c k ks -> c -> f :@@: Args0 ks -> c
  kfoldr m c0 = gfoldr m c0 . fromK @k @f

instance (Foldable f) => KFoldable f where
  kfoldMap (FM f :@ K0) = foldMap f
  kfoldr (RF f :@ K0) = foldr f

instance (Bifoldable f) => KFoldable f where
  kfoldMap (FM f :@ FM g :@ K0) = bifoldMap f g
  kfoldr (RF f :@ RF g :@ K0) = bifoldr f g

type ToLoArgs1 :: forall k. LoT k -> LoT (LoArgs (Type -> Type) k)
type family ToLoArgs1 as where
  ToLoArgs1 LoT0 = LoT0
  ToLoArgs1 (a :&&: as) = (a :&&: LoT0) :&&: ToLoArgs1 as

type KSeqr :: forall {k}. LoT k -> (Type -> Type) -> Constraint
class KSeqr (as :: LoT k) f where
  kseqr :: (Applicative f) => RFolds (f ()) k (ToLoArgs1 as)

instance KSeqr LoT0 f where
  kseqr = K0

instance forall (a :: Type) as f b. (a ~ f b, KSeqr as f) => KSeqr (a :&&: as) f where
  kseqr = RF (*>) :@ kseqr @as @f

ksequence_ ::
  forall t f a.
  ( a ~ t :@@: Args0 (ToLoArgs1 (StripF t a))
  , KFoldable t
  , KSeqr (StripF t a) f
  , Applicative f
  ) =>
  a ->
  f ()
ksequence_ = kfoldr @t (kseqr @(StripF t a)) (pure ())

-- Generic code

type GFoldable :: forall {k}. (LoT k -> Type) -> Constraint
class GFoldable (f :: LoT k -> Type) where
  gfoldMap :: (Monoid m) => FoldMaps m k ks -> f (Args0 ks) -> m
  gfoldr :: RFolds c k ks -> c -> f (Args0 ks) -> c

instance GFoldable U1 where
  gfoldMap _ U1 = mempty
  gfoldr _ c U1 = c

instance (GFoldable f) => GFoldable (M1 i c f) where
  gfoldMap f (M1 x) = gfoldMap f x
  gfoldr f c (M1 x) = gfoldr f c x

instance
  ( GFoldable f
  , GFoldable g
  ) =>
  GFoldable (f :+: g)
  where
  gfoldMap f (L1 x) = gfoldMap f x
  gfoldMap f (R1 x) = gfoldMap f x
  gfoldr f c (L1 x) = gfoldr f c x
  gfoldr f c (R1 x) = gfoldr f c x

instance
  ( GFoldable f
  , GFoldable g
  ) =>
  GFoldable (f :*: g)
  where
  gfoldMap f (x :*: y) = gfoldMap f x <> gfoldMap f y
  gfoldr f c (x :*: y) = gfoldr f (gfoldr f c y) x

instance (GFoldableArg t) => GFoldable (Field t) where
  gfoldMap f (Field x) = gfoldMapf @t f x
  gfoldr f c (Field x) = gfoldrf @t f c x

type GFoldableArg :: forall {k}. Atom k Type -> Constraint
class GFoldableArg (t :: Atom k Type) where
  gfoldMapf :: (Monoid m) => FoldMaps m k ks -> Interpret t (Args0 ks) -> m
  gfoldrf :: RFolds c k ks -> c -> Interpret t (Args0 ks) -> c

instance GFoldableArg (Kon t) where
  gfoldMapf _ _ = mempty
  gfoldrf _ c _ = c

instance GFoldableArg (Var VZ) where
  gfoldMapf (FM f :@ _) = f
  gfoldrf (RF f :@ _) c x = x `f` c

instance (GFoldableArg (Var vr)) => GFoldableArg (Var (VS vr)) where
  gfoldMapf (_ :@ rest) = gfoldMapf @(Var vr) rest
  gfoldrf (_ :@ rest) = gfoldrf @(Var vr) rest

instance (KFoldable f, GFoldableArg x) => GFoldableArg (f :$: x) where
  gfoldMapf m = kfoldMap (FM (gfoldMapf @x m) :@ K0)
  gfoldrf m = kfoldr (RF (flip (gfoldrf @x m)) :@ K0)

instance (KFoldable f, GFoldableArg x, GFoldableArg y) => GFoldableArg (f :$: x :@: y) where
  gfoldMapf m = kfoldMap (FM (gfoldMapf @x m) :@ FM (gfoldMapf @y m) :@ K0)
  gfoldrf m = kfoldr (RF (flip (gfoldrf @x m)) :@ RF (flip (gfoldrf @y m)) :@ K0)

instance (KFoldable f, GFoldableArg x, GFoldableArg y, GFoldableArg z) => GFoldableArg (f :$: x :@: y :@: z) where
  gfoldMapf m = kfoldMap (FM (gfoldMapf @x m) :@ FM (gfoldMapf @y m) :@ FM (gfoldMapf @z m) :@ K0)
  gfoldrf m = kfoldr (RF (flip (gfoldrf @x m)) :@ RF (flip (gfoldrf @y m)) :@ RF (flip (gfoldrf @z m)) :@ K0)
