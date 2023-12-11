{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.NAry.KFoldable (
  RFolds (..),
  FoldMaps (..),
  KFoldable (..),
  ksequence_,
) where

import Data.Bifoldable (Bifoldable (..))
import Data.Kind (Constraint, Type)
import Generics.Kind
import Type.Errors

infixr 9 :>

type RFolds :: forall k. Type -> LoT k -> Type
data RFolds c as where
  F0 :: RFolds c LoT0
  (:>) ::
    (a -> c -> c) ->
    RFolds c as ->
    RFolds c (a :&&: as)

infixr 9 :<>

type FoldMaps :: forall k. Type -> LoT k -> Type
data FoldMaps m as where
  FM0 :: FoldMaps m LoT0
  (:<>) ::
    (a -> m) ->
    FoldMaps m as ->
    FoldMaps m (a :&&: as)

type KFoldable :: forall {k}. k -> Constraint
class KFoldable (f :: k) where
  kfoldMap :: (Monoid m) => FoldMaps m as -> f :@@: as -> m
  kfoldr :: RFolds c as -> c -> f :@@: as -> c

  default kfoldMap :: (GenericK f, GFoldable (RepK f), Monoid m) => FoldMaps m as -> f :@@: as -> m
  kfoldMap m = gfoldMap m . fromK @k @f

  default kfoldr :: (GenericK f, GFoldable (RepK f)) => RFolds c as -> c -> f :@@: as -> c
  kfoldr m c0 = gfoldr m c0 . fromK @k @f

instance (Foldable f) => KFoldable f where
  kfoldMap (f :<> FM0) = foldMap f
  kfoldr (f :> F0) = foldr f

instance (Bifoldable f) => KFoldable f where
  kfoldMap (f :<> g :<> FM0) = bifoldMap f g
  kfoldr (f :> g :> F0) = bifoldr f g

type KSeqr :: forall {k}. LoT k -> (Type -> Type) -> Constraint
class KSeqr as f where
  kseqr :: (Applicative f) => RFolds (f ()) as

instance KSeqr LoT0 f where
  kseqr = F0

instance forall (a :: Type) as f b. (a ~ f b, KSeqr as f) => KSeqr (a :&&: as) f where
  kseqr = (*>) :> kseqr @as @f

type StripF' :: forall k1 k2. k1 -> k2 -> LoT k2 -> LoT k1
type family StripF' (f :: k) a l :: LoT k where
  StripF' f f l = l
  StripF' f (g x) l = StripF' f g (x :&&: l)
  StripF' a b c = TypeError (Text "Mismatch!!! " :<>: ShowTypeQuoted a :<>: Text " " :<>: ShowTypeQuoted b :<>: Text " " :<>: ShowTypeQuoted c)

type StripF f a = StripF' f a LoT0

ksequence_ :: forall t f a. (a ~ t :@@: StripF t a, KFoldable t, KSeqr (StripF t a) f, Applicative f) => a -> f ()
ksequence_ = kfoldr @t (kseqr @(StripF t a)) (pure ())

test = ksequence_ @((,) (Maybe Int)) (Nothing, Just 3)

-- >>> test
-- Just ()

-- Generic code

type GFoldable :: forall {k}. (LoT k -> Type) -> Constraint
class GFoldable (f :: LoT k -> Type) where
  gfoldMap :: (Monoid m) => FoldMaps m as -> f as -> m
  gfoldr :: RFolds c as -> c -> f as -> c

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

type GFoldableArg :: forall {d}. Atom d Type -> Constraint
class GFoldableArg (t :: Atom d Type) where
  gfoldMapf :: (Monoid m) => FoldMaps m as -> Interpret t as -> m
  gfoldrf :: RFolds c as -> c -> Interpret t as -> c

instance GFoldableArg (Kon t) where
  gfoldMapf _ _ = mempty
  gfoldrf _ c _ = c

instance GFoldableArg (Var VZ) where
  gfoldMapf (f :<> _) = f
  gfoldrf (f :> _) c x = x `f` c

instance (GFoldableArg (Var vr)) => GFoldableArg (Var (VS vr)) where
  gfoldMapf (_ :<> rest) = gfoldMapf @(Var vr) rest
  gfoldrf (_ :> rest) = gfoldrf @(Var vr) rest

instance (KFoldable f, GFoldableArg x) => GFoldableArg (f :$: x) where
  gfoldMapf m = kfoldMap (gfoldMapf @x m :<> FM0)
  gfoldrf m = kfoldr (flip (gfoldrf @x m) :> F0)

instance (KFoldable f, GFoldableArg x, GFoldableArg y) => GFoldableArg (f :$: x :@: y) where
  gfoldMapf m = kfoldMap (gfoldMapf @x m :<> gfoldMapf @y m :<> FM0)
  gfoldrf m = kfoldr (flip (gfoldrf @x m) :> flip (gfoldrf @y m) :> F0)

instance (KFoldable f, GFoldableArg x, GFoldableArg y, GFoldableArg z) => GFoldableArg (f :$: x :@: y :@: z) where
  gfoldMapf m = kfoldMap (gfoldMapf @x m :<> gfoldMapf @y m :<> gfoldMapf @z m :<> FM0)
  gfoldrf m = kfoldr (flip (gfoldrf @x m) :> flip (gfoldrf @y m) :> flip (gfoldrf @z m) :> F0)
