{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.NAry.KFoldable (
  KList1 (..),
  ksequence_,
  RFold (..),
  RFolds,
  FoldMap (..),
  FoldMaps,
  KFoldable (..),
) where

import Data.Kind (Constraint, Type)
import Generics.Kind
import Data.NAry.Aux.KList (KList1 (..))

newtype RFold c a = RF (a -> c -> c)
type RFolds c k = KList1 (RFold c) k

newtype FoldMap m a = FM (a -> m)
type FoldMaps m k = KList1 (FoldMap m) k

type KFoldable :: forall {k}. k -> Constraint
class KFoldable (f :: k) where
  kfoldMap :: (Monoid m) => FoldMaps m k as -> f :@@: as -> m
  kfoldr :: RFolds c k as -> c -> f :@@: as -> c

  default kfoldMap :: (GenericK f, GFoldable (RepK f), Monoid m) => FoldMaps m k as -> f :@@: as -> m
  kfoldMap m = gfoldMap m . fromK @k @f

  default kfoldr :: (GenericK f, GFoldable (RepK f)) => RFolds c k as -> c -> f :@@: as -> c
  kfoldr m c0 = gfoldr m c0 . fromK @k @f

instance (Foldable f) => KFoldable f where
  kfoldMap (FM f :+ K1) = foldMap f
  kfoldr (RF f :+ K1) = foldr f

type KSeqr :: forall {k}. (Type -> Type) -> LoT k -> Constraint
class KSeqr f (as :: LoT k) where
  kseqr :: Applicative f => RFolds (f ()) k as

instance KSeqr f LoT0 where
  kseqr = K1

instance (KSeqr f as) => KSeqr f (f b :&&: as) where
  kseqr = RF (*>) :+ kseqr @f @as

ksequence_ ::
  forall t f as.
  ( KFoldable t
  , KSeqr f as
  , Applicative f
  ) =>
  t :@@: as ->
  f ()
ksequence_ = kfoldr @t (kseqr @_ @as) (pure ())

-- Generic code

type GFoldable :: forall {k}. (LoT k -> Type) -> Constraint
class GFoldable (f :: LoT k -> Type) where
  gfoldMap :: (Monoid m) => FoldMaps m k as -> f as -> m
  gfoldr :: RFolds c k as -> c -> f as -> c

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
  gfoldMapf :: (Monoid m) => FoldMaps m k as -> Interpret t as -> m
  gfoldrf :: RFolds c k as -> c -> Interpret t as -> c

instance GFoldableArg (Kon t) where
  gfoldMapf _ _ = mempty
  gfoldrf _ c _ = c

instance GFoldableArg (Var VZ) where
  gfoldMapf (FM f :+ _) = f
  gfoldrf (RF f :+ _) c x = x `f` c

instance (GFoldableArg (Var vr)) => GFoldableArg (Var (VS vr)) where
  gfoldMapf (_ :+ rest) = gfoldMapf @(Var vr) rest
  gfoldrf (_ :+ rest) = gfoldrf @(Var vr) rest

instance (KFoldable f, GFoldableArg x) => GFoldableArg (f :$: x) where
  gfoldMapf m = kfoldMap (FM (gfoldMapf @x m) :+ K1)
  gfoldrf m = kfoldr (RF (flip (gfoldrf @x m)) :+ K1)

instance (KFoldable f, GFoldableArg x, GFoldableArg y) => GFoldableArg (f :$: x :@: y) where
  gfoldMapf m = kfoldMap (FM (gfoldMapf @x m) :+ FM (gfoldMapf @y m) :+ K1)
  gfoldrf m = kfoldr (RF (flip (gfoldrf @x m)) :+ RF (flip (gfoldrf @y m)) :+ K1)

instance (KFoldable f, GFoldableArg x, GFoldableArg y, GFoldableArg z) => GFoldableArg (f :$: x :@: y :@: z) where
  gfoldMapf m = kfoldMap (FM (gfoldMapf @x m) :+ FM (gfoldMapf @y m) :+ FM (gfoldMapf @z m) :+ K1)
  gfoldrf m = kfoldr (RF (flip (gfoldrf @x m)) :+ RF (flip (gfoldrf @y m)) :+ RF (flip (gfoldrf @z m)) :+ K1)
