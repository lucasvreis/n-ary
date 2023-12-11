{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.NAry.KFunctor (
  Mappings (..),
  KFunctor (..),
) where

import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Constraint, Type)
import Generics.Kind

infixr 9 :#

type Mappings :: forall k. LoT k -> LoT k -> Type
data Mappings as bs where
  M0 :: Mappings LoT0 LoT0
  (:#) ::
    (a -> b) ->
    Mappings as bs ->
    Mappings (a :&&: as) (b :&&: bs)

type KFunctor :: forall {k}. k -> Constraint
class KFunctor (f :: k) where
  kfmap :: Mappings as bs -> f :@@: as -> f :@@: bs
  default kfmap :: (GenericK f, GFunctor (RepK f)) => Mappings as bs -> f :@@: as -> f :@@: bs
  kfmap m = toK @k @f . gfmap m . fromK @k @f

instance (Functor f) => KFunctor f where
  kfmap (f :# M0) = fmap f

instance (Bifunctor f) => KFunctor f where
  kfmap (f :# g :# M0) = bimap f g

type GFunctor :: forall {k}. (LoT k -> Type) -> Constraint
class GFunctor (f :: LoT k -> Type) where
  gfmap :: Mappings as bs -> f as -> f bs

instance GFunctor U1 where
  gfmap _ U1 = U1

instance (GFunctor f) => GFunctor (M1 i c f) where
  gfmap f (M1 x) = M1 (gfmap f x)

instance
  ( GFunctor f
  , GFunctor g
  ) =>
  GFunctor (f :+: g)
  where
  gfmap f (L1 x) = L1 (gfmap f x)
  gfmap f (R1 x) = R1 (gfmap f x)

instance
  ( GFunctor f
  , GFunctor g
  ) =>
  GFunctor (f :*: g)
  where
  gfmap f (x :*: y) = (:*:) (gfmap f x) (gfmap f y)

instance (GFunctorArg t) => GFunctor (Field t) where
  gfmap f (Field x) = Field (gfmapf @t f x)

type GFunctorArg :: forall {d}. Atom d Type -> Constraint
class GFunctorArg (t :: Atom d Type) where
  gfmapf :: Mappings as bs -> Interpret t as -> Interpret t bs

instance GFunctorArg (Kon t) where
  gfmapf _ = id

instance GFunctorArg (Var VZ) where
  gfmapf (f :# _) = f

instance (GFunctorArg (Var vr)) => GFunctorArg (Var (VS vr)) where
  gfmapf (_ :# rest) = gfmapf @(Var vr) rest

instance (KFunctor f, GFunctorArg x) => GFunctorArg (f :$: x) where
  gfmapf m = kfmap (gfmapf @x m :# M0)

instance (KFunctor f, GFunctorArg x, GFunctorArg y) => GFunctorArg (f :$: x :@: y) where
  gfmapf m = kfmap @f (gfmapf @x m :# gfmapf @y m :# M0)

instance (KFunctor f, GFunctorArg x, GFunctorArg y, GFunctorArg z) => GFunctorArg (f :$: x :@: y :@: z) where
  gfmapf m = kfmap @f (gfmapf @x m :# gfmapf @y m :# gfmapf @z m :# M0)
