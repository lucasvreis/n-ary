{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.NAry.KFunctor (
  lfmap,
  Mappings,
  KFunctor (..),
) where

import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Constraint, Type)
import Data.NAry.Labels
import Generics.Kind

lfmap ::
  forall f ss ks a b.
  (a ~ f :@@: Args0 (LMatches2 f ss ks)) =>
  (b ~ f :@@: Args1 (LMatches2 f ss ks)) =>
  (GetKList (Labels f) ss) =>
  (KFunctor f) =>
  LKList (->) ss ks ->
  a ->
  b
lfmap m = kfmap @f (getKList @(Labels f) m)

type Mappings k = KList (->) k

type KFunctor :: forall {k}. k -> Constraint
class KFunctor (f :: k) where
  kfmap :: Mappings k ks -> f :@@: Args0 ks -> f :@@: Args1 ks
  default kfmap :: (GenericK f, GFunctor (RepK f)) => Mappings k ks -> f :@@: Args0 ks -> f :@@: Args1 ks
  kfmap m = toK @k @f . gfmap m . fromK @k @f

instance (Functor f) => KFunctor f where
  kfmap (f :@ K0) = fmap f

instance (Bifunctor f) => KFunctor f where
  kfmap (f :@ g :@ K0) = bimap f g

type GFunctor :: forall {k}. (LoT k -> Type) -> Constraint
class GFunctor (f :: LoT k -> Type) where
  gfmap :: Mappings k ks -> f (Args0 ks) -> f (Args1 ks)

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

type GFunctorArg :: forall {k}. Atom k Type -> Constraint
class GFunctorArg (t :: Atom k Type) where
  gfmapf :: Mappings k ks -> Interpret t (Args0 ks) -> Interpret t (Args1 ks)

instance GFunctorArg (Kon t) where
  gfmapf _ = id

instance GFunctorArg (Var VZ) where
  gfmapf (f :@ _) = f

instance (GFunctorArg (Var vr)) => GFunctorArg (Var (VS vr)) where
  gfmapf (_ :@ rest) = gfmapf @(Var vr) rest

instance (KFunctor f, GFunctorArg x) => GFunctorArg (f :$: x) where
  gfmapf m = kfmap @f (gfmapf @x m :@ K0)

instance (KFunctor f, GFunctorArg x, GFunctorArg y) => GFunctorArg (f :$: x :@: y) where
  gfmapf m = kfmap @f (gfmapf @x m :@ gfmapf @y m :@ K0)

instance (KFunctor f, GFunctorArg x, GFunctorArg y, GFunctorArg z) => GFunctorArg (f :$: x :@: y :@: z) where
  gfmapf m = kfmap @f (gfmapf @x m :@ gfmapf @y m :@ gfmapf @z m :@ K0)
