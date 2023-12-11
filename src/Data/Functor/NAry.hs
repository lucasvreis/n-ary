{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Functor.NAry where

import Control.Applicative (liftA2)
import Data.Kind (Type)
import Data.PolyKinded (Proxy (..))
import Generics.Kind
import Generics.Kind.Examples ()

class KTraversable (t :: k) (as :: LoT k) (bs :: LoT k) where
  ktraverse :: (Applicative f) => Traversals f as bs -> (t :@@: as) -> f (t :@@: bs)

infixr 9 :#:

type Traversals :: forall k. (Type -> Type) -> LoT k -> LoT k -> Type
data Traversals f as bs where
  T0 :: Traversals f LoT0 LoT0
  (:#:) :: (a -> f b) -> Traversals f as bs -> Traversals f (a :&&: as) (b :&&: bs)

class GTraversable (t :: LoT k -> Type) (as :: LoT k) (bs :: LoT k) where
  gtraverse :: (Applicative f) => Traversals f as bs -> t as -> f (t bs)

instance GTraversable U1 as bs where
  gtraverse _ U1 = pure U1

instance (GTraversable f as bs) => GTraversable (M1 i c f) as bs where
  gtraverse f (M1 x) = M1 <$> gtraverse f x

instance
  ( GTraversable f as bs
  , GTraversable g as bs
  ) =>
  GTraversable (f :+: g) as bs
  where
  gtraverse f (L1 x) = L1 <$> gtraverse f x
  gtraverse f (R1 x) = R1 <$> gtraverse f x

instance
  ( GTraversable f as bs
  , GTraversable g as bs
  ) =>
  GTraversable (f :*: g) as bs
  where
  gtraverse f (x :*: y) = liftA2 (:*:) (gtraverse f x) (gtraverse f y)

class
  GTraversableArg
    (t :: Atom d Type)
    (as :: LoT d)
    (bs :: LoT d)
  where
  gtraversef ::
    (Applicative f) =>
    Proxy t ->
    Traversals f as bs ->
    Interpret t as ->
    f (Interpret t bs)

instance
  (GTraversableArg t as bs) =>
  GTraversable (Field t) as bs
  where
  gtraverse f (Field x) = Field <$> gtraversef (Proxy @t) f x

instance GTraversableArg (Kon t) as bs where
  gtraversef _ _ = pure

instance GTraversableArg (Var VZ) (a :&&: as) (b :&&: bs) where
  gtraversef _ (f :#: _) = f

instance
  (GTraversableArg (Var vr) as bs) =>
  GTraversableArg (Var (VS vr)) (a ':&&: as) (b ':&&: bs)
  where
  gtraversef _ (_ :#: rest) = gtraversef (Proxy @(Var vr)) rest

instance
  ( KTraversable f (Interpret x as :&&: LoT0) (Interpret x bs :&&: LoT0)
  , GTraversableArg x as bs
  ) =>
  GTraversableArg (f :$: x) as bs
  where
  gtraversef _ v =
    ktraverse
      ( gtraversef (Proxy @x) v
          :#: T0
      )

instance
  ( KTraversable
      f
      (Interpret x as :&&: Interpret y as :&&: LoT0)
      (Interpret x bs :&&: Interpret y bs :&&: LoT0)
  , GTraversableArg x as bs
  , GTraversableArg y as bs
  ) =>
  GTraversableArg (f :$: x :@: y) as bs
  where
  gtraversef _ v =
    ktraverse
      ( gtraversef (Proxy @x) v
          :#: gtraversef (Proxy @y) v
          :#: T0
      )

instance
  ( KTraversable
      f
      (Interpret x as :&&: Interpret y as :&&: Interpret z as :&&: LoT0)
      (Interpret x bs :&&: Interpret y bs :&&: Interpret z bs :&&: LoT0)
  , GTraversableArg x as bs
  , GTraversableArg y as bs
  , GTraversableArg z as bs
  ) =>
  GTraversableArg (f :$: x :@: y :@: z) as bs
  where
  gtraversef _ v =
    ktraverse
      ( gtraversef (Proxy @x) v
          :#: gtraversef (Proxy @y) v
          :#: gtraversef (Proxy @z) v
          :#: T0
      )

instance
  ( KTraversable
      f
      (Interpret x as :&&: Interpret y as :&&: Interpret z as :&&: Interpret w as :&&: LoT0)
      (Interpret x bs :&&: Interpret y bs :&&: Interpret z bs :&&: Interpret w bs :&&: LoT0)
  , GTraversableArg x as bs
  , GTraversableArg y as bs
  , GTraversableArg z as bs
  , GTraversableArg w as bs
  ) =>
  GTraversableArg (f :$: x :@: y :@: z :@: w) as bs
  where
  gtraversef _ v =
    ktraverse
      ( gtraversef (Proxy @x) v
          :#: gtraversef (Proxy @y) v
          :#: gtraversef (Proxy @z) v
          :#: gtraversef (Proxy @w) v
          :#: T0
      )

instance forall k (f :: k) as bs. (GenericK f, GTraversable (RepK f) as bs) => KTraversable f as bs where
  ktraverse ts x = toK @k @f <$> gtraverse ts (fromK @k @f x)
