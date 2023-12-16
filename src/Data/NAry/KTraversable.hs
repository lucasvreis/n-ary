{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.NAry.KTraversable (
  KList2 (..),
  Traversal (..),
  Traversals,
  KTraversable (..),
) where

import Control.Applicative (liftA2)
import Data.Kind (Constraint, Type)
import Generics.Kind
import Data.NAry.Aux.KList (KList2 (..))

newtype Traversal f a b = T (a -> f b)
type Traversals f k = KList2 (Traversal f) k

type KTraversable :: forall {k}. k -> Constraint
class KTraversable (t :: k) where
  ktraverse :: (Applicative f) => Traversals f k as bs -> t :@@: as -> f (t :@@: bs)
  default ktraverse :: (GenericK t, GTraversable (RepK t)) => (Applicative f) => Traversals f k as bs -> t :@@: as -> f (t :@@: bs)
  ktraverse f x = toK @k @t <$> gtraverse f (fromK @k @t x)

instance (Traversable f) => KTraversable f where
  ktraverse (T f :@ K2) = traverse f

-- Generic code

type GTraversable :: forall {k}. (LoT k -> Type) -> Constraint
class GTraversable (t :: LoT k -> Type) where
  gtraverse :: (Applicative f) => Traversals f k as bs -> t as -> f (t bs)

instance GTraversable U1 where
  gtraverse _ U1 = pure U1

instance (GTraversable f) => GTraversable (M1 i c f) where
  gtraverse f (M1 x) = M1 <$> gtraverse f x

instance
  ( GTraversable f
  , GTraversable g
  ) =>
  GTraversable (f :+: g)
  where
  gtraverse f (L1 x) = L1 <$> gtraverse f x
  gtraverse f (R1 x) = R1 <$> gtraverse f x

instance
  ( GTraversable f
  , GTraversable g
  ) =>
  GTraversable (f :*: g)
  where
  gtraverse f (x :*: y) = liftA2 (:*:) (gtraverse f x) (gtraverse f y)

instance (GTraversableArg t) => GTraversable (Field t) where
  gtraverse f (Field x) = Field <$> gtraversef @t f x

type GTraversableArg :: forall {k}. Atom k Type -> Constraint
class GTraversableArg (t :: Atom k Type) where
  gtraversef :: (Applicative f) => Traversals f k as bs -> Interpret t as -> f (Interpret t bs)

instance GTraversableArg (Kon t) where
  gtraversef _ = pure

instance GTraversableArg (Var VZ) where
  gtraversef (T f :@ _) = f

instance (GTraversableArg (Var vr)) => GTraversableArg (Var (VS vr)) where
  gtraversef (_ :@ rest) = gtraversef @(Var vr) rest

instance (KTraversable f, GTraversableArg x) => GTraversableArg (f :$: x) where
  gtraversef m = ktraverse (T (gtraversef @x m) :@ K2)

instance (KTraversable f, GTraversableArg x, GTraversableArg y) => GTraversableArg (f :$: x :@: y) where
  gtraversef m = ktraverse (T (gtraversef @x m) :@ T (gtraversef @y m) :@ K2)

instance (KTraversable f, GTraversableArg x, GTraversableArg y, GTraversableArg z) => GTraversableArg (f :$: x :@: y :@: z) where
  gtraversef m = ktraverse (T (gtraversef @x m) :@ T (gtraversef @y m) :@ T (gtraversef @z m) :@ K2)
