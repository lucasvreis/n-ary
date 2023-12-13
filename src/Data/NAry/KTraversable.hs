{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.NAry.KTraversable (
  ltraverse,
  Traversal (..),
  Traversals,
  KTraversable (..),
) where

import Control.Applicative (liftA2)
import Data.Bitraversable (Bitraversable (..))
import Data.Kind (Constraint, Type)
import Data.NAry.Labels
import Generics.Kind

ltraverse ::
  forall t ss ks a b f.
  (a ~ t :@@: Args0 (LMatches2 t ss ks)) =>
  (b ~ t :@@: Args1 (LMatches2 t ss ks)) =>
  (GetKList (Labels t) ss, KTraversable t) =>
  (Applicative f) =>
  LKList (Traversal f) ss ks ->
  a ->
  f b
ltraverse m = ktraverse @t (getKList @(Labels t) m)

newtype Traversal f a b = T (a -> f b)
type Traversals f k = KList (Traversal f) k

type KTraversable :: forall {k}. k -> Constraint
class KTraversable (t :: k) where
  ktraverse :: (Applicative f) => Traversals f k ks -> t :@@: Args0 ks -> f (t :@@: Args1 ks)
  default ktraverse :: (GenericK t, GTraversable (RepK t)) => (Applicative f) => Traversals f k ks -> t :@@: Args0 ks -> f (t :@@: Args1 ks)
  ktraverse f x = toK @k @t <$> gtraverse f (fromK @k @t x)

instance (Traversable f) => KTraversable f where
  ktraverse (T f :@ K0) = traverse f

instance (Bitraversable f) => KTraversable f where
  ktraverse (T f :@ T g :@ K0) = bitraverse f g

-- Generic code

type GTraversable :: forall {k}. (LoT k -> Type) -> Constraint
class GTraversable (t :: LoT k -> Type) where
  gtraverse :: (Applicative f) => Traversals f k ks -> t (Args0 ks) -> f (t (Args1 ks))

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
  gtraversef :: (Applicative f) => Traversals f k ks -> Interpret t (Args0 ks) -> f (Interpret t (Args1 ks))

instance GTraversableArg (Kon t) where
  gtraversef _ = pure

instance GTraversableArg (Var VZ) where
  gtraversef (T f :@ _) = f

instance (GTraversableArg (Var vr)) => GTraversableArg (Var (VS vr)) where
  gtraversef (_ :@ rest) = gtraversef @(Var vr) rest

instance (KTraversable f, GTraversableArg x) => GTraversableArg (f :$: x) where
  gtraversef m = ktraverse (T (gtraversef @x m) :@ K0)

instance (KTraversable f, GTraversableArg x, GTraversableArg y) => GTraversableArg (f :$: x :@: y) where
  gtraversef m = ktraverse (T (gtraversef @x m) :@ T (gtraversef @y m) :@ K0)

instance (KTraversable f, GTraversableArg x, GTraversableArg y, GTraversableArg z) => GTraversableArg (f :$: x :@: y :@: z) where
  gtraversef m = ktraverse (T (gtraversef @x m) :@ T (gtraversef @y m) :@ T (gtraversef @z m) :@ K0)
