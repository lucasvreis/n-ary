{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Category.Bifunctor where

import Control.Arrow (Arrow (arr, (***)), ArrowChoice (..))
import Control.Category (Category (..))
import Data.Bifunctor qualified as B
import Data.Kind (Constraint, Type)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

type EndoBifunctor :: forall {k}. (k -> k -> Type) -> (k -> k -> k) -> Constraint
class EndoBifunctor r p where
  bimap :: a `r` b -> c `r` d -> (a `p` c) `r` (b `p` d)

instance {-# OVERLAPPING #-} (B.Bifunctor f) => EndoBifunctor (->) f where
  bimap = B.bimap

instance (Arrow a) => EndoBifunctor a (,) where
  bimap = (***)

instance (ArrowChoice a) => EndoBifunctor a Either where
  bimap = (+++)

class (EndoBifunctor r p) => Associative r p where
  associate :: ((a `p` b) `p` c) `r` (a `p` (b `p` c))
  disassociate :: (a `p` (b `p` c)) `r` ((a `p` b) `p` c)

instance (Arrow a) => Associative a (,) where
  associate = arr $ \((x, y), z) -> (x, (y, z))
  disassociate = arr $ \(x, (y, z)) -> ((x, y), z)

instance (ArrowChoice a) => Associative a Either where
  associate = arr $ \case
    Right x -> Right (Right x)
    Left (Right x) -> Right (Left x)
    Left (Left x) -> Left x
  disassociate = arr $ \case
    Right (Right x) -> Right x
    Right (Left x) -> Left (Right x)
    Left x -> Left (Left x)

class (Associative r p) => Monoidal (r :: k -> k -> Type) (p :: k -> k -> k) where
  type Id r p :: k
  idl :: (Id r p `p` a) `r` a
  idr :: (a `p` Id r p) `r` a
  coidl :: a `r` (Id r p `p` a)
  coidr :: a `r` (a `p` Id r p)

instance (Arrow a) => Monoidal a (,) where
  type Id a (,) = ()
  idl = arr Prelude.snd
  idr = arr Prelude.fst
  coidl = arr ((),)
  coidr = arr (,())

instance (ArrowChoice a) => Monoidal a Either where
  type Id a Either = Void
  idl = arr absurd ||| id
  idr = id ||| arr absurd
  coidl = arr Right
  coidr = arr Left

-- class (Category r, Monoidal r (Product r)) => Cartesian (r :: k -> k -> Type) where
type Cartesian :: forall {k}. (k -> k -> Type) -> Constraint
class (Category r, EndoBifunctor r (Product r)) => Cartesian (r :: k -> k -> Type) where
  type Product r :: k -> k -> k
  fst :: Product r a b `r` a
  snd :: Product r a b `r` b
  diag :: a `r` Product r a a
  (&&&) :: (a `r` b) -> (a `r` c) -> a `r` Product r b c

  diag = id &&& id
  f &&& g = bimap f g . diag
