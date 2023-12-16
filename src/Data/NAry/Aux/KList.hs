{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.NAry.Aux.KList where

import Data.Kind (Type, Constraint)
import Data.PolyKinded (LoT (..))
import Prelude hiding (id, (.))

-- * n-ary products

type HList :: forall (k :: Type) (l :: Type). k -> l -> Type
data HList k l where
  H0 :: HList k Type
  (:*) :: k -> HList k l -> HList k (Type -> l)

type All :: forall k l. (k -> Constraint) -> HList k l -> Constraint
type family All c fs where
  All c H0 = ()
  All c (x :* xs) = (c x, All c xs)

infixr 9 :+

type KList1 :: (Type -> Type) -> forall l -> LoT l -> Type
data KList1 f k as where
  K1 :: KList1 f Type as
  (:+) :: f a -> KList1 f k as -> KList1 f (Type -> k) (a :&&: as)

deriving instance (Show (KList1 f Type LoT0))
deriving instance (Show (KList1 f k as), Show (f a)) => (Show (KList1 f (Type -> k) (a :&&: as)))

infixr 9 :@

type KList2 :: (Type -> Type -> Type) -> forall l -> LoT l -> LoT l -> Type
data KList2 f k (as :: LoT k) (bs :: LoT k) where
  K2 :: KList2 f Type as bs
  (:@) :: f a b -> KList2 f k as bs -> KList2 f (Type -> k) (a :&&: as) (b :&&: bs)
