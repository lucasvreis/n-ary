{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.NAry.Labels (
  StripF,
  Args0,
  Args1,
  LoArgs,
  KList (..),
  LList (..),
  LKList (..),
  Labels,
  Match,
  LMatches1,
  LMatches2,
  GetKList (..),
) where

import Data.Kind (Constraint, Type)
import Data.PolyKinded (HeadLoT, TailLoT)
import Generics.Kind
import Type.Errors
import Unsafe.Coerce (unsafeCoerce)

type StripF' :: forall k1 k2. k1 -> k2 -> LoT k2 -> LoT k1
type family StripF' (f :: k) a l :: LoT k where
  StripF' f f l = l
  StripF' f (g x) l = StripF' f g (x :&&: l)
  StripF' a b c = TypeError (ShowTypeQuoted a :<>: Text " does not match base type " :<>: ShowTypeQuoted b :<>: Text ".")

-- | Returns a list of type arguments for the k-ary type @f@ as they occur in the type @a@.
type StripF f a = StripF' f a LoT0

type Args0 :: LoT l -> LoT k
type family Args0 ks where
  Args0 LoT0 = LoT0
  Args0 ks = HeadLoT (HeadLoT ks) :&&: Args0 (TailLoT ks)

type Args1 :: LoT l -> LoT k
type family Args1 ks where
  Args1 LoT0 = LoT0
  Args1 ks = HeadLoT (TailLoT (HeadLoT ks)) :&&: Args1 (TailLoT ks)

type family LoArgs k l = r | r -> l where
  LoArgs k Type = Type
  LoArgs k (Type -> l) = LoT k -> LoArgs k l

infixr 9 :@

type KList :: forall k. k -> forall l -> LoT (LoArgs k l) -> Type
data KList a k ks where
  K0 :: KList a Type LoT0
  (:@) :: (b ~ a :@@: StripF a b) => b -> KList a k ks -> KList a (Type -> k) (StripF a b :&&: ks)

infixr 9 :.

data LList l k where
  L0 :: LList l Type
  (:.) :: l -> LList l k -> LList l (Type -> k)

type family Labels (f :: k) :: LList l k

type instance Labels Maybe = 1 :. L0

type Labeled :: forall {s}. s -> Type -> Type
newtype Labeled (l :: s) a = On a

infixr 9 :@.

type LKList :: forall k s l. k -> LList s l -> LoT (LoArgs k l) -> Type
data LKList a ls ks where
  LK0 :: LKList a L0 LoT0
  (:@.) :: (b ~ a :@@: StripF a b) => Labeled s b -> LKList a l ks -> LKList a (s :. l) (StripF a b :&&: ks)

type Match :: forall l k1 k2. forall k -> LList l k1 -> LList l k2 -> LoT (LoArgs k k2) -> LoT (LoArgs k k1)
type family Match k ts ss as where
  Match k L0 ss as = LoT0
  Match k (l :. ls) L0 LoT0 = TypeError (Text "Not enough fields supplied. " :<>: ShowType l :<>: Text " was left unmatched.")
  Match k (s :. ls) (s :. ss) as = HeadLoT as :&&: Match k ls ss (TailLoT as)
  Match k ls (s :. ss) as = Match k ls ss (TailLoT as)

type LMatches1 f ss ks = Match (Type -> Type) (Labels f) ss ks
type LMatches2 f ss ks = Match (Type -> Type -> Type) (Labels f) ss ks

type GetKList :: forall {l} {k1} {k2}. LList l k1 -> LList l k2 -> Constraint
class GetKList (l1 :: LList l k1) (l2 :: LList l k2) where
  getKList :: forall {k} (f :: k) ks. LKList f l2 ks -> KList f k1 (Match k l1 l2 ks)

instance GetKList L0 l2 where
  getKList _ = K0

instance (GetKList ls ss) => GetKList (s :. ls) (s :. ss) where
  getKList (On x :@. xs) = x :@ getKList @ls @ss xs

instance {-# OVERLAPPABLE #-} (GetKList ls ss) => GetKList ls (s :. ss) where
  -- Usage of usafeCoerce here is to avoid adding another unnecessary argument
  -- for the class. GHC can't figure out that due to OVERLAPPABLE pragma, the
  -- last equation of Match is used without instatiating the types.
  getKList (_ :@. xs) = unsafeCoerce $ getKList @ls @ss xs
