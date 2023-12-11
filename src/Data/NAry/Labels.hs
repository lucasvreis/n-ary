{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module Data.NAry.Labels where

import Data.Kind (Type)
import GHC.TypeLits (Symbol)
import Generics.Kind
import Type.Errors

data KList a ks where
  L0 :: KList a Type
  (:+) :: a -> KList a ks -> KList a (Type -> ks)

type family Labels (f :: k) :: KList Symbol k

newtype Labeled (s :: Symbol) a = On a

type Match :: forall k l. KList Symbol l -> KList Symbol k -> LoT k -> LoT l
type family Match ls ss as where
  Match L0 ss as = LoT0
  Match (l :+ ls) L0 LoT0 = TypeError (Text "Not enough fields supplied. " :<>: ShowType l :<>: Text " was left unmatched.")
  Match (s :+ ls) (s :+ ss) (a :&&: as) = a :&&: Match ls ss as
  Match ls (s :+ ss) (a :&&: as) = Match ls ss as
