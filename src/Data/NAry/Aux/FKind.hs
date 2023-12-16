{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

{- | Class for doing type-level matching and recursion on GADTs parametrized by
function types.
-}
module Data.NAry.Aux.FKind where

import Data.Kind (Type)
import Data.PolyKinded (LoT (..))
import Unsafe.Coerce (unsafeCoerce)
import Data.NAry.Aux.KList (HList (..))

data FKWit k where
  FKWit0 :: FKWit Type
  FKWitRec :: (FKind k) => FKWit (Type -> k)

class FKind k where
  fkWit :: FKWit k

instance FKind Type where
  fkWit = FKWit0

instance (FKind k) => FKind (Type -> k) where
  fkWit = FKWitRec

type LoTWit :: forall k. LoT k -> Type
data LoTWit (a :: LoT k) where
  LoTWit0 :: LoTWit LoT0
  LoTWitRec :: forall k (a :: Type) (as :: LoT k). (FKind k) => LoTWit (a :&&: as)

{- | GHC inference is not smart enough. This is witness of the fact @LoT0@ and
     @:&&:@ are the unique constructors of @LoT@.
-}
lotWit :: forall {k} (a :: LoT k). (FKind k) => LoTWit a
lotWit =
  case fkWit @k of
    FKWit0 -> unsafeCoerce LoTWit0
    FKWitRec -> unsafeCoerce (LoTWitRec @k)
{-# INLINE lotWit #-}

type HWit :: forall (k :: Type) (l :: Type). HList k l -> Type
data HWit h where
  HWit0 :: HWit H0
  HWitRec :: forall {k} l (a :: k) (as :: HList k l). (FKind l) => HWit (a :* as)

{- | GHC inference is not smart enough. This is witness of the fact @H0@ and
     @:*@ are the unique constructors of @HList@.
-}
hlWit :: forall {k} {l} (a :: HList k l). (FKind l) => HWit @k @l a
hlWit =
  case fkWit @l of
    FKWit0 -> unsafeCoerce HWit0
    FKWitRec @ll -> unsafeCoerce (HWitRec @ll)
{-# INLINE hlWit #-}
