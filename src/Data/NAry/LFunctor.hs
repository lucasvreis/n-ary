{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.NAry.LFunctor where

import Data.Kind (Type)
import Data.NAry.KFunctor
import Data.NAry.Labels
import Data.PolyKinded
import GHC.TypeLits (Symbol)
import Unsafe.Coerce (unsafeCoerce)

type LMappings :: forall k. KList Symbol k -> LoT k -> LoT k -> Type
data LMappings ss as bs where
  LM0 :: LMappings L0 LoT0 LoT0
  (:#.) ::
    Labeled s (a -> b) ->
    LMappings ss as bs ->
    LMappings (s :+ ss) (a :&&: as) (b :&&: bs)

class GetLMappings ls ss where
  getLMappings :: LMappings ss as bs -> Mappings (Match ls ss as) (Match ls ss bs)

instance GetLMappings L0 ss where
  getLMappings _ = M0

instance (GetLMappings ls ss) => GetLMappings (s :+ ls) (s :+ ss) where
  getLMappings (On f :#. fs) = f :# getLMappings @ls @ss fs

instance
  {-# OVERLAPPABLE  #-}
  ( GetLMappings ls ss
  ) =>
  GetLMappings ls (s :+ ss)
  where
  getLMappings (_ :#. fs) = unsafeCoerce $ getLMappings @ls @ss fs

lfmap ::
  forall f ss as bs.
  (GetLMappings (Labels f) ss) =>
  (KFunctor f) =>
  LMappings ss as bs ->
  f :@@: Match (Labels f) ss as ->
  f :@@: Match (Labels f) ss bs
lfmap m = kfmap @f @(Match (Labels f) ss as) @(Match (Labels f) ss bs) (getLMappings @(Labels f) m)
