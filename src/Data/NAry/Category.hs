{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Category instances for n-ary products of categories.
module Data.NAry.Category where

import Control.Category
import Control.Category.Bifunctor
import Control.Category.Bifunctor qualified as B
import Data.Functor.Identity
import Data.Kind (Type)
import Data.NAry.Aux.FKind (FKind, HWit (..), LoTWit (..), hlWit, lotWit)
import Data.NAry.Aux.KList
import Data.NAry.KFunctor (KFunctor (..))
import Data.PolyKinded
import Prelude hiding (id, (.))

instance (Category r, FKind k) => Category (KList2 r k) where
  id :: forall a. KList2 r k a a
  id = case lotWit @a of
    LoTWitRec -> id :@ id
    LoTWit0 -> K2
  {-# INLINE id #-}
  (.) :: forall a b c. KList2 r k b c -> KList2 r k a b -> KList2 r k a c
  (.) = case lotWit @c of
    LoTWitRec -> \(f :@ fs) (g :@ gs) -> (f . g) :@ (fs . gs)
    LoTWit0 -> \K2 K2 -> K2
  {-# INLINE (.) #-}

-- * KProd category definition

-- This is a hack to circumvent Haskell's lack of unsaturated type synonyms.
data ProdObj l
  = ProdObj (LoT l)
  | EndoAp (HList l l) (ProdObj l)
  | Prod (Type -> Type -> Type) (ProdObj l) (ProdObj l)

type EndoApply :: forall k l. HList k l -> LoT k -> LoT l
type family EndoApply fs xs where
  EndoApply H0 xs = LoT0
  EndoApply (f :* fs) xs = (f :@@: xs) :&&: EndoApply fs xs

type Zip :: forall {k} l. (k -> k -> k) -> LoT l -> LoT l -> LoT l
type family Zip c as bs where
  Zip _ LoT0 LoT0 = LoT0
  Zip p as bs = p (HeadLoT as) (HeadLoT bs) :&&: Zip p (TailLoT as) (TailLoT bs)

type GetProdObj :: forall l. ProdObj l -> LoT l
type family GetProdObj obj where
  GetProdObj ('ProdObj obj) = obj
  GetProdObj ('EndoAp fs dom) = EndoApply fs (GetProdObj dom)
  GetProdObj ('Prod p as bs) = Zip p (GetProdObj as) (GetProdObj bs)

newtype KProd c l (a :: ProdObj l) (b :: ProdObj l) = KProd {getKProd :: KList2 c l (GetProdObj a) (GetProdObj b)}

pattern KProd' :: KList2 c l as bs -> KProd c l ('ProdObj as) ('ProdObj bs)
pattern KProd' ls = KProd ls

instance (Category (KList2 c k)) => Category (KProd c k) where
  id = KProd id
  {-# INLINE id #-}
  KProd f . KProd g = KProd (f . g)
  {-# INLINE (.) #-}

-- * Cartesian structure

instance
  ( EndoBifunctor c p
  ) =>
  EndoBifunctor (KProd c k) (Prod p)
  where
  bimap (KProd K2) (KProd K2) = KProd K2
  bimap (KProd (f :@ fs)) (KProd (g :@ gs)) = KProd (bimap f g :@ getKProd (bimap @_ @(Prod p) (KProd' fs) (KProd' gs)))

fstZip :: forall c {k} as bs. (Cartesian c, FKind k) => KList2 c k (Zip (Product c) as bs) as
fstZip =
  case lotWit @as of
    LoTWitRec -> B.fst :@ fstZip @_ @_ @(TailLoT bs)
    LoTWit0 -> K2

sndZip :: forall c {k} as bs. (Cartesian c, FKind k) => KList2 c k (Zip (Product c) as bs) bs
sndZip =
  case lotWit @bs of
    LoTWitRec -> B.snd :@ sndZip @_ @(TailLoT as)
    LoTWit0 -> K2

instance (Cartesian c, FKind k) => Cartesian (KProd c k) where
  type Product (KProd c k) = Prod (Product c)
  fst :: forall a b. KProd c k ('Prod (Product c) a b) a
  fst = KProd (fstZip @c @(GetProdObj a) @(GetProdObj b))
  snd :: forall a b. KProd c k ('Prod (Product c) a b) b
  snd = KProd (sndZip @c @(GetProdObj a) @(GetProdObj b))
  (&&&) = p
    where
      p :: forall r x y z. KProd c r x y -> KProd c r x z -> KProd c r x ('Prod (Product c) y z)
      p (KProd K2) (KProd K2) = KProd K2
      p (KProd (f :@ fs)) (KProd (g :@ gs)) = KProd ((f &&& g) :@ getKProd (KProd' fs `p` KProd' gs))

-- * n-ary products of Hask

type KList k = KList1 Identity k

pattern (:#) :: a -> KList k as -> KList (Type -> k) (a :&&: as)
pattern x :# xs = Identity x :+ xs
{-# COMPLETE (:#), K1 #-}

type KMap k = KProd (->) k

kapply :: forall k a b. KList2 (->) k a b -> KList k a -> KList k b
kapply (f :@ fs) (x :# xs) = f x :# kapply fs xs
kapply K2 K1 = K1

infixr 1 $*

-- Apply an n-ary morphism to a list of values
($*) :: forall k a b. KMap k a b -> KList k (GetProdObj a) -> KList k (GetProdObj b)
KProd f $* x = kapply f x

-- * instances for functors on n-ary products

class (Category c) => Endofunctor c f where
  fmapc :: a `c` b -> f a `c` f b

instance (FKind k, All KFunctor f) => Endofunctor (KMap k) (EndoAp f) where
  fmapc (KProd (f :: KList2 (->) k a b)) = KProd (h @k @f)
    where
      h :: forall l (h :: HList k l). (FKind l, All KFunctor h) => KList2 (->) l (EndoApply h a) (EndoApply h b)
      h = case hlWit @h of
        HWit0 -> K2
        HWitRec @ll @hh @hs -> kfmap @hh f :@ h @ll @hs

-- * Recursion-schemes

type family Base (b :: k) :: k -> k

class (Endofunctor c (Base b)) => Recursive c b where
  project :: b `c` Base b b

fold :: (Category c, Recursive c b) => (Base b a `c` a) -> b `c` a
fold f = c where c = f . fmapc c . project

para :: (Category c, Cartesian c, Recursive c b) => (Base b (Product c b a) `c` a) -> b `c` a
para f = p where p = f . fmapc (id &&& p) . project

class (Endofunctor c (Base b)) => Corecursive c b where
  embed :: Base b b `c` b

unfold :: (Category c, Corecursive c b) => (a `c` Base b a) -> a `c` b
unfold f = c where c = embed . fmapc c . f
