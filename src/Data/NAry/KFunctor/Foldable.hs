{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.NAry.KFunctor.Foldable where

import Control.Category
import Prelude hiding (id, (.))

class (Category c) => Endofunctor f c where
  fmapc :: c a b -> c (f a) (f b)

class (Endofunctor f c) => Recursive f c b where
  project :: b `c` f b

catac :: (Category c, Recursive f c b) => (f a `c` a) -> b `c` a
catac f = c
  where c = f . fmapc c . project
