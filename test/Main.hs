{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Data.NAry.KFoldable
import Data.NAry.KFunctor
import Data.NAry.KTraversable
import Generics.Kind.TH

data MyLabel = Foo | Bar | Baz

data MyThing a b c
  = C1 a b (MyThing a b c)
  | C2 c
  deriving (Eq, Show)

$(deriveGenericK ''MyThing)
deriving instance (KFunctor MyThing)
deriving instance (KFoldable MyThing)
deriving instance (KTraversable MyThing)

type instance Labels MyThing = Foo :. Bar :. Baz :. L0

data MyThing2 a b = D1 a b
  deriving (Eq, Show)

$(deriveGenericK ''MyThing2)
deriving instance (KFunctor MyThing2)
deriving instance (KFoldable MyThing2)
deriving instance (KTraversable MyThing2)

type instance Labels MyThing2 = Foo :. Baz :. L0

myMap = On @Foo ("Hello " ++) :@. On @Bar (lfmap @MyThing2 myMap) :@. On @Baz tail :@. LK0 @(->)

myValue :: MyThing String (MyThing2 String [()]) [()]
myValue = C1 "hello" (D1 "world" [(), (), ()]) (C1 "how are you?" (D1 "fine" [()]) (C2 [()]))

myResult = lfmap @MyThing myMap myValue

-- >>> myResult
-- C1 "Hello hello" (D1 "Hello world" [(),()]) (C1 "Hello how are you?" (D1 "Hello fine" []) (C2 []))

main :: IO ()
main = putStrLn "Test suite not yet implemented."
