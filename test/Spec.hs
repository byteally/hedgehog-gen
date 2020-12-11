{-# LANGUAGE DeriveGeneric, TypeApplications, DataKinds, OverloadedStrings #-}
module Main where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog.Gen.Generic
import Data.Function
import Data.Text (Text)
import GHC.Generics

data Gender = Male | Female | Other
  deriving (Show, Eq, Generic)

data User = User
  { name :: Text
  , age :: Word
  , gender :: Gender
  } deriving (Show, Eq, Generic)

userGen1 :: Hedgehog.Gen User
userGen1 = mkGen emptyGens

userGen2 :: Hedgehog.Gen User
userGen2 = mkGen $ emptyGens
  & byField @User @"age" (Gen.word (Range.constant 1 120))
  & byPos @User @1 (Gen.element ["foo", "bar", "baz"])


data UUID = UUID {uuid :: Text}
  deriving (Show, Eq)

---
data EventId = EventId { rawEventId :: UUID } deriving (Eq, Show)

data Event = Event
  { evtId :: !EventId
  , evtFoo:: !String
  , evtUser :: !User
  } deriving (Eq, Show, Generic)

eventGen :: Hedgehog.Gen Event
eventGen = mkGenWith (eventIdGen :& stringGen :& GNil) emptyGens
  where
    eventIdGen = Gen.element [ EventId $ UUID "c2cc10e1-57d6-4b6f-9899-38d972112d8c"
                             , EventId $ UUID "550e8400-e29b-41d4-a716-446655440000"
                             ]
    stringGen :: Gen String
    stringGen = Gen.element ["foo", "bar", "baz"]
main :: IO ()
main = do
  print =<< Gen.sample eventGen
  pure ()
