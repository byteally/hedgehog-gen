# hedgehog-gen
Customizable Gen for ADT using Generics

[![Hackage](https://img.shields.io/hackage/v/hedgehog-gen.svg?logo=haskell)](https://hackage.haskell.org/package/hedgehog-gen)

## Tutorial

```haskell

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog.Gen.Generic
import Data.Function

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

```
