{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}

{-# LANGUAGE DeriveGeneric #-}
module Hedgehog.Gen.Generic
  ( mkGen
  , mkGenWith
  , emptyGens
  , byType
  , byField
  , byPos
  , GenList (..)
  , GenMap
  , GMkGen
  ) where

import GHC.Generics
import GHC.TypeLits
import GHC.Exts
import Data.TypeRepMap (TypeRepMap)
import qualified Data.TypeRepMap as TMap
import Data.Proxy
import Data.Typeable
import Data.Kind
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Hedgehog.Internal.Shrink as Shrink
import qualified Hedgehog.Internal.Gen as GenI
import Data.Text
import Data.Int
import Data.Word
import Data.List.NonEmpty (NonEmpty)
import Data.Sequence (Seq)
import Data.Map (Map)
import Data.IntMap (IntMap)
import Data.Set (Set)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HSet



-- |'mkGen' creates a 'Gen.Gen' for any __/a/__ having 'Generic'.
--  'mkGen' assumes 'Generic' instance is present for all the types in the the transitive dependency of __/a/__.
mkGen :: forall a.(Generic a, GMkGen (Rep a) '[], Typeable a) =>
  GenMap -- ^ Map containing type-based and field-based overrides of `Gen.Gen`
  -> Hedgehog.Gen a -- ^ Generator for any __/a/__ having 'Generic' instance
mkGen genMap = mkGenWith GNil genMap

-- |'mkGenWith' creates a 'Gen.Gen' for any __/a/__ having 'Generic'.
--   It is same as 'mkGen', except that it takes HList of 'Gen.Gen's for all types not having 'Generic' instance in the transitive dependency of __/a/__
mkGenWith :: forall a glist.
  ( Generic a, GMkGen (Rep a) glist, Typeable a
  ) => GenList glist  -- ^ HList of 'Gen.Gen's for types not having 'Generic' instance
    -> GenMap         -- ^ Map containing type-based and field-based overrides of `Gen.Gen`
    -> Hedgehog.Gen a -- ^ Generator for any __/a/__ having 'Generic' instance
mkGenWith glist genMap = to <$> (gMkGen 1 glist (Proxy :: Proxy a) genMap)

-- | Hetrogenous List of Gen
data GenList (or :: [*]) where
  GNil :: GenList '[]
  (:&) :: Gen x -> GenList xs -> GenList (x ': xs)

infixr 5 :&

-- | Map to hold type-based and field-based overrides of `Gen.Gen`
type GenMap = TypeRepMap Hedgehog.Gen

-- | 'emptyGens' creates a empty map of overrides.
emptyGens :: GenMap
emptyGens = TMap.empty

-- | 'byType' is used to override the 'Gen.Gen' for type __/t/__.
--   This have lower precedences than 'byField' & 'byPos' i.e. when there is field or position based override applied to the target type, that gets the percedence. If there is no such overrides, all the occurrences of this type uses the 'Gen.Gen' provided by this override.
byType :: Typeable t => Hedgehog.Gen t -> GenMap -> GenMap
byType = TMap.insert

-- | 'byField' is used to override the 'Gen.Gen' for type __/t/__ of field named __/field/__ in type __/s/__ .
--   This has higher precedences than 'byType' and 'byPos'
byField :: forall s (field :: Symbol) t.
  ( KnownSymbol field
  , Typeable s
  , Typeable t
  , FromEither (ValidateSel s (Rep s) field t)
  ) => Hedgehog.Gen t -> GenMap -> GenMap
byField gen = TMap.insert (Field <$> gen :: Gen (Field s field t))

-- | 'byPos' is used to override the 'Gen.Gen' for type __/t/__ at positon __/pos/__ in type __/s/__ .
--   This has higher precedences than 'byType' and lower precedence thab 'byField'
byPos :: forall s (pos :: Nat) t.
  ( KnownNat pos
  , Typeable s
  , Typeable t
  , FromEither (ValidatePos s (Rep s) pos 1 t)
  ) => Hedgehog.Gen t -> GenMap -> GenMap
byPos gen = TMap.insert (Pos <$> gen :: Gen (Pos s pos t))


newtype Field s (field :: Symbol) t = Field {getFieldGen :: t}
newtype Pos s (pos :: Nat) t = Pos {getPosGen :: t}




class GMkGen f (or ::[*]) where
  gMkGen :: (Typeable s) => Word -> GenList or -> Proxy s -> GenMap -> Hedgehog.Gen (f a)

instance (GMkGen f or) => GMkGen (D1 m f) or where
  gMkGen pos glist pxyS genMap  = M1 <$> gMkGen pos glist pxyS genMap

instance (GMkGen f or, GMkGen g or) => GMkGen (f :+: g) or where
  gMkGen pos glist pxyS genMap  = Gen.choice [ L1 <$> gMkGen pos glist pxyS genMap
                                             , R1 <$> gMkGen pos glist pxyS genMap
                                             ]

instance (GMkGen f or) => GMkGen (C1 m f) or where
  gMkGen pos glist pxyS genMap= M1 <$> gMkGen pos glist pxyS genMap

instance (GMkGen f or, GMkGen g or) => GMkGen (f :*: g) or where
  gMkGen pos glist pxyS genMap = (:*:) <$> (gMkGen pos glist pxyS genMap) <*> (gMkGen (pos+1) glist pxyS genMap)

instance GMkGen U1 or where
  gMkGen _ _ _ _ = pure U1

{-
instance ( Typeable a
         , KnownSymbol fn
         , GMkGen (K1 f (DervType (IsCustom a or) a)) or
         ) => GMkGen (S1 ('MetaSel 'Nothing up sst st) (K1 f a)) or where
  gMkGen pos glist pxyS genMap=
    let
      typeGen = TMap.lookup genMap :: Maybe (Hedgehog.Gen a)
      getFieldGen' :: (Typeable s, Typeable a, KnownSymbol fn) => Proxy s -> Maybe (Hedgehog.Gen (Pos s pos a))
      getFieldGen' _ = TMap.lookup genMap
      fieldGen :: Maybe (Hedgehog.Gen a)
      fieldGen = (fmap . fmap) getFieldGen (getFieldGen' pxyS)
    in M1 <$> case fieldGen of
      Just gen -> K1 <$> gen
      Nothing -> case typeGen of
        Just gen -> K1 <$> gen
        Nothing  ->
          let g = gMkGen pos glist pxyS genMap :: Hedgehog.Gen (K1 f (DervType (IsCustom a or) a) a)
          in flip fmap g $ \case
            K1 (Custom a) -> K1 a
            K1 (Stock a) -> K1 a
-}

instance ( Typeable a
         , KnownSymbol fn
         , GMkGen (K1 f (DervType (IsCustom a or) a)) or
         ) => GMkGen (S1 ('MetaSel ('Just fn) up sst st) (K1 f a)) or where
  gMkGen pos glist pxyS genMap=
    let
      typeGen = TMap.lookup genMap :: Maybe (Hedgehog.Gen a)
      getFieldGen' :: (Typeable s, Typeable a, KnownSymbol fn) => Proxy s -> Maybe (Hedgehog.Gen (Field s fn a))
      getFieldGen' _ = TMap.lookup genMap
      posGen :: Maybe (Hedgehog.Gen a)
      posGen = case someNatVal (toInteger pos) of
        Just (SomeNat pxyPos) ->
          let
            getPosGen' :: (Typeable s, Typeable a, KnownNat pos) => Proxy s -> Proxy pos -> Maybe (Hedgehog.Gen (Pos s pos a))
            getPosGen' _ _ = TMap.lookup genMap
          in (fmap . fmap) getPosGen (getPosGen' pxyS pxyPos)
        Nothing -> Nothing
      fieldGen :: Maybe (Hedgehog.Gen a)
      fieldGen = (fmap . fmap) getFieldGen (getFieldGen' pxyS)
    in M1 <$> case fieldGen of
      Just gen -> K1 <$> gen
      Nothing -> case posGen of
        Just gen -> K1 <$> gen
        Nothing -> case typeGen of
          Just gen -> K1 <$> gen
          Nothing  ->
            let g = gMkGen pos glist pxyS genMap :: Hedgehog.Gen (K1 f (DervType (IsCustom a or) a) a)
            in flip fmap g $ \case
              K1 (Custom a) -> K1 a
              K1 (Stock a) -> K1 a

instance GMkGen (K1 f (DervType 'False Int)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.int Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Int8)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.int8 Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Int16)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.int16 Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Int32)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.int32 Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Int64)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.int64 Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Word)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.word Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Word8)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.word8 Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Word16)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.word16 Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Word32)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.word32 Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Word64)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.word64 Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Char)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.alphaNum

instance GMkGen (K1 f (DervType 'False Text)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.text (Range.constant 0 100) Gen.alphaNum

instance GMkGen (K1 f (DervType 'False Bool)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.bool

instance GMkGen (K1 f (DervType 'False Double)) '[] where
  gMkGen _ _ _ _ = fmap (K1 . Stock) $ Gen.double $ Range.exponentialFloat (-10) 10

instance GMkGen (K1 f (DervType 'False Float)) '[] where
  gMkGen _ _ _ _ = fmap (K1 . Stock) $ Gen.float $ Range.exponentialFloat (-10) 10

instance
  ( GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    Typeable a
  ) => GMkGen (K1 f (DervType 'False (Maybe a))) ors where
  gMkGen p glist _ gmap =
    let
      g = gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      toMaybe :: K1 k (DervType (IsCustom a ors) a) b -> K1 k (DervType 'False (Maybe a)) b
      toMaybe (K1 dva) = case dva of
        Stock a -> K1 (Stock $ Just a)
        Custom a -> K1 (Stock $ Just a)
    in Gen.sized $ \n ->
      Gen.frequency [ (2, pure $ K1 $ Stock Nothing),
                      (1 + fromIntegral n, fmap toMaybe g)
                    ]

instance
  ( GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    Typeable a
  ) => GMkGen (K1 f (DervType 'False [a])) ors where
  gMkGen p glist _ gmap =
    let
      g = gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      getVal :: K1 k (DervType (IsCustom a ors) a) b -> a
      getVal (K1 dva) = case dva of
        Stock a -> a
        Custom a -> a
    in fmap (K1. Stock) $ Gen.list (Range.constant 0 10) $ fmap getVal g

instance
  ( GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    Typeable a
  ) => GMkGen (K1 f (DervType 'False (NonEmpty a))) ors where
  gMkGen p glist _ gmap =
    let
      g = gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      getVal :: K1 k (DervType (IsCustom a ors) a) b -> a
      getVal (K1 dva) = case dva of
        Stock a -> a
        Custom a -> a
    in fmap (K1. Stock) $ Gen.nonEmpty (Range.constant 1 10) $ fmap getVal g

instance
  ( GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    Typeable a
  ) => GMkGen (K1 f (DervType 'False (Seq a))) ors where
  gMkGen p glist _ gmap =
    let
      g = gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      getVal :: K1 k (DervType (IsCustom a ors) a) b -> a
      getVal (K1 dva) = case dva of
        Stock a -> a
        Custom a -> a
    in fmap (K1. Stock) $ Gen.seq (Range.constant 0 10) $ fmap getVal g


instance
  ( GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    Typeable a
  ) => GMkGen (K1 f (DervType 'False (Vector a))) ors where
  gMkGen p glist _ gmap =
    let
      g = gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      getVal :: K1 k (DervType (IsCustom a ors) a) b -> a
      getVal (K1 dva) = case dva of
        Stock a -> a
        Custom a -> a
    in fmap (K1. Stock . V.fromList) $ Gen.list (Range.constant 0 10) $ fmap getVal g


instance
  ( GMkGen (K1 f (DervType (IsCustom k ors) k)) ors,
    GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    Ord k,
    Typeable k,
    Typeable a
  ) => GMkGen (K1 f (DervType 'False (Map k a))) ors where
  gMkGen p glist _ gmap =
    let
      k = getVal <$> gMkGen @(K1 f (DervType (IsCustom k ors) k)) p glist (Proxy @k) gmap
      v = getVal <$> gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      kv = (,) <$> k <*> v
      getVal :: K1 f (DervType (IsCustom v ors) v) x -> v
      getVal (K1 dva) = case dva of
        Stock a -> a
        Custom a -> a
    in fmap (K1. Stock) $ Gen.map (Range.constant 0 10) kv

instance
  ( GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    GMkGen (K1 f (DervType (IsCustom b ors) b)) ors,
    Typeable a,
    Typeable b
  ) => GMkGen (K1 f (DervType 'False (Either a b))) ors where
  gMkGen p glist _ gmap =
    let
      a = getVal <$> gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      b = getVal <$> gMkGen @(K1 f (DervType (IsCustom b ors) b)) p glist (Proxy @b) gmap
      getVal :: K1 k (DervType (IsCustom v ors) v) x -> v
      getVal (K1 dva) = case dva of
        Stock v -> v
        Custom v -> v
    in fmap (K1. Stock) $ Gen.sized $ \n ->
      Gen.frequency [ (2, fmap Left a),
                      (1 + fromIntegral n, fmap Right b)
                    ]

instance
  ( GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    Ord a,
    Typeable a
  ) => GMkGen (K1 f (DervType 'False (Set a))) ors where
  gMkGen p glist _ gmap =
    let
      g = gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      getVal :: K1 k (DervType (IsCustom a ors) a) b -> a
      getVal (K1 dva) = case dva of
        Stock a -> a
        Custom a -> a
    in fmap (K1. Stock) $ Gen.set (Range.constant 0 10) $ fmap getVal g

{- TODO:
instance
  ( GMkGen (K1 f (DervType (IsCustom a ors) a)) ors,
    Ord a,
    Typeable a
  ) => GMkGen (K1 f (DervType 'False (HashSet a))) ors where
  gMkGen p glist _ gmap =
    let
      g = gMkGen @(K1 f (DervType (IsCustom a ors) a)) p glist (Proxy @a) gmap
      getVal :: K1 k (DervType (IsCustom a ors) a) b -> a
      getVal (K1 dva) = case dva of
        Stock a -> a
        Custom a -> a
    in fmap (K1. Stock) $ hashset (Range.constant 0 10) $ fmap getVal g

hashmap :: (MonadGen m, Ord k) => Range Int -> m (k, v) -> m (HashMap k v)
hashmap range gen =
  GenI.sized $ \size ->
    GenI.ensure ((>= Range.lowerBound size range) . HMap.size) .
    fmap HMap.fromList .
    (sequence =<<) .
    GenI.shrink Shrink.list $ do
      k <- GenI.integral_ range
      uniqueByKey k gen

hashset :: (MonadGen m, Ord a) => Range Int -> m a -> m (HashSet a)
hashset range gen =
  fmap HMap.keysSet . fmap range $ fmap (, ()) gen
-}

instance ( Typeable t
         , Typeable x
         ) => GMkGen (K1 f (DervType 'False t)) '[x] where
  gMkGen _ (gen :& GNil) _ _ = case (eqT :: Maybe ( x :~: t)) of
    Just Refl -> (K1 . Stock) <$> gen
    Nothing -> error "Panic: Invariant violated"

instance ( Typeable t
         , Typeable x1
         , GMkGen (K1 f (DervType 'False t)) (x2 ': xs)
         ) => GMkGen (K1 f (DervType 'False t)) (x1 ': x2 ': xs) where
  gMkGen pos (gen :& glist) pxy genMap = case (eqT :: Maybe ( x1 :~: t)) of
    Just Refl -> (K1 . Stock) <$> gen
    Nothing -> gMkGen pos glist pxy genMap

instance (Typeable a, Generic a, GMkGen (Rep a) xs) => GMkGen (K1 f (DervType 'True a)) xs where
  gMkGen pos glist _ genMap = (K1 . Custom . to) <$> (gMkGen pos glist (Proxy :: Proxy a) genMap)


data DervType :: Bool -> Type -> Type where
  Custom :: a -> DervType 'True a
  Stock :: a -> DervType 'False a

instance Functor (DervType b) where
  fmap f (Custom v) = Custom (f v)
  fmap f (Stock v) = Stock (f v)

type family IsCustom t (xs :: [*]) where
  IsCustom Int _  = 'False
  IsCustom Int8 _ = 'False
  IsCustom Int16 _ = 'False
  IsCustom Int32 _ = 'False
  IsCustom Int64 _ = 'False
  IsCustom Bool _ = 'False
  IsCustom Char _ = 'False
  IsCustom Word _ = 'False
  IsCustom Word8 _ = 'False
  IsCustom Word16 _ = 'False
  IsCustom Word32 _ = 'False
  IsCustom Word64 _ = 'False
  IsCustom Text _ = 'False
  IsCustom Double _ = 'False
  IsCustom Float _ = 'False
  IsCustom (Maybe _) _ = 'False
  IsCustom [_] _ = 'False
  IsCustom (Seq _) _ = 'False
  IsCustom (NonEmpty _) _ = 'False
  IsCustom (Vector _) _ = 'False
  IsCustom (Map _ _) _ = 'False
  IsCustom (IntMap _) _ = 'False
  IsCustom (Set _) _ = 'False
  IsCustom (HashMap _ _) _ = 'False
  IsCustom (HashSet _) _ = 'False
  IsCustom (Either _ _) _ = 'False
  IsCustom t ts   = IsNotElem t ts

type family IsNotElem t (xs :: [*]) :: Bool where
  IsNotElem t '[]       = 'True
  IsNotElem t (t ': ts) = 'False
  IsNotElem t (_ ': ts) = IsNotElem t ts

class SingBool (b ::Bool) where
  singBool :: Proxy# b -> Bool

instance SingBool 'True where
  singBool _ = True

instance SingBool 'False where
  singBool _ = False

type family FromEither (m :: Either ErrorMessage Constraint) :: Constraint where
  FromEither ('Left ex) = TypeError ex
  FromEither ('Right c) = c

type family ValidateSelK (m :: Either ErrorMessage Constraint) s (srep :: * -> *) (fld :: Symbol) t :: Either ErrorMessage Constraint where
  ValidateSelK ('Left ex) s srep fld t = ValidateSel s srep fld t
  ValidateSelK ('Right c) _ _ _ _      = 'Right c

type family ValidatePosK (m :: Either ErrorMessage Constraint) s (srep :: * -> *) (pos :: Nat) (cpos :: Nat) t :: Either ErrorMessage Constraint where
  ValidatePosK ('Left ex) s srep pos newpos t = ValidatePos s srep pos newpos t
  ValidatePosK ('Right c) _ _ _ _ _         = 'Right c

type family ValidateSel s (srep :: * -> *) (fld :: Symbol) t :: Either ErrorMessage Constraint where
  ValidateSel s (D1 i f) fld t = ValidateSel s f fld t
  ValidateSel s (f :+: g) fld t = ValidateSelK (ValidateSel s f fld t) s g fld t
  ValidateSel s (C1 ('MetaCons cn _ 'False) _) fld t = 'Left ('Text "The constructor " ':<>: 'ShowType cn ':<>: 'Text " does not have named fields")
  ValidateSel s (C1 i c) fld t = ValidateSel s c  fld t
  ValidateSel s (f :*: g) fld t = ValidateSelK (ValidateSel s f fld t) s g fld t
  ValidateSel s (S1 ('MetaSel ('Just fld) _ _ _) (K1 i t1)) fld t2 = 'Right (t1 ~ t2)
  ValidateSel s (S1 ('MetaSel ('Just fld1) _ _ _) (K1 i _)) fld2 _ = 'Left ('Text "type '" ':<>: 'ShowType s ':<>: 'Text "' does not have a field named: " ':<>: 'ShowType fld2)


type family ValidatePos s (srep :: * -> *) (pos :: Nat) (cpos ::Nat) t :: Either ErrorMessage Constraint where
  ValidatePos s (D1 i f) pos cpos t = ValidatePos s f pos cpos t
  ValidatePos s (f :+: g) pos cpos t = ValidatePosK (ValidatePos s f pos cpos t) s g pos cpos t
  ValidatePos s (C1 i c) pos cpos t = ValidatePos s c pos cpos t
  ValidatePos s (f :*: g) pos cpos t = ValidatePosK (ValidatePos s f pos cpos t) s g pos (cpos+1) t
  ValidatePos s (S1 ('MetaSel _ _ _ _) (K1 i t1)) pos pos t2 = 'Right (t1 ~ t2)
  ValidatePos s (S1 ('MetaSel _ _ _ _) (K1 i _)) pos2 _ _ = 'Left ('Text "type '" ':<>: 'ShowType s ':<>: 'Text "' does not have a positon numbered: " ':<>: 'ShowType pos2)
