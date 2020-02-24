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
import Data.Text


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

instance GMkGen (K1 f (DervType 'False Word)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.word Range.exponentialBounded

instance GMkGen (K1 f (DervType 'False Text)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.text (Range.constant 0 100) Gen.alphaNum
  
instance GMkGen (K1 f (DervType 'False Bool)) '[] where
  gMkGen _ _ _ _ = (K1 . Stock) <$> Gen.bool
  

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

instance (Typeable a, Generic a, GMkGen (Rep a) '[]) => GMkGen (K1 f (DervType 'True a)) '[] where
  gMkGen pos glist _ genMap = (K1 . Custom . to) <$> (gMkGen pos glist (Proxy :: Proxy a) genMap)
  

data DervType :: Bool -> Type -> Type where
  Custom :: a -> DervType 'True a 
  Stock :: a -> DervType 'False a 

type family IsCustom t (xs :: [*]) where
  IsCustom Int _  = 'False
  IsCustom Bool _ = 'False
  IsCustom Word _ = 'False
  IsCustom Text _ = 'False
  IsCustom t ts   = IsNotElem t ts

type family IsNotElem t (xs :: [*]) :: Bool where
  IsNotElem t '[]       = 'True
  IsNotElem t (t ': ts) = 'False
  IsNotElem t (_ ': ts) = IsNotElem t ts

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
  
  
