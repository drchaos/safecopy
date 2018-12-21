{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, UndecidableInstances, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.SafeCopy.Instances where

import Data.SafeCopy.SafeCopy

#if !MIN_VERSION_base(4,8,0)
import           Control.Applicative
#endif
import           Control.Monad
import           Codec.Serialise
import           Codec.Serialise.Decoding
import           Codec.Serialise.Encoding
import qualified Data.Array as Array
import qualified Data.Array.Unboxed as UArray
import qualified Data.Array.IArray as IArray
import qualified Data.ByteString.Lazy.Char8 as L
import qualified Data.ByteString.Char8 as B
import qualified Data.Foldable as Foldable
import           Data.Fixed (HasResolution, Fixed)
import           Data.Int
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import           Data.Ix
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map
import           Data.Ratio (Ratio)
import qualified Data.Sequence as Sequence
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import           Data.Time.Calendar (Day(..))
import           Data.Time.Clock (DiffTime, NominalDiffTime, UniversalTime(..), UTCTime(..))
import           Data.Time.Clock.TAI (AbsoluteTime, taiEpoch, addAbsoluteTime, diffAbsoluteTime)
import           Data.Time.LocalTime (LocalTime(..), TimeOfDay(..), TimeZone(..), ZonedTime(..))
import qualified Data.Tree as Tree
#if MIN_VERSION_base(4,7,0)
import           Data.Typeable hiding (Proxy)
#else
import           Data.Typeable
#endif
import           Data.Word
import           System.Time (ClockTime(..), TimeDiff(..), CalendarTime(..), Month(..))
import qualified System.Time as OT
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Primitive as VP
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Unboxed as VU

import Data.Monoid ((<>))

instance SafeCopy a => SafeCopy (Prim a) where
  kind = primitive
  getCopy = contain $
            do e <- unsafeUnPack getCopy
               return $ Prim e
  putCopy (Prim e)
    = contain $ unsafeUnPack (putCopy e)

instance {-# OVERLAPPABLE #-} SafeCopy a => SafeCopy [a] where
  kind = primitive
  getCopy = contain $ do
    getter <- getSafeGet
    mn <- decodeListLenOrIndef
    d <- case mn of
      Nothing -> decodeSequenceLenIndef (flip (:)) [] reverse   getter
      Just n  -> decodeSequenceLenN     (flip (:)) [] reverse n getter
    return d

  putCopy lst = contain $ versionHeader <>
                  if null lst then
                          encodeListLen 0
                    else
                          encodeListLenIndef
                       <> mconcat (map putter lst)
                       <> encodeBreak
    where
      (versionHeader, putter) = getSafePut
  errorTypeName = typeName1

instance {-# INCOHERENT #-} SafeCopy [Char] where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName

instance SafeCopy a => SafeCopy (NonEmpty.NonEmpty a) where
    getCopy = contain $ do
      l <- safeGet
      case NonEmpty.nonEmpty l of
        Nothing -> fail "Expected a NonEmpty list, but an empty list was found!"
        Just xs -> return xs
    putCopy = contain . safePut . NonEmpty.toList
    errorTypeName = typeName1

instance SafeCopy a => SafeCopy (Maybe a) where
    getCopy = contain $ do
                          n <- decodeListLen
                          case n of
                            0 -> return Nothing
                            1 -> do !x <- safeGet
                                    return (Just x)
                            _ -> fail "unknown tag"
    putCopy (Just a) = contain $ encodeListLen 1 <> safePut a
    putCopy Nothing = contain $ encodeListLen 0
    errorTypeName = typeName1

encodeSetSkel :: SafeCopy a
              => (s -> Int)
              -> ((a -> Encoding -> Encoding) -> Encoding -> s -> Encoding)
              -> s
              -> Encoding
encodeSetSkel size foldr' =
  encodeContainerSkel
    encodeListLen
    size
    foldr'
    (\a b -> putter a <> b)
    versionHeader
  where
    (versionHeader, putter) = getSafePut
{-# INLINE encodeSetSkel #-}

decodeSetSkel :: SafeCopy a
              => ([a] -> c) -> Decoder s c
decodeSetSkel fromList = do
  getter <- getSafeGet
  n <- decodeListLen
  fmap fromList (replicateM n getter)
{-# INLINE decodeSetSkel #-}

instance (SafeCopy a, Ord a) => SafeCopy (Set.Set a) where
    getCopy = contain $ decodeSetSkel Set.fromList
    putCopy = contain . encodeSetSkel Set.size Set.foldr
    errorTypeName = typeName1

instance SafeCopy IntSet.IntSet where
    getCopy = contain $ decodeSetSkel IntSet.fromList
    putCopy = contain . encodeSetSkel IntSet.size IntSet.foldr
    errorTypeName = typeName

encodeMapSkel :: (SafeCopy k, SafeCopy v)
              => (m -> Int)
              -> ((k -> v -> Encoding -> Encoding) -> Encoding -> m -> Encoding)
              -> m
              -> Encoding
encodeMapSkel size foldrWithKey =
  encodeContainerSkel
    encodeMapLen
    size
    foldrWithKey
    (\k v b -> keyPutter k <> valPutter v <> b)
    (keyVersionHeader <> valVersionHeader)
  where
    (keyVersionHeader, keyPutter) = getSafePut
    (valVersionHeader, valPutter) = getSafePut
{-# INLINE encodeMapSkel #-}

decodeMapSkel :: (SafeCopy k, SafeCopy v)
              => ([(k,v)] -> m)
              -> Decoder s m
decodeMapSkel fromList = do
  keyGetter <- getSafeGet
  valGetter <- getSafeGet
  n <- decodeMapLen
  let decodeEntry = do
        !k <- keyGetter
        !v <- valGetter
        return (k, v)
  fmap fromList (replicateM n decodeEntry)
{-# INLINE decodeMapSkel #-}

instance (SafeCopy a, SafeCopy b, Ord a) => SafeCopy (Map.Map a b) where
    getCopy = contain $ decodeMapSkel Map.fromList
    putCopy = contain . encodeMapSkel Map.size Map.foldrWithKey
    errorTypeName = typeName2

instance (SafeCopy a) => SafeCopy (IntMap.IntMap a) where
    getCopy = contain $ decodeMapSkel IntMap.fromList
    putCopy = contain . encodeMapSkel IntMap.size IntMap.foldrWithKey
    errorTypeName = typeName1

instance (SafeCopy a) => SafeCopy (Sequence.Seq a) where
    getCopy = contain $ decodeContainerSkelWithReplicate
                          decodeListLen
                          Sequence.replicateM
                          mconcat
    putCopy s = contain $ encodeContainerSkel
                            encodeListLen
                            Sequence.length
                            Foldable.foldr
                            (\a b -> putter a <> b)
                            versionHeader
                            s
      where
        (versionHeader, putter) = getSafePut
    errorTypeName = typeName1

instance (SafeCopy a) => SafeCopy (Tree.Tree a) where
    getCopy = contain $ decodeListLenOf 2 *> (Tree.Node <$> safeGet <*> safeGet)
    putCopy (Tree.Node root sub) = contain $ encodeListLen 2 <> safePut root <> safePut sub
    errorTypeName = typeName1

iarray_getCopy :: (Ix i, SafeCopy e, SafeCopy i, IArray.IArray a e) => Contained (Decoder s (a i e))
iarray_getCopy = contain $ do decodeListLenOf 3
                              getIx <- getSafeGet
                              liftM3 mkArray getIx getIx safeGet
    where
      mkArray l h xs = IArray.listArray (l, h) xs
{-# INLINE iarray_getCopy #-}

iarray_putCopy :: (Ix i, SafeCopy e, SafeCopy i, IArray.IArray a e) => a i e -> Contained Encoding
iarray_putCopy arr = contain $ let (versionHeader, putIx) = getSafePut
                                   (l,h) = IArray.bounds arr
                               in    encodeListLen 3
                                  <> versionHeader <> putIx l <> putIx h
                                  <> safePut (IArray.elems arr)
{-# INLINE iarray_putCopy #-}

instance (Ix i, SafeCopy e, SafeCopy i) => SafeCopy (Array.Array i e) where
    getCopy = iarray_getCopy
    putCopy = iarray_putCopy
    errorTypeName = typeName2

instance (IArray.IArray UArray.UArray e, Ix i, SafeCopy e, SafeCopy i) => SafeCopy (UArray.UArray i e) where
    getCopy = iarray_getCopy
    putCopy = iarray_putCopy
    errorTypeName = typeName2

instance (SafeCopy a, SafeCopy b) => SafeCopy (a,b) where
    kind = primitive
    getCopy = contain $ do
      decodeListLenOf 2
      liftM2 (,) safeGet safeGet
    putCopy (a,b) = contain $ encodeListLen 2 <> safePut a <> safePut b
    errorTypeName = typeName2
instance (SafeCopy a, SafeCopy b, SafeCopy c) => SafeCopy (a,b,c) where
    kind = primitive
    getCopy = contain $ do
      decodeListLenOf 3
      liftM3 (,,) safeGet safeGet safeGet
    putCopy (a,b,c) = contain $ encodeListLen 3
                             <> safePut a <> safePut b <> safePut c
instance (SafeCopy a, SafeCopy b, SafeCopy c, SafeCopy d) => SafeCopy (a,b,c,d) where
    kind = primitive
    getCopy = contain $ do
      decodeListLenOf 4
      liftM4 (,,,) safeGet safeGet safeGet safeGet
    putCopy (a,b,c,d) = contain $ encodeListLen 4
                               <> safePut a <> safePut b <> safePut c <> safePut d
instance (SafeCopy a, SafeCopy b, SafeCopy c, SafeCopy d, SafeCopy e) =>
         SafeCopy (a,b,c,d,e) where
    kind = primitive
    getCopy = contain $ do
      decodeListLenOf 5
      liftM5 (,,,,) safeGet safeGet safeGet safeGet safeGet
    putCopy (a,b,c,d,e) = contain $ encodeListLen 5
                                 <> safePut a <> safePut b <> safePut c <> safePut d <> safePut e
instance (SafeCopy a, SafeCopy b, SafeCopy c, SafeCopy d, SafeCopy e, SafeCopy f) =>
         SafeCopy (a,b,c,d,e,f) where
    kind = primitive
    getCopy = contain $ do
      decodeListLenOf 6
      (,,,,,) <$> safeGet <*> safeGet <*> safeGet <*> safeGet <*> safeGet <*> safeGet
    putCopy (a,b,c,d,e,f) = contain $ encodeListLen 6
                                   <> safePut a <> safePut b <> safePut c <> safePut d
                                   <> safePut e <> safePut f
instance (SafeCopy a, SafeCopy b, SafeCopy c, SafeCopy d, SafeCopy e, SafeCopy f, SafeCopy g) =>
         SafeCopy (a,b,c,d,e,f,g) where
    kind = primitive
    getCopy = contain $ do
      decodeListLenOf 7
      (,,,,,,) <$> safeGet <*> safeGet <*> safeGet <*> safeGet <*>
                                     safeGet <*> safeGet <*> safeGet
    putCopy (a,b,c,d,e,f,g) = contain $ encodeListLen 7
                                     <> safePut a <> safePut b <> safePut c <> safePut d
                                     <> safePut e <> safePut f <> safePut g


instance SafeCopy Int where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Integer where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName

instance SafeCopy Float where
  kind = primitive
  getCopy = contain decode
  putCopy = contain . encode
  errorTypeName = typeName

instance SafeCopy Double where
  kind = primitive
  getCopy = contain decode
  putCopy = contain . encode
  errorTypeName = typeName

instance SafeCopy L.ByteString where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy B.ByteString where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Char where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Word where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Word8 where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Word16 where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Word32 where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Word64 where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Ordering where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Int8 where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Int16 where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Int32 where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Int64 where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance (Integral a, Serialise a) => SafeCopy (Ratio a) where
    kind = primitive
    getCopy = contain decode
    putCopy = contain . encode
    errorTypeName = typeName1
instance (HasResolution a, Fractional (Fixed a)) => SafeCopy (Fixed a) where
    kind = primitive
    getCopy   = contain decode
    putCopy   = contain . encode
    errorTypeName = typeName1

instance SafeCopy () where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance SafeCopy Bool where
    kind = primitive
    getCopy = contain decode; putCopy = contain . encode; errorTypeName = typeName
instance (SafeCopy a, SafeCopy b) => SafeCopy (Either a b) where
    getCopy = contain $ do decodeListLenOf 2
                           t <- decodeWord
                           case t of
                             0 -> do !x <- safeGet
                                     return (Left x)
                             1 -> do !x <- safeGet
                                     return (Right x)
                             _ -> fail "unknown tag"

    putCopy (Left  a) = contain $ encodeListLen 2 <> encodeWord 0 <> safePut a
    putCopy (Right a) = contain $ encodeListLen 2 <> encodeWord 1 <> safePut a

    errorTypeName = typeName2

--  instances for 'text' library

instance SafeCopy T.Text where
    kind = primitive
    getCopy = contain decode
    putCopy = contain . encode
    errorTypeName = typeName

instance SafeCopy TL.Text where
    kind = primitive
    getCopy = contain decode
    putCopy = contain . encode
    errorTypeName = typeName

-- instances for 'time' library

instance SafeCopy Day where
    kind = base
    getCopy = contain $ ModifiedJulianDay <$> safeGet
    putCopy = contain . safePut . toModifiedJulianDay
    errorTypeName = typeName

instance SafeCopy DiffTime where
    kind = base
    getCopy = contain $ fromRational <$> safeGet
    putCopy = contain . safePut . toRational
    errorTypeName = typeName

instance SafeCopy UniversalTime where
    kind = base
    getCopy = contain $ ModJulianDate <$> safeGet
    putCopy = contain . safePut . getModJulianDate
    errorTypeName = typeName

instance SafeCopy UTCTime where
    kind = base
    getCopy = contain decode
    putCopy = contain . encode
    errorTypeName = typeName

instance SafeCopy NominalDiffTime where
    kind = base
    getCopy = contain $ fromRational <$> safeGet
    putCopy = contain . safePut . toRational
    errorTypeName = typeName

instance SafeCopy TimeOfDay where
    kind = base
    getCopy   = contain $ do hour <- safeGet
                             mins <- safeGet
                             sec  <- safeGet
                             return (TimeOfDay hour mins sec)
    putCopy t = contain $    safePut (todHour t)
                          <> safePut (todMin t)
                          <> safePut (todSec t)
    errorTypeName = typeName

instance SafeCopy TimeZone where
    kind = base
    getCopy   = contain $ do mins       <- safeGet
                             summerOnly <- safeGet
                             zoneName   <- safeGet
                             return (TimeZone mins summerOnly zoneName)
    putCopy t = contain $    safePut (timeZoneMinutes t)
                          <> safePut (timeZoneSummerOnly t)
                          <> safePut (timeZoneName t)
    errorTypeName = typeName

instance SafeCopy LocalTime where
    kind = base
    getCopy   = contain $ do day <- safeGet
                             tod <- safeGet
                             return (LocalTime day tod)
    putCopy t = contain $    safePut (localDay t)
                          <> safePut (localTimeOfDay t)
    errorTypeName = typeName

instance SafeCopy ZonedTime where
    kind = base
    getCopy   = contain $ do localTime <- safeGet
                             timeZone  <- safeGet
                             return (ZonedTime localTime timeZone)
    putCopy t = contain $    safePut (zonedTimeToLocalTime t)
                          <> safePut (zonedTimeZone t)
    errorTypeName = typeName

instance SafeCopy AbsoluteTime where
  getCopy = contain $ liftM toAbsoluteTime safeGet
    where
      toAbsoluteTime :: DiffTime -> AbsoluteTime
      toAbsoluteTime dt = addAbsoluteTime dt taiEpoch
  putCopy = contain . safePut . fromAbsoluteTime
    where
      fromAbsoluteTime :: AbsoluteTime -> DiffTime
      fromAbsoluteTime at = diffAbsoluteTime at taiEpoch
  errorTypeName = typeName

-- instances for old-time

instance SafeCopy ClockTime where
    kind = base
    getCopy = contain $ do secs <- safeGet
                           pico <- safeGet
                           return (TOD secs pico)
    putCopy (TOD secs pico) =
              contain $    safePut secs
                        <> safePut pico

instance SafeCopy TimeDiff where
    kind = base
    getCopy   = contain $ do year    <- decode
                             month   <- decode
                             day     <- decode
                             hour    <- decode
                             mins    <- decode
                             sec     <- decode
                             pico    <- decode
                             return (TimeDiff year month day hour mins sec pico)
    putCopy t = contain $    encode (tdYear t)
                          <> encode (tdMonth t)
                          <> encode (tdDay t)
                          <> encode (tdHour t)
                          <> encode (tdMin t)
                          <> encode (tdSec t)
                          <> encode (tdPicosec t)

instance SafeCopy OT.Day where
    kind = base ; getCopy = contain $ toEnum <$> decode ; putCopy = contain . encode . fromEnum

instance SafeCopy Month where
    kind = base ; getCopy = contain $ toEnum <$> decode ; putCopy = contain . encode . fromEnum


instance SafeCopy CalendarTime where
    kind = base
    getCopy   = contain $ do year   <- decode
                             month  <- safeGet
                             day    <- decode
                             hour   <- decode
                             mins   <- decode
                             sec    <- decode
                             pico   <- decode
                             wday   <- safeGet
                             yday   <- decode
                             tzname <- safeGet
                             tz     <- decode
                             dst    <- decode
                             return (CalendarTime year month day hour mins sec pico wday yday tzname tz dst)
    putCopy t = contain $    encode  (ctYear t)
                          <> safePut (ctMonth t)
                          <> encode  (ctDay t)
                          <> encode  (ctHour t)
                          <> encode  (ctMin t)
                          <> encode  (ctSec t)
                          <> encode  (ctPicosec t)
                          <> safePut (ctWDay t)
                          <> encode  (ctYDay t)
                          <> safePut (ctTZName t)
                          <> encode  (ctTZ t)
                          <> encode  (ctIsDST t)

typeName :: Typeable a => Proxy a -> String
typeName proxy = show (typeOf (undefined `asProxyType` proxy))

#if MIN_VERSION_base(4,10,0)
typeName1 :: (Typeable c) => Proxy (c a) -> String
typeName2 :: (Typeable c) => Proxy (c a b) -> String
#else
typeName1 :: (Typeable1 c) => Proxy (c a) -> String
typeName2 :: (Typeable2 c) => Proxy (c a b) -> String
#endif

typeName1 proxy = show (typeOf1 (undefined `asProxyType` proxy))
typeName2 proxy = show (typeOf2 (undefined `asProxyType` proxy))

encodeContainerSkel :: (Word -> Encoding)
                    -> (container -> Int)
                    -> (accumFunc -> Encoding -> container -> Encoding)
                    -> accumFunc
                    -> Encoding
                    -> container
                    -> Encoding
encodeContainerSkel encodeLen size foldr' f v c =
    v <> encodeLen (fromIntegral (size c)) <> foldr' f mempty c
{-# INLINE encodeContainerSkel #-}

decodeContainerSkelWithReplicate
  :: (SafeCopy a)
  => Decoder s Int
     -- ^ How to get the size of the container
  -> (Int -> Decoder s a -> Decoder s container)
     -- ^ replicateM for the container
  -> ([container] -> container)
     -- ^ concat for the container
  -> Decoder s container
decodeContainerSkelWithReplicate decodeLen replicateFun fromList = do
    -- Look at how much data we have at the moment and use it as the limit for
    -- the size of a single call to replicateFun. We don't want to use
    -- replicateFun directly on the result of decodeLen since this might lead to
    -- DOS attack (attacker providing a huge value for length). So if it's above
    -- our limit, we'll do manual chunking and then combine the containers into
    -- one.
    getter <- getSafeGet
    size <- decodeLen
    limit <- peekAvailable
    if size <= limit
       then replicateFun size getter
       else do
           -- Take the max of limit and a fixed chunk size (note: limit can be
           -- 0). This basically means that the attacker can make us allocate a
           -- container of size 128 even though there's no actual input.
           let chunkSize = max limit 128
               (d, m) = size `divMod` chunkSize
               buildOne s = replicateFun s getter
           containers <- sequence $ buildOne m : replicate d (buildOne chunkSize)
           return $! fromList containers
{-# INLINE decodeContainerSkelWithReplicate #-}

getGenericVector :: (SafeCopy a, VG.Vector v a) => (Decoder s (v a))
getGenericVector = 
  decodeContainerSkelWithReplicate
    decodeListLen
    VG.replicateM
    VG.concat
{-# INLINE getGenericVector #-}

putGenericVector :: (SafeCopy a, VG.Vector v a) => v a -> Encoding
putGenericVector =
  encodeContainerSkel
    encodeListLen
    VG.length
    VG.foldr
    (\a b -> putter a <> b)
    versionHeader
  where
    (versionHeader, putter) = getSafePut
{-# INLINE putGenericVector #-}

instance SafeCopy a => SafeCopy (V.Vector a) where
    kind = primitive
    getCopy = contain getGenericVector
    putCopy = contain . putGenericVector

instance (SafeCopy a, VP.Prim a) => SafeCopy (VP.Vector a) where
    kind = primitive
    getCopy = contain getGenericVector
    putCopy = contain . putGenericVector

instance (SafeCopy a, VS.Storable a) => SafeCopy (VS.Vector a) where
    kind = primitive
    getCopy = contain getGenericVector
    putCopy = contain . putGenericVector

instance (SafeCopy a, VU.Unbox a) => SafeCopy (VU.Vector a) where
    kind = primitive
    getCopy = contain getGenericVector
    putCopy = contain . putGenericVector
