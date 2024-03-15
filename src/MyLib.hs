{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DuplicateRecordFields #-}
module MyLib where

import Data.Word
import Data.IORef
import GHC.Data.FastMutInt
import Foreign hiding (void)
import System.IO.Unsafe
import Control.Monad
import GHC.ForeignPtr
import System.IO.Error
import System.IO
import qualified Data.Dependent.Map as DMap
import Control.Applicative
import qualified Data.ByteString.Internal as BI
import qualified Data.ByteString.Unsafe as BI
import qualified Data.ByteString as B
import Data.Proxy
import Data.GADT.Compare
import Data.Functor
import Data.Char
import Data.GADT.Compare.TH
import Data.Type.Equality
import Data.Array
import qualified Data.Dependent.Sum as DMap
import Data.List
import Data.Ord

data TAG a where
  FS :: FastString -> TAG FastString
  N :: Name -> TAG Name
  IFR :: IfTyConInfo -> TAG IfTyConInfo

data SingTag a where
  FS_SING :: SingTag FastString
  FS_NAME :: SingTag Name
  FS_IFR  :: SingTag IfTyConInfo

type family Sing f where
  Sing TAG = SingTag


untag :: TAG a -> a
untag (FS f) = f
untag (N n) = n
untag (IFR i) = i

newtype FastString = FastString String deriving (Eq, Ord, Show)
data Name = Name FastString Int deriving (Eq, Ord, Show)

data IfTyConInfo = IfTyConInfo Int Int deriving (Eq, Ord, Show)

data GetKey (f :: * -> *) (a :: *) where
  GetKey :: Sing f a -> Int -> GetKey f a

instance GEq (Sing f) => GEq (GetKey f) where
  geq (GetKey s1 i) (GetKey s2 i2) =
    case geq s1 s2 of
      Just Refl -> if i == i2 then Just Refl else Nothing
      Nothing -> Nothing

instance GCompare (Sing f) => GCompare (GetKey f) where
  gcompare g1@(GetKey s1 i) g2@(GetKey s2 i2) =
    case geq g1 g2 of
      Just Refl -> GEQ
      Nothing ->
        if i < i2 then GLT
                  else GGT



deriveGEq ''TAG
deriveGCompare ''TAG

deriveGEq ''SingTag
deriveGCompare ''SingTag

instance Binary TAG FastString where
  get h = untag <$> getShared h FS_SING
  put h fs = putShared h (FS fs)

instance Binary TAG Name where
  get h = untag <$> getShared h FS_NAME
  put h n = putShared h (N n)

instance Binary TAG IfTyConInfo where
  get h = untag <$> getShared h FS_IFR
  put h n = putShared h (IFR n)

instance Binary TAG (TAG Name) where
  get h = (\x y -> N (Name x y)) <$> get h <*> get h
  put h (N (Name f n)) = do
    put h f
    put h n

instance Binary TAG (TAG FastString) where
  get h = FS . FastString <$> get h
  put h (FS (FastString f)) = put h f

instance Binary TAG (TAG IfTyConInfo) where
  get h = (\x y -> IFR (IfTyConInfo x y)) <$> get h <*> get h
  put h (IFR (IfTyConInfo x1 x2)) = put h x1 >> put h x2

encode_bs :: Binary TAG a => a -> B.ByteString
encode_bs a = unsafePerformIO $ do
  rh <- openBinMem (1024*1024)
  h <- initShared @TAG rh
  forwardPut rh (const (put_dictionary h)) $ do
    put h a
  toByteString rh

decode_bs :: Binary TAG a => B.ByteString -> a
decode_bs b = unsafePerformIO $ do
  h <- fromByteString b
  dict <- forwardGet h (getDictionary h)
  l <- newFastMutInt 0
  get_map <- newIORef DMap.empty
  let hf = H_READ @TAG h dict get_map
  get hf

share :: Binary TAG a => a -> a
share = decode_bs . encode_bs


encode :: Binary TAG a => FilePath -> a -> IO ()
encode fp a = do
  rh <- openBinMem (1024*1024)
  h <- initShared @TAG rh
  forwardPut rh (const (put_dictionary h)) $ do
    put h a
  writeBinMem rh fp

put_dictionary :: H_WRITE f -> IO ()
put_dictionary h = do
  n <- readFastMutInt (shared_count h)
  buff <- readIORef (shared h)
  putDictionary (raw_write h) n buff

putDictionary :: RH -> Int -> DMap.DMap f (Payload f) -> IO ()
putDictionary rh n shared_rh = do
  putWord32 rh (fromIntegral n)
  -- The map will contain all keys from 0..n
  let vs = sortBy (comparing fst) [ (n, b) | _ DMap.:=> (Payload n _ b)  <- DMap.assocs shared_rh ]
  mapM_ (putBS rh . snd) vs

putBS :: RH -> B.ByteString -> IO ()
putBS bh bs =
  BI.unsafeUseAsCStringLen bs $ \(ptr, l) -> do
  putWord32 bh (fromIntegral l)
  putPrim bh l (\op -> copyBytes op (castPtr ptr) l)

getBS :: RH -> IO B.ByteString
getBS bh = do
  l <- getWord32 bh :: IO Word32
  BI.create (fromIntegral l) $ \dest -> do
    getPrim bh (fromIntegral l) (\src -> copyBytes dest src (fromIntegral l))


getDictionary :: RH -> IO (Array Int B.ByteString)
getDictionary rh = do
  n <- getWord32 rh
  bs <- replicateM (fromIntegral n) (getBS rh)
  return $ listArray (0, fromIntegral n) bs



decode :: Binary TAG a => FilePath -> IO a
decode fp = do
  h <- readBinMem fp
  dict <- forwardGet h (getDictionary h)
  l <- newFastMutInt 0
  get_map <- newIORef DMap.empty
  let hf = H_READ @TAG h dict get_map
  get hf

readBinMem_ :: Int -> Handle -> IO RH
readBinMem_ filesize h = do
  arr <- mallocForeignPtrBytes filesize
  count <- unsafeWithForeignPtr arr $ \p -> hGetBuf h p filesize
  when (count /= filesize) $
       error ("Binary.readBinMem: only read " ++ show count ++ " bytes")
  arr_r <- newIORef arr
  ix_r <- newFastMutInt 0
  sz_r <- newFastMutInt filesize
  let rh = (RH ix_r sz_r arr_r )
  bs <- toByteString rh
  return rh

initShared :: RH -> IO (H_WRITE f)
initShared rh = do
  H_WRITE <$> pure rh <*> newFastMutInt 0 <*> newIORef (DMap.empty)

type BinArray = ForeignPtr Word8

openBinMem :: Int -> IO RH
openBinMem size
 | size <= 0 = error "GHC.Utils.Binary.openBinMem: size must be >= 0"
 | otherwise = do
   arr <- mallocForeignPtrBytes size
   arr_r <- newIORef arr
   ix_r <- newFastMutInt 0
   sz_r <- newFastMutInt size
   return (RH ix_r sz_r arr_r)

writeBinMem :: RH -> FilePath -> IO ()
writeBinMem (RH ix_r _ arr_r) fn = do
  h <- openBinaryFile fn WriteMode
  arr <- readIORef arr_r
  ix  <- readFastMutInt ix_r
  unsafeWithForeignPtr arr $ \p -> hPutBuf h p ix
  hClose h

readBinMem :: FilePath -> IO RH
readBinMem filename = do
  withBinaryFile filename ReadMode $ \h -> do
    filesize' <- hFileSize h
    let filesize = fromIntegral filesize'
    rh <- readBinMem_ filesize h
    return rh

-- -----------------------------------------------------------------------------
-- Forward reading/writing

-- | "forwardPut put_A put_B" outputs A after B but allows A to be read before B
-- by using a forward reference
forwardPut :: RH -> (b -> IO a) -> IO b -> IO (a,b)
forwardPut bh put_A put_B = do
  -- write placeholder pointer to A
  pre_a <- tellBin bh
  putBin bh pre_a

  -- write B
  r_b <- put_B

  -- update A's pointer
  a <- tellBin bh
  putAt bh pre_a putBin a
  seekBinNoExpand bh a

  -- write A
  r_a <- put_A r_b
  pure (r_a,r_b)

forwardPut_ :: RH -> (b -> IO a) -> IO b -> IO ()
forwardPut_ bh put_A put_B = void $ forwardPut bh put_A put_B

putAt  :: RH -> Bin (Bin a) -> (RH -> Bin a -> IO ()) -> Bin a -> IO ()
putAt bh p f x = do seekBin bh p; f bh x; return ()


newtype Bin a = BinPtr Int
  deriving (Eq, Ord, Show, Bounded)

putBin :: RH -> Bin a -> IO ()
putBin rh (BinPtr i) =  putWord32 rh (fromIntegral i :: Word32)

getBin rh = do i <- getWord32 rh; return (BinPtr (fromIntegral (i :: Word32)))

-- | Read a value stored using a forward reference
forwardGet :: RH -> IO a -> IO a
forwardGet bh get_A = do
    -- read forward reference
    p <- getBin bh -- a BinPtr
    -- store current position
    p_a <- tellBin bh
    -- go read the forward value, then seek back
    seekBinNoExpand bh p
    r <- get_A
    seekBinNoExpand bh p_a
    pure r

tellBin :: RH -> IO (Bin a)
tellBin (RH r _ _) = do ix <- readFastMutInt r; return (BinPtr ix)

seekBin :: RH -> Bin a -> IO ()
seekBin h@(RH ix_r sz_r _) (BinPtr !p) = do
  sz <- readFastMutInt sz_r
  if (p >= sz)
        then do expandBin h p; writeFastMutInt ix_r p
        else writeFastMutInt ix_r p

-- | SeekBin but without calling expandBin
seekBinNoExpand :: RH -> Bin a -> IO ()
seekBinNoExpand (RH ix_r sz_r _) (BinPtr !p) = do
  sz <- readFastMutInt sz_r
  if (p >= sz)
        then error "seekBinNoExpand: seek out of range"
        else writeFastMutInt ix_r p



data Payload f a = Payload Word32 -- n
                           (Proxy a) -- The type
                           B.ByteString -- The serialised key


instance Functor f => Functor (Payload f) where
  fmap f (Payload n a b) = Payload n (f <$> a) b


data RH
  = RH  { _off_r :: !FastMutInt,      -- the current offset
         _sz_r  :: !FastMutInt,      -- size of the array (cached)
         _arr_r :: !(IORef BinArray) -- the array (bounds: (0,size-1))
         }

getCurrentOffset :: RH -> IO Int
getCurrentOffset (RH off _ _) = readFastMutInt off


data H_READ f = H_READ {
         raw_read :: RH,
         shared_buffer :: (Array Int B.ByteString), -- A list of keys, only used for deserialising
         shared_get :: (IORef (DMap.DMap (GetKey f) f)) -- A map from offsets to decoded keys
       }


data H_WRITE f = H_WRITE {
    raw_write :: RH
  , shared_count :: FastMutInt
  , shared :: (IORef (DMap.DMap f (Payload f))) -- A map of shared values
}

toByteString :: RH -> IO B.ByteString
toByteString (RH ix _ binr) = BI.BS <$> readIORef binr <*> readFastMutInt ix

fromByteString :: B.ByteString -> IO RH
fromByteString (BI.BS p l) = do
  cont <- newIORef p
  len <- newFastMutInt l
  off <- newFastMutInt 0
  return (RH off len cont)




class Binary f a where
  put :: H_WRITE f -> a -> IO ()
  get :: H_READ f -> IO a

instance Binary f () where
  put _ () = return ()
  get _ = return ()

instance Binary f Word8 where
  put h = putWord8 (raw_write h)
  get h = getWord8 (raw_read h)

instance Binary f Char where
     put  bh c = putWord32 (raw_write bh) (fromIntegral (ord c) :: Word32)
     get  bh   = do x <- getWord32 (raw_read bh); return $! (chr (fromIntegral (x :: Word32)))

instance Binary f a => Binary f [a] where
    put bh l = do
        let len :: Int
            len = length l
        put bh len
        mapM_ (put bh) l
    get bh = do
        len <- get bh :: IO Int -- Int is variable length encoded so only
                                -- one byte for small lists.
        let loop 0 = return []
            loop n = do a <- get bh; as <- loop (n-1); return (a:as)
        loop len

instance Binary f Int where
  get h = getSLEB128 (raw_read h)
  put h = putSLEB128 (raw_write h)



{-# SPECIALISE getSLEB128 :: RH -> IO Word #-}
{-# SPECIALISE getSLEB128 :: RH -> IO Word64 #-}
{-# SPECIALISE getSLEB128 :: RH -> IO Word32 #-}
{-# SPECIALISE getSLEB128 :: RH -> IO Word16 #-}
{-# SPECIALISE getSLEB128 :: RH -> IO Int #-}
{-# SPECIALISE getSLEB128 :: RH -> IO Int64 #-}
{-# SPECIALISE getSLEB128 :: RH -> IO Int32 #-}
{-# SPECIALISE getSLEB128 :: RH -> IO Int16 #-}
getSLEB128 :: forall a . (Show a, Integral a, FiniteBits a) => RH -> IO a
getSLEB128 bh = do
    (val,shift,signed) <- go 0 0
    if signed && (shift < finiteBitSize val )
        then return $! ((complement 0 `unsafeShiftL` shift) .|. val)
        else return val
    where
        go :: Int -> a -> IO (a,Int,Bool)
        go shift val = do
            byte <- getWord8 bh
            let !byteVal = fromIntegral (clearBit byte 7) :: a
            let !val' = val .|. (byteVal `unsafeShiftL` shift)
            let !more = testBit byte 7
            let !shift' = shift+7
            if more
                then go (shift') val'
                else do
                    let !signed = testBit byte 6
                    return (val',shift',signed)

{-# SPECIALISE putSLEB128 :: RH -> Word -> IO () #-}
{-# SPECIALISE putSLEB128 :: RH -> Word64 -> IO () #-}
{-# SPECIALISE putSLEB128 :: RH -> Word32 -> IO () #-}
{-# SPECIALISE putSLEB128 :: RH -> Word16 -> IO () #-}
{-# SPECIALISE putSLEB128 :: RH -> Int -> IO () #-}
{-# SPECIALISE putSLEB128 :: RH -> Int64 -> IO () #-}
{-# SPECIALISE putSLEB128 :: RH -> Int32 -> IO () #-}
{-# SPECIALISE putSLEB128 :: RH -> Int16 -> IO () #-}
putSLEB128 :: forall a . (Integral a, Bits a) => RH -> a -> IO ()
putSLEB128 bh initial = go initial
  where
    go :: a -> IO ()
    go val = do
        let !byte = fromIntegral (clearBit val 7) :: Word8
        let !val' = val `unsafeShiftR` 7
        let !signBit = testBit byte 6
        let !done =
                -- Unsigned value, val' == 0 and last value can
                -- be discriminated from a negative number.
                ((val' == 0 && not signBit) ||
                -- Signed value,
                 (val' == -1 && signBit))

        let !byte' = if done then byte else setBit byte 7
        putWord8 bh byte'

        unless done $ go val'

putByte :: H_WRITE f -> Word8 -> IO ()
putByte bh !w = putWord8 (raw_write bh) w

getByte :: H_READ f -> IO Word8
getByte h = getWord8 (raw_read h)




putShared :: (GCompare f, Binary f (f a)) => H_WRITE f -> f a -> IO ()
putShared h key = do
  shared_cache <- readIORef (shared h)
  case DMap.lookup key shared_cache of
    (Just (Payload n _ _)) -> putSLEB128 (raw_write h) n
    Nothing -> do
      n <- readFastMutInt (shared_count h)
      writeFastMutInt (shared_count h) (n + 1)

      rh' <- openBinMem 10
      let h' = h { raw_write = rh' }
      put h' key
      key_payload <- toByteString rh'

      let payload = Payload (fromIntegral n) Proxy key_payload
      modifyIORef (shared h) (DMap.insert key payload)
      putSLEB128 (raw_write h) n


getShared :: forall f a . (Binary f (f a), GCompare (GetKey f)) => H_READ f -> Sing f a -> IO (f a)
getShared h key = do
  -- 1. Get the offset into shared buffer
  n <- getSLEB128 @Word32 (raw_read h)
  -- 2. Lookup to see if we already decode that offset (to avoid reallocating)
  shared_cache <- readIORef (shared_get h)
  case DMap.lookup (GetKey @f @a key (fromIntegral n)) shared_cache of
    -- Not seen before, read from shared buffer.
    Nothing -> do
      let bs = (shared_buffer h) ! (fromIntegral n)
      rh' <- fromByteString bs
      v <- get @f @(f a) (h { raw_read = rh' })
      modifyIORef (shared_get h) (DMap.insert (GetKey @f @a key (fromIntegral n)) v)
      return v
    Just v -> do
      return v


getPrim :: RH -> Int -> (Ptr Word8 -> IO a) -> IO a
getPrim (RH ix_r sz_r arr_r) size f = do
  ix <- readFastMutInt ix_r
  sz <- readFastMutInt sz_r
  when (ix + size > sz) $
      ioError (mkIOError eofErrorType "Data.Binary.getPrim" Nothing Nothing)
  arr <- readIORef arr_r
  w <- unsafeWithForeignPtr arr $ \p -> f (p `plusPtr` ix)
    -- This is safe WRT #17760 as we we guarantee that the above line doesn't
    -- diverge
  writeFastMutInt ix_r (ix + size)
  return w

putPrim :: RH -> Int -> (Ptr Word8 -> IO ()) -> IO ()
putPrim h@(RH ix_r sz_r arr_r) size f = do
  ix <- readFastMutInt ix_r
  sz <- readFastMutInt sz_r
  when (ix + size > sz) $
    expandBin h (ix + size)
  arr <- readIORef arr_r
  unsafeWithForeignPtr arr $ \op -> f (op `plusPtr` ix)
  writeFastMutInt ix_r (ix + size)


-- expand the size of the array to include a specified offset
expandBin :: RH -> Int -> IO ()
expandBin (RH _ sz_r arr_r) !off = do
   !sz <- readFastMutInt sz_r
   let !sz' = getSize sz
   arr <- readIORef arr_r
   arr' <- mallocForeignPtrBytes sz'
   withForeignPtr arr $ \old ->
     withForeignPtr arr' $ \new ->
       copyBytes new old sz
   writeFastMutInt sz_r sz'
   writeIORef arr_r arr'
   where
    getSize :: Int -> Int
    getSize !sz
      | sz > off
      = sz
      | otherwise
      = getSize (sz * 2)


putWord8 :: RH -> Word8 -> IO ()
putWord8 h !w = putPrim h 1 (\op -> poke op w)

getWord8 :: RH -> IO Word8
getWord8 h = getPrim h 1 peek

putWord32 :: RH -> Word32 -> IO ()
putWord32 h w = putPrim h 4 (\op -> do
  pokeElemOff op 0 (fromIntegral (w `shiftR` 24))
  pokeElemOff op 1 (fromIntegral ((w `shiftR` 16) .&. 0xFF))
  pokeElemOff op 2 (fromIntegral ((w `shiftR` 8) .&. 0xFF))
  pokeElemOff op 3 (fromIntegral (w .&. 0xFF))
  )

getWord32 :: RH -> IO Word32
getWord32 h = getPrim h 4 (\op -> do
  w0 <- fromIntegral <$> peekElemOff op 0
  w1 <- fromIntegral <$> peekElemOff op 1
  w2 <- fromIntegral <$> peekElemOff op 2
  w3 <- fromIntegral <$> peekElemOff op 3

  return $! (w0 `shiftL` 24) .|.
            (w1 `shiftL` 16) .|.
            (w2 `shiftL` 8)  .|.
            w3
  )


