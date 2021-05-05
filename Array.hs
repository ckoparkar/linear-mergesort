{-# LANGUAGE LinearTypes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE UnboxedTuples       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE InstanceSigs        #-}

module Array
    ( Array(..), showMArray#, Range(..), showRange
    , size, fromList, toList, alloc, slice, splitAt, merge
    , unsafeGet, unsafeSet, unsafeAlias, unsafeSplitAt
    ) where

import           Prelude.Linear ( (&) )
import           Data.Unrestricted.Linear
import qualified Unsafe.Linear as Unsafe
import qualified GHC.Exts as GHC
import           Prelude hiding ( splitAt )

--------------------------------------------------------------------------------
-- An Arrays API
--------------------------------------------------------------------------------

{-
  See Ed Kmett's comments here:

  [1]: https://github.com/tweag/linear-base/issues/312
  [2]: https://github.com/ekmett/linear-haskell/blob/6f9e5c0e96d0c99d064ae027086db48c4fcfc63c/linear-keys/src/Linear/Range.hs
-}

type MArray# a = GHC.MutableArray# GHC.RealWorld a

data Array a = Array (MArray# a)

showMArray# :: Show a => MArray# a -> String
showMArray# arr = do
  let sz = GHC.sizeofMutableArray# arr
      ls = go 0 (GHC.I# sz) arr
  show ls
  where
   go :: Int -> Int -> MArray# a -> [a]
   go i len arr
    | i == len = []
    | GHC.I# i# <- i =
        case GHC.runRW# (GHC.readArray# arr i#) of
          (# _, ret #) -> ret : go (i+1) len arr

showRange :: Show a => Range s a %1-> String
showRange (Range l u arr) =
    "Range{l=" ++ show l ++ ",u=" ++ show u ++ ",arr=" ++ show (go l u arr) ++ "}"
  where
   go :: Int -> Int -> MArray# a -> [a]
   go i len arr
    | i == len = []
    | GHC.I# i# <- i =
        case GHC.runRW# (GHC.readArray# arr i#) of
          (# _, ret #) -> ret : go (i+1) len arr

instance Consumable (Array a) where
    consume :: Array a %1-> ()
    consume (Array arr) = arr `lseq#` ()

data Range s a where
    Range :: Int        {- lower bound -}
          -> Int        {- uppper bound -}
          -> MArray# a  {- underlying array -}
          -> Range s a

instance Show a => Show (Range s a) where
    show r = Unsafe.toLinear showRange r

instance Consumable (Range s a) where
    consume :: Range s a %1-> ()
    consume (Range _ _ arr) = arr `lseq#` ()

lseq# :: MArray# a %1-> b %1-> b
lseq# = Unsafe.toLinear2 (\_ b -> b)

size :: Range s a %1 -> (Ur Int, Range s a)
size (Range l u a) = (Ur (u-l), Range l u a)

{- https://hackage.haskell.org/package/linear-base-0.1.0/docs/src/Data.Array.Mutable.Linear.html#fromList -}
fromList :: forall a b. [a] -> (forall s. Range s a %1-> Ur b) %1 -> Ur b
fromList list f =
  alloc
    (length list)
    (error "invariant violation: unintialized array position")
    (\arr -> f (insert arr))
 where
  insert :: Range s a %1-> Range s a
  insert = doWrites (zip list [0..])

  doWrites :: [(a,Int)] -> Range s a %1-> Range s a
  doWrites [] arr = arr
  doWrites ((a,ix):xs) arr = doWrites xs (unsafeSet ix a arr)


{- https://hackage.haskell.org/package/linear-base-0.1.0/docs/src/Data.Array.Mutable.Unlifted.Linear.html#toList -}
toList :: Range s a %1-> Ur [a]
toList (Range l u arr0) = Ur (go l u arr0)
 where
  go i len arr
    | i == len = []
    | GHC.I# i# <- i =
        case GHC.runRW# (GHC.readArray# arr i#) of
          (# _, ret #) -> ret : go (i+1) len arr

{- https://hackage.haskell.org/package/linear-base-0.1.0/docs/src/Data.Array.Mutable.Unlifted.Linear.html#alloc -}
alloc :: Int -> a -> (forall s. Range s a %1-> Ur b) %1 -> Ur b
alloc (GHC.I# len) a f =
  let new = GHC.runRW# Prelude.$ \st ->
        case GHC.newArray# len a st of
          (# _, arr #) -> Range 0 (GHC.I# len) arr
   in f new
{-# NOINLINE alloc #-}  -- prevents runRW# from floating outwards

-- | 'slice' is not O(1), it copies elements. So this splitAt is quite expensive :(
splitAt :: Show a => Int -> Range s a %1-> ((Ur Int,Range s a),(Ur Int,Range s a))
splitAt n arr0 = unsafeSplitAt n n arr0

merge :: Range s a %1-> Range s a %1-> Range s a
merge (Range l1 u1 a) (Range l2 u2 _) =
    Range l1 u2 a
    -- if u1 == l2
    -- then Range l1 u2 a
    -- else error $ "merge: non-contiguous slices: " ++ show (l1,u1) ++ " " ++ show (l2,u2)

-- | Unsafe because it aliases the input slice.
slice :: forall s a. Int -> Int -> Range s a %1-> Range s a
slice i n (Range l0 u0 arr0) = Unsafe.coerce go
  where
    go :: Range s a
    go =
        let l1 = l0 + i
            u1 = l0 + i + n
        in if l1 > u0
           then error ("slice: lower out of bounds, " ++ show (l1,u0))
           else if u1 > u0
                then error ("slice: upper out of bounds, " ++ show (u1,u0))
                else (Range l1 u1 arr0)

--------------------------------------------------------------------------------
-- Unsafe operations
--------------------------------------------------------------------------------

-- | Unsafe because there's no bounds-checking, but OK wrt linearity.
unsafeGet :: forall s a. Int -> Range s a %1-> (Ur a, Range s a)
unsafeGet (GHC.I# i) (Range (GHC.I# l) u arr0) = Unsafe.coerce go arr0
  where
    go :: MArray# a -> (Ur a, Range s a)
    go arr =
      case GHC.runRW# (GHC.readArray# arr (l GHC.+# i)) of
        (# _, ret #) -> (Ur ret, Range (GHC.I# l) u arr)
{-# NOINLINE unsafeGet #-}  -- prevents the runRW# effect from being reordered

-- | Unsafe because there's no bounds-checking, but OK wrt linearity.
unsafeSet :: forall s a. Int -> a -> Range s a %1-> Range s a
unsafeSet (GHC.I# i) val (Range (GHC.I# l) u arr0) = Unsafe.toLinear go arr0
  where
    go :: MArray# a -> Range s a
    go arr =
      case GHC.runRW# (GHC.writeArray# arr (l GHC.+# i) val) of
        _ -> Range (GHC.I# l) u arr
{-# NOINLINE unsafeSet #-}  -- prevents the runRW# effect from being reordered

-- | Unsafe because it aliases the input slice.
unsafeAlias :: Range s a %1 -> (Range s a, Range s a)
unsafeAlias x = Unsafe.toLinear (\a -> (a, a)) x

-- | Unsafe because it allows non-contiguous slices.
unsafeSplitAt :: Show a => Int -> Int -> Range s a %1-> ((Ur Int,Range s a),(Ur Int,Range s a))
unsafeSplitAt n m arr0 =
    if m < n
    then arr0 `lseq` error $ "unsafeSplitAt: m < n, " ++ show (m,n)
    else size arr0 &
             \(Ur len, arr1) ->
                 go len arr1
  where
    go len arr1 =
        unsafeAlias arr1 &
                \(arr2,arr3) ->
                    slice 0 n' arr2 &
                        \sl1 ->
                            slice x x' arr3 &
                                \sl2 ->
                                    ((Ur n',sl1), (Ur x',sl2))
        where
          n'  = max n 0
          x   = min m len
          x'  = max 0 (len - m)
