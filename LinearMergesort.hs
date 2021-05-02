{-# LANGUAGE LinearTypes         #-}
{-# LANGUAGE ScopedTypeVariables #-}

module LinearMergesort where

import           Prelude hiding ( splitAt )
import           Prelude.Linear                   ( lseq, (&) )
import           Data.Unrestricted.Internal.Ur    ( Ur(..), unur )
import qualified Data.Array.Mutable.Linear as Arr
import qualified Unsafe.Linear as Unsafe

import Debug.Trace

--------------------------------------------------------------------------------
-- Sorting
--------------------------------------------------------------------------------

mergeSort :: forall a. Show a => a -> (a -> a -> Int) -> Array2 a %1-> Ur (Array2 a)
mergeSort init cmp src0 =
    size2 src0 &
        \(Ur len, src1) ->
            alloc2 len init (\tmp -> go src1 tmp)
  where
    go :: Show a => Array2 a %1-> Array2 a %1-> Ur (Array2 a)
    go src tmp =
        writeSort1 cmp src tmp &
            (Unsafe.toLinear Ur)

-- | Sort the left and right halves of 'src' into 'tmp', and merge the results
-- back into 'src'.
writeSort1 :: Show a => (a -> a -> Int) -> Array2 a %1-> Array2 a %1-> Array2 a
writeSort1 cmp src0 tmp =
    {- INVARIANT: length src0 == length tmp -}
    size2 src0 &
        \(Ur len, src) ->
            if len <= 1
            then tmp `lseq` src
            else splitAt (len `div` 2) src &
                     \((Ur _n1,src_l),(Ur _n2,src_r),src1) ->
                         splitAt (len `div` 2) tmp &
                             {- INVARIANT: n1 == n3, and n2 == n4 -}
                             \((Ur n3,tmp_l),(Ur n4,tmp_r),tmp1) ->
                                 writeSort2 cmp src_l tmp_l &
                                     \tmp_l1 ->
                                         writeSort2 cmp src_r tmp_r &
                                             \tmp_r1 ->
                                                 {- tmp1 `lseq` src1 `lseq` tmp_l1 `lseq` tmp_r1 -}
                                                 (tmp1 `lseq` writeMerge_par cmp n3 tmp_l1 n4 tmp_r1 src1)

-- | Sort the left and right halves of 'src' into 'tmp', and merge the results
-- back into 'tmp'.
writeSort2 :: Show a => (a -> a -> Int) -> Array2 a %1-> Array2 a %1-> Array2 a
writeSort2 cmp src0 tmp =
    {- INVARIANT: length src0 == length tmp -}
    size2 src0 &
        \(Ur len, src) ->
            if len <= 1
            then tmp `lseq` src
            else splitAt (len `div` 2) src &
                     \((Ur n1,src_l),(Ur n2,src_r),src1) ->
                         splitAt (len `div` 2) tmp &
                             {- INVARIANT: n1 == n3, and n2 == n4 -}
                             \((Ur _n3,tmp_l),(Ur _n4,tmp_r),tmp1) ->
                                 writeSort1 cmp src_l tmp_l &
                                     \src_l1 ->
                                         writeSort1 cmp src_r tmp_r &
                                             \src_r1 ->
                                                 {- tmp1 `lseq` src1 `lseq` src_l1 `lseq` src_r1 -}
                                                 {- Unsafe.toLinear (traceShow len) -}
                                                 (src1 `lseq` writeMerge_par cmp n1 src_l1 n2 src_r1 tmp1)

-- | Merge 'src_1' and 'src_2' into 'tmp'.
writeMerge_par :: forall a. Show a => (a -> a -> Int) -> Int -> Array2 a %1-> Int -> Array2 a %1-> Array2 a %1-> Array2 a
writeMerge_par cmp n1 src_10 n2 src_20 tmp0 =
    if (n1+n2) <= 2
    then writeMerge_seq cmp n1 src_10 n2 src_20 tmp0
    else
        if (n1 == 0)
        then src_10 `lseq` write_loop 0 0 n2 src_20 tmp0
        else if (n2 == 0)
             then src_20 `lseq` write_loop 0 0 n1 src_10 tmp0
             else go (n1 `div` 2) src_10 src_20 tmp0
  where
    go :: Show a => Int -> Array2 a %1-> Array2 a %1-> Array2 a %1-> Array2 a
    go mid1 src_1 src_2 tmp =
        unsafeGet2 mid1 src_1 &
            \(Ur pivot, src_11) ->
                binarySearch cmp pivot src_2 &
                    \(Ur mid2, src_21) ->
                        go2 mid1 mid2 pivot src_11 src_21 tmp

    go2 :: Show a => Int -> Int -> a -> Array2 a %1-> Array2 a %1-> Array2 a %1-> Array2 a
    go2 mid1 mid2 pivot src_1 src_2 tmp00 =
        unsafeSet2 (mid1+mid2) pivot tmp00 &
            \tmp ->
                {- (Unsafe.toLinear (traceShow (mid1,mid2,pivot))) (src_1 `lseq` src_2 `lseq` tmp) -}
                splitAt2 mid1 (mid1+1) src_1 &
                    \((Ur n5,src_1_l),(Ur n6,src_1_r),src_11) ->
                        splitAt mid2 src_2 &
                            \((Ur n3,src_2_l),(Ur n4,src_2_r),src_21) ->
                                splitAt2 (mid1+mid2) (mid1+mid2+1) tmp &
                                    \((Ur _,tmp_l),(Ur _,tmp_r),tmp1) ->
                                        writeMerge_par cmp n5 src_1_l n6 src_2_l tmp_l &
                                            \tmp_l1 ->
                                                writeMerge_par cmp n3 src_1_r n4 src_2_r tmp_r &
                                                    \tmp_r1 ->
                                                        {-
                                                         - need to join tmp_l1 and tmp_r1. but copying tmp_l1 and tmp_r1
                                                         - into a new vector would be inefficient. instead we should return
                                                         - the underlying mutable array
                                                         -}
                                                        src_11 `lseq` src_21 `lseq` tmp1 `lseq` tmp_r1  `lseq` tmp_l1



-- | Merge 'src_1' and 'src_2' into 'tmp'.
writeMerge_seq :: Show a => (a -> a -> Int) -> Int -> Array2 a %1-> Int -> Array2 a %1-> Array2 a %1-> Array2 a
writeMerge_seq cmp n1 src_1 n2 src_2 tmp = writeMerge_seq_loop 0 0 0 n1 n2 cmp src_1 src_2 tmp


-- | The main sequential merge function.
-- i1 index into src_1
-- i2 index into src_2
-- j index into tmp (output).
writeMerge_seq_loop :: Show a => Int -> Int -> Int -> Int -> Int -> (a -> a -> Int) -> Array2 a %1-> Array2 a %1-> Array2 a %1-> Array2 a
writeMerge_seq_loop i1 i2 j n1 n2 cmp src_1 src_2 tmp =
    if (i1 == n1)
    then src_1 `lseq` write_loop_seq j i2 n2 src_2 tmp
    else if i2 == n2
         then src_2 `lseq` write_loop_seq j i1 n1 src_1 tmp
         else
             unsafeGet2 i1 src_1 &
                 \(Ur x1, src_11) ->
                     unsafeGet2 i2 src_2 &
                         \(Ur x2, src_21) ->
                             if cmp x1 x2 < 0
                             then
                                 unsafeSet2 j x1 tmp &
                                     \tmp_1 -> writeMerge_seq_loop (i1+1) i2 (j+1) n1 n2 cmp src_11 src_21 tmp_1
                             else
                                 unsafeSet2 j x2 tmp &
                                     \tmp_1 -> writeMerge_seq_loop i1 (i2+1) (j+1) n1 n2 cmp src_11 src_21 tmp_1

write_loop :: Show a => Int -> Int -> Int -> Array2 a %1-> Array2 a %1-> Array2 a
write_loop = write_loop_seq

-- | Copy elements from 'from' to 'to'.
--
-- from[from_idx]    ===>   to[to_idx]
-- from[from_idx+1]  ===>   to[to_idx+1]
-- ...
write_loop_seq :: Show a => Int -> Int -> Int -> Array2 a %1-> Array2 a %1-> Array2 a
write_loop_seq to_idx from_idx end from to =
    if from_idx == end
    then from `lseq` to
    else
        unsafeGet2 from_idx from &
            \(Ur val, from1) ->
                unsafeSet2 to_idx val to &
                    \to1 -> write_loop_seq (to_idx+1) (from_idx+1) end from1 to1

-- | Return 'query's *position* in 'vec'.
--
-- That is, return a *p* s.t.
-- (1) elements vec[0]..vec[p] are less than query, and
-- (2) elements vec[p+1]..vec[end] are greater than query.
binarySearch :: forall a. Show a => (a -> a -> Int) -> a -> Array2 a %1-> (Ur Int, Array2 a)
{-# INLINE binarySearch #-}
binarySearch cmp query = Unsafe.toLinear go
  where
    go :: Show a => Array2 a -> (Ur Int, Array2 a)
    go vec = let (Ur len, vec1) = size2 vec
             in (Ur (binarySearch' 0 len cmp vec1 query), vec1)

binarySearch' :: Show a => Int -> Int -> (a -> a -> Int) -> Array2 a %1-> a -> Int
binarySearch' lo hi cmp vec query =
    if n == 0
    then vec `lseq` lo
    {- mid = (lo+(div n 2)) -}
    else  unsafeGet2 (lo+(div n 2)) vec &
          \(Ur pivot, vec1) ->
              if (cmp query pivot) < 0
              then binarySearch' lo (lo+(div n 2)) cmp vec1 query
              else if (cmp query pivot) > 0
                   then binarySearch' ((lo+(div n 2))+1) hi cmp vec1 query
                   else vec1 `lseq` (lo+(div n 2))
  where
    n = hi - lo


--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

goto_seqmerge :: Int
{-# INLINE goto_seqmerge #-}
goto_seqmerge = 4096

spawn :: Show a => a -> a
{-# INLINE spawn #-}
spawn x = x

compare1 :: Show a => Ord a => a -> a -> Int
compare1 r1 r2 =
    case r1 `compare` r2 of
        LT -> -1
        EQ -> 0
        GT -> 1

sortList :: [Int] -> [Int]
sortList xs =
    fromList2 xs (\input -> mergeSort 0 compare1 input) &
        \(Ur sorted) -> Unsafe.toLinear unur (toList2 sorted)

genRevList :: Int -> [Int]
genRevList n = [n,n-1..1]

test1 :: Bool
test1 = sortList (genRevList 10) == [1..10]


--------------------------------------------------------------------------------
-- An Arrays API
--------------------------------------------------------------------------------

{-
 - See Ed Kmett's comments here:
 -
 - [1]: https://github.com/tweag/linear-base/issues/312
 - [2]: https://github.com/ekmett/linear-haskell/blob/6f9e5c0e96d0c99d064ae027086db48c4fcfc63c/linear-keys/src/Linear/Range.hs
 -}

type Array2 a = Arr.Array a

size2 :: Array2 a %1 -> (Ur Int, Array2 a)
size2 = Arr.size

slice2 :: Int -> Int -> Array2 a %1-> (Array2 a, Array2 a)
slice2 = Arr.slice

fromList2 :: [a] -> (Array2 a %1-> Ur b) %1 -> Ur b
fromList2 = Arr.fromList

toList2 :: Array2 a %1-> Ur [a]
toList2 = Arr.toList

alloc2 :: Int -> a -> (Array2 a %1-> Ur b) %1 -> Ur b
alloc2 = Arr.alloc

unsafeGet2 :: Int -> Array2 a %1-> (Ur a, Array2 a)
unsafeGet2 = Arr.unsafeGet

unsafeSet2 :: Int -> a -> Array2 a %1-> Array2 a
unsafeSet2 = Arr.unsafeSet

-- | 'slice2' is not O(1), it copies elements. So this splitAt is quite expensive :(
splitAt :: Show a => Int -> Array2 a %1-> ((Ur Int,Array2 a),(Ur Int,Array2 a),Array2 a)
splitAt n arr0 = splitAt2 n n arr0

splitAt2 :: Show a => Int -> Int -> Array2 a %1-> ((Ur Int,Array2 a),(Ur Int,Array2 a),Array2 a)
splitAt2 n m arr0 =
    size2 arr0 &
        \(Ur len, arr1) ->
            slice2 0 n arr1 &
                \(arr2, slice1) ->
                    slice2 m (len - m) arr2 &
                        \(arr3, slice2) ->
                            ((Ur n,slice1), (Ur (len-n),slice2), arr3)
