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

mergeSort :: (a -> a -> Int) -> Arr.Array a %1-> Ur (Arr.Array a)
mergeSort cmp src0 =
    Arr.size src0 &
        \(Ur len, src1) ->
            Arr.alloc len (undefined :: a) (\tmp -> go len cmp src1 tmp)
  where
    go :: Int -> (a -> a -> Int) -> Arr.Array a %1-> Arr.Array a %1-> Ur (Arr.Array a)
    go len cmp src tmp =
        writeSort1 len cmp src tmp &
            (Unsafe.toLinear Ur)

-- | Sort the left and right halves of 'src' into 'tmp', and merge the results
-- back into 'src'.
writeSort1 :: Int -> (a -> a -> Int) -> Arr.Array a %1-> Arr.Array a %1-> Arr.Array a
writeSort1 len cmp src tmp =
    if len <= 1
    then tmp `lseq` src
    else
    splitAt half src &
        \((Ur n1,src_l),(Ur n2,src_r),src1) ->
            splitAt half tmp &
                {- INVARIANT: n1 == n3, and n2 == n4 -}
                \((Ur _n3,tmp_l),(Ur _n4,tmp_r),tmp1) ->
                    writeSort2 n1 cmp src_l tmp_l &
                        \tmp_l1 ->
                            writeSort2 n2 cmp src_r tmp_r &
                                \tmp_r1 ->
                                    {- tmp1 `lseq` src1 `lseq` tmp_l1 `lseq` tmp_r1 -}
                                    (tmp1 `lseq` writeMerge len cmp tmp_l1 tmp_r1 src1)
  where
    half = len `div` 2


-- | Sort the left and right halves of 'tmp' into 'src', and merge the results
-- back into 'tmp'.
writeSort2 :: Int -> (a -> a -> Int) -> Arr.Array a %1-> Arr.Array a %1-> Arr.Array a
writeSort2 len cmp src tmp =
    if len <= 1
    then tmp `lseq` src
    else
    splitAt half src &
        \((Ur n1,src_l),(Ur n2,src_r),src1) ->
            splitAt half tmp &
                {- INVARIANT: n1 == n3, and n2 == n4 -}
                \((Ur _n3,tmp_l),(Ur _n4,tmp_r),tmp1) ->
                    writeSort1 n1 cmp src_l tmp_l &
                        \src_l1 ->
                            writeSort1 n2 cmp src_r tmp_r &
                                \src_r1 ->
                                    {- tmp1 `lseq` src1 `lseq` src_l1 `lseq` src_r1 -}
                                    {- Unsafe.toLinear (traceShow len) -}
                                    (src1 `lseq` writeMerge len cmp src_l1 src_r1 tmp1)
  where
    half = len `div` 2


-- | Merge 'src_1' and 'src_2' into 'tmp'.
writeMerge :: Int -> (a -> a -> Int) -> Arr.Array a %1-> Arr.Array a %1-> Arr.Array a %1-> Arr.Array a
writeMerge len cmp src_1 src_2 tmp =
    Arr.size src_1 &
        \(Ur n1, src_11) ->
            Arr.size src_2 &
                \(Ur n2, src_21) ->
                    writeMerge_seq_loop 0 0 0 n1 n2 cmp src_11 src_21 tmp

-- | The main sequential merge function.
-- i1 index into src_1
-- i2 index into src_2
-- j index into tmp (output).
writeMerge_seq_loop :: Int -> Int -> Int -> Int -> Int -> (a -> a -> Int) -> Arr.Array a %1-> Arr.Array a %1-> Arr.Array a %1-> Arr.Array a
writeMerge_seq_loop i1 i2 j n1 n2 cmp src_1 src_2 tmp =
    if (i1 == n1)
    then src_1 `lseq` write_loop_seq j i2 n2 src_2 tmp
    else if i2 == n2
         then src_2 `lseq` write_loop_seq j i1 n1 src_1 tmp
         else
             Arr.unsafeGet i1 src_1 &
                 \(Ur x1, src_11) ->
                     Arr.unsafeGet i2 src_2 &
                         \(Ur x2, src_21) ->
                             if cmp x1 x2 < 0
                             then
                                 Arr.unsafeSet j x1 tmp &
                                     \tmp_1 -> writeMerge_seq_loop (i1+1) i2 (j+1) n1 n2 cmp src_11 src_21 tmp_1
                             else
                                 Arr.unsafeSet j x2 tmp &
                                     \tmp_1 -> writeMerge_seq_loop i1 (i2+1) (j+1) n1 n2 cmp src_11 src_21 tmp_1

-- | Copy elements from 'from' to 'to'.
--
-- from[from_idx]    ===>   to[to_idx]
-- from[from_idx+1]  ===>   to[to_idx+1]
-- ...
write_loop_seq :: Int -> Int -> Int -> Arr.Array a %1-> Arr.Array a %1-> Arr.Array a
write_loop_seq to_idx from_idx end from to =
    if from_idx == end
    then from `lseq` to
    else
        Arr.unsafeGet from_idx from &
            \(Ur val, from1) ->
                Arr.unsafeSet to_idx val to &
                    \to1 -> write_loop_seq (to_idx+1) (from_idx+1) end from1 to1

--------------------------------------------------------------------------------

-- | 'Arr.slice' is not O(1), it copies elements. So this splitAt is quite expensive :(
splitAt :: Int -> Arr.Array a %1-> ((Ur Int, Arr.Array a), (Ur Int, Arr.Array a), Arr.Array a)
splitAt n arr0 =
    Arr.size arr0 &
        \(Ur len, arr1) ->
            if n > 0 && n < len
            then
                Arr.slice 0 n arr1 &
                    \(arr2, slice1) ->
                        Arr.slice n (len - n) arr2 &
                            \(arr3, slice2) ->
                                ((Ur n,slice1), (Ur (len-n),slice2), arr3)
            else arr1 `lseq` error ("splitAt:" ++ show (n,len))


--------------------------------------------------------------------------------
-- Tests

compare1 :: Ord a => a -> a -> Int
compare1 r1 r2 =
    case r1 `compare` r2 of
        LT -> -1
        EQ -> 0
        GT -> 1

sortList :: [Int] -> [Int]
sortList xs =
    Arr.fromList xs (\input -> mergeSort compare1 input) &
        \(Ur sorted) -> Unsafe.toLinear unur (Arr.toList sorted)

genRevList :: Int -> [Int]
genRevList n = [n,n-1..1]

test1 :: Bool
test1 = sortList (genRevList 10) == [1..10]
