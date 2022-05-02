{-# OPTIONS_GHC -cpp -XMagicHash #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Inode where

import qualified Prelude
import qualified BaseTypes
import qualified Datatypes
import qualified FSParameters
import qualified List
import qualified ListUtils
import Interpreter

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

type Inum = BaseTypes.Coq_addr

data Inode =
   Build_Inode BaseTypes.Coq_user (([]) BaseTypes.Coq_addr)

owner :: Inode -> BaseTypes.Coq_user
owner i =
  case i of {
   Build_Inode owner0 _ -> owner0}

block_numbers :: Inode -> ([]) BaseTypes.Coq_addr
block_numbers i =
  case i of {
   Build_Inode _ block_numbers0 -> block_numbers0}

encode_inode :: Inode -> BaseTypes.Coq_value
encode_inode = (Helpers.setToBlockSize (Prelude.div BaseTypes.block_size 8) Prelude.. Data.Serialize.encode)

decode_inode :: BaseTypes.Coq_value -> Inode
decode_inode = \x -> case Data.Serialize.decode x of {
Prelude.Left _ -> Build_Inode 0 []; 
Prelude.Right h -> h }

_InodeAllocatorParams__bitmap_addr :: Prelude.Int
_InodeAllocatorParams__bitmap_addr =
  FSParameters.inode_blocks_start

_InodeAllocatorParams__num_of_blocks :: Prelude.Int
_InodeAllocatorParams__num_of_blocks =
  FSParameters.inode_count

_InodeAllocator__alloc :: BaseTypes.Coq_value -> Prelude.IO
                          (Prelude.Maybe Prelude.Int)
_InodeAllocator__alloc v' =
  (Prelude.>>=) (
    (unsafeCoerce (Transaction.read _InodeAllocatorParams__bitmap_addr)))
    (\v ->
    let {bits = BaseTypes.value_to_bits (unsafeCoerce v)} in
    let {
     index = BaseTypes.get_first_zero_index
               (List.firstn _InodeAllocatorParams__num_of_blocks bits)}
    in
    case (Prelude.<) index _InodeAllocatorParams__num_of_blocks of {
     Prelude.True -> (Prelude.>>=) (
      (unsafeCoerce (Transaction.write
        ((Prelude.+) _InodeAllocatorParams__bitmap_addr (Prelude.succ index))
        v'))) (\r ->
      case unsafeCoerce r of {
       Prelude.Just _ -> (Prelude.>>=) (
        (unsafeCoerce (Transaction.write _InodeAllocatorParams__bitmap_addr
          (BaseTypes.bits_to_value (ListUtils.updn bits index Prelude.True)))))
        (\r0 ->
        case unsafeCoerce r0 of {
         Prelude.Just _ -> Prelude.return (Prelude.Just index);
         Prelude.Nothing -> Prelude.return Prelude.Nothing});
       Prelude.Nothing -> Prelude.return Prelude.Nothing});
     Prelude.False -> Prelude.return Prelude.Nothing})

_InodeAllocator__free :: Prelude.Int -> Prelude.IO (Prelude.Maybe ())
_InodeAllocator__free a =
  case (Prelude.<) a _InodeAllocatorParams__num_of_blocks of {
   Prelude.True -> (Prelude.>>=) (
    (unsafeCoerce (Transaction.read _InodeAllocatorParams__bitmap_addr)))
    (\v ->
    let {bits = BaseTypes.value_to_bits (unsafeCoerce v)} in
    case List.nth_error bits a of {
     Prelude.Just b ->
      case b of {
       Prelude.True -> 
        (unsafeCoerce (Transaction.write _InodeAllocatorParams__bitmap_addr
          (BaseTypes.bits_to_value (ListUtils.updn bits a Prelude.False))));
       Prelude.False -> Prelude.return Prelude.Nothing};
     Prelude.Nothing -> Prelude.return Prelude.Nothing});
   Prelude.False -> Prelude.return Prelude.Nothing}

_InodeAllocator__free_bits_rec :: (([]) Prelude.Bool) -> (([]) Prelude.Int)
                                  -> Prelude.Maybe (([]) Prelude.Bool)
_InodeAllocator__free_bits_rec bits l_a =
  case l_a of {
   ([]) -> Prelude.Just bits;
   (:) a l_a' ->
    case List.nth_error bits a of {
     Prelude.Just y ->
      case y of {
       Prelude.True ->
        case _InodeAllocator__free_bits_rec bits l_a' of {
         Prelude.Just bits' -> Prelude.Just
          (ListUtils.updn bits' a Prelude.False);
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.False -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

_InodeAllocator__free_all :: (([]) Prelude.Int) -> Prelude.IO
                             (Prelude.Maybe ())
_InodeAllocator__free_all l_a =
  (Prelude.>>=) (
    (unsafeCoerce (Transaction.read _InodeAllocatorParams__bitmap_addr)))
    (\v ->
    let {bits = BaseTypes.value_to_bits (unsafeCoerce v)} in
    case _InodeAllocator__free_bits_rec bits l_a of {
     Prelude.Just bits' -> 
      (unsafeCoerce (Transaction.write _InodeAllocatorParams__bitmap_addr
        (BaseTypes.bits_to_value bits')));
     Prelude.Nothing -> Prelude.return Prelude.Nothing})

_InodeAllocator__read :: Prelude.Int -> Prelude.IO
                         (Prelude.Maybe BaseTypes.Coq_value)
_InodeAllocator__read a =
  case (Prelude.<) a _InodeAllocatorParams__num_of_blocks of {
   Prelude.True -> (Prelude.>>=) (
    (unsafeCoerce (Transaction.read _InodeAllocatorParams__bitmap_addr)))
    (\v ->
    let {bits = BaseTypes.value_to_bits (unsafeCoerce v)} in
    case List.nth_error bits a of {
     Prelude.Just b ->
      case b of {
       Prelude.True -> (Prelude.>>=) (
        (unsafeCoerce (Transaction.read
          ((Prelude.+) _InodeAllocatorParams__bitmap_addr (Prelude.succ a)))))
        (\v0 -> Prelude.return (Prelude.Just (unsafeCoerce v0)));
       Prelude.False -> Prelude.return Prelude.Nothing};
     Prelude.Nothing -> Prelude.return Prelude.Nothing});
   Prelude.False -> Prelude.return Prelude.Nothing}

_InodeAllocator__write :: Prelude.Int -> BaseTypes.Coq_value -> Prelude.IO
                          (Prelude.Maybe ())
_InodeAllocator__write a b =
  case (Prelude.<) a _InodeAllocatorParams__num_of_blocks of {
   Prelude.True -> (Prelude.>>=) (
    (unsafeCoerce (Transaction.read _InodeAllocatorParams__bitmap_addr)))
    (\v ->
    let {bits = BaseTypes.value_to_bits (unsafeCoerce v)} in
    case List.nth_error bits a of {
     Prelude.Just b0 ->
      case b0 of {
       Prelude.True -> 
        (unsafeCoerce (Transaction.write
          ((Prelude.+) _InodeAllocatorParams__bitmap_addr (Prelude.succ a))
          b));
       Prelude.False -> Prelude.return Prelude.Nothing};
     Prelude.Nothing -> Prelude.return Prelude.Nothing});
   Prelude.False -> Prelude.return Prelude.Nothing}

get_inode :: Prelude.Int -> Prelude.IO (Prelude.Maybe Inode)
get_inode inum =
  (Prelude.>>=) (unsafeCoerce _InodeAllocator__read inum) (\r ->
    case unsafeCoerce r of {
     Prelude.Just i -> Prelude.return (Prelude.Just (decode_inode i));
     Prelude.Nothing -> Prelude.return Prelude.Nothing})

set_inode :: Prelude.Int -> Inode -> Prelude.IO (Prelude.Maybe ())
set_inode inum inode =
  _InodeAllocator__write inum (encode_inode inode)

alloc :: BaseTypes.Coq_user -> Prelude.IO (Prelude.Maybe Prelude.Int)
alloc user =
  _InodeAllocator__alloc (encode_inode (Build_Inode user ([])))

free :: Prelude.Int -> Prelude.IO (Prelude.Maybe ())
free =
  _InodeAllocator__free

extend :: Prelude.Int -> BaseTypes.Coq_addr -> Prelude.IO (Prelude.Maybe ())
extend inum block_num =
  (Prelude.>>=) (unsafeCoerce get_inode inum) (\r ->
    case unsafeCoerce r of {
     Prelude.Just inode ->
      set_inode inum (Build_Inode (owner inode)
        (Datatypes.app (block_numbers inode) ((:) block_num ([]))));
     Prelude.Nothing -> Prelude.return Prelude.Nothing})

change_owner :: Prelude.Int -> BaseTypes.Coq_user -> Prelude.IO
                (Prelude.Maybe ())
change_owner inum user =
  (Prelude.>>=) (unsafeCoerce get_inode inum) (\r ->
    case unsafeCoerce r of {
     Prelude.Just inode ->
      set_inode inum (Build_Inode user (block_numbers inode));
     Prelude.Nothing -> Prelude.return Prelude.Nothing})

get_block_number :: Prelude.Int -> Prelude.Int -> Prelude.IO
                    (Prelude.Maybe BaseTypes.Coq_addr)
get_block_number inum off =
  (Prelude.>>=) (unsafeCoerce get_inode inum) (\r ->
    case unsafeCoerce r of {
     Prelude.Just inode -> Prelude.return
      (List.nth_error (block_numbers inode) off);
     Prelude.Nothing -> Prelude.return Prelude.Nothing})

get_all_block_numbers :: Prelude.Int -> Prelude.IO
                         (Prelude.Maybe (([]) BaseTypes.Coq_addr))
get_all_block_numbers inum =
  (Prelude.>>=) (unsafeCoerce get_inode inum) (\r ->
    case unsafeCoerce r of {
     Prelude.Just inode -> Prelude.return (Prelude.Just
      (block_numbers inode));
     Prelude.Nothing -> Prelude.return Prelude.Nothing})

get_owner :: Prelude.Int -> Prelude.IO (Prelude.Maybe BaseTypes.Coq_user)
get_owner inum =
  (Prelude.>>=) (unsafeCoerce get_inode inum) (\r ->
    case unsafeCoerce r of {
     Prelude.Just inode -> Prelude.return (Prelude.Just (owner inode));
     Prelude.Nothing -> Prelude.return Prelude.Nothing})

