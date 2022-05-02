{-# OPTIONS_GHC -cpp -XMagicHash #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Avoid lambda" #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module File where

import qualified Prelude
import qualified BaseTypes
import qualified Datatypes
import qualified FSParameters
import qualified Inode
import qualified LayerImplementation
import qualified List
import qualified ListUtils

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import Interpreter
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

_DiskAllocatorParams__bitmap_addr :: Prelude.Int
_DiskAllocatorParams__bitmap_addr =
  FSParameters.file_blocks_start

_DiskAllocatorParams__num_of_blocks :: Prelude.Int
_DiskAllocatorParams__num_of_blocks =
  FSParameters.file_blocks_count

_DiskAllocator__alloc :: BaseTypes.Coq_value ->
                         Prelude.IO
                         (Prelude.Maybe
                         Prelude.Int)
_DiskAllocator__alloc v' =
  (Prelude.>>=) (
    (unsafeCoerce (Transaction.read
      _DiskAllocatorParams__bitmap_addr))) (\v ->
    let {
     bits = BaseTypes.value_to_bits
              (unsafeCoerce v)}
    in
    let {
     index = BaseTypes.get_first_zero_index
               (List.firstn
                 _DiskAllocatorParams__num_of_blocks
                 bits)}
    in
    case (Prelude.<) index
           _DiskAllocatorParams__num_of_blocks of {
     Prelude.True -> (Prelude.>>=) (
      (unsafeCoerce (Transaction.write
        ((Prelude.+)
          _DiskAllocatorParams__bitmap_addr
          (Prelude.succ index)) v'))) (\r ->
      case unsafeCoerce r of {
       Prelude.Just _ -> (Prelude.>>=) (
        (unsafeCoerce (Transaction.write
          _DiskAllocatorParams__bitmap_addr
          (BaseTypes.bits_to_value
            (ListUtils.updn bits index
              Prelude.True))))) (\r0 ->
        case unsafeCoerce r0 of {
         Prelude.Just _ -> Prelude.return
          (Prelude.Just index);
         Prelude.Nothing -> Prelude.return
          Prelude.Nothing});
       Prelude.Nothing -> Prelude.return
        Prelude.Nothing});
     Prelude.False -> Prelude.return
      Prelude.Nothing})

_DiskAllocator__free :: Prelude.Int -> Prelude.IO
                        (Prelude.Maybe ())
_DiskAllocator__free a =
  case (Prelude.<) a
         _DiskAllocatorParams__num_of_blocks of {
   Prelude.True -> (Prelude.>>=) (
    (unsafeCoerce (Transaction.read
      _DiskAllocatorParams__bitmap_addr))) (\v ->
    let {
     bits = BaseTypes.value_to_bits
              (unsafeCoerce v)}
    in
    case List.nth_error bits a of {
     Prelude.Just b ->
      case b of {
       Prelude.True -> 
        (unsafeCoerce (Transaction.write
          _DiskAllocatorParams__bitmap_addr
          (BaseTypes.bits_to_value
            (ListUtils.updn bits a Prelude.False))));
       Prelude.False -> Prelude.return
        Prelude.Nothing};
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing});
   Prelude.False -> Prelude.return
    Prelude.Nothing}

_DiskAllocator__free_bits_rec :: (([])
                                 Prelude.Bool) ->
                                 (([])
                                 Prelude.Int) ->
                                 Prelude.Maybe
                                 (([])
                                 Prelude.Bool)
_DiskAllocator__free_bits_rec bits l_a =
  case l_a of {
   ([]) -> Prelude.Just bits;
   (:) a l_a' ->
    case List.nth_error bits a of {
     Prelude.Just y ->
      case y of {
       Prelude.True ->
        case _DiskAllocator__free_bits_rec bits
               l_a' of {
         Prelude.Just bits' -> Prelude.Just
          (ListUtils.updn bits' a Prelude.False);
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.False -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

_DiskAllocator__free_all :: (([]) Prelude.Int) ->
                            Prelude.IO
                            (Prelude.Maybe ())
_DiskAllocator__free_all l_a =
  (Prelude.>>=) (
    (unsafeCoerce (Transaction.read
      _DiskAllocatorParams__bitmap_addr))) (\v ->
    let {
     bits = BaseTypes.value_to_bits
              (unsafeCoerce v)}
    in
    case _DiskAllocator__free_bits_rec bits l_a of {
     Prelude.Just bits' -> 
      (unsafeCoerce (Transaction.write
        _DiskAllocatorParams__bitmap_addr
        (BaseTypes.bits_to_value bits')));
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing})

_DiskAllocator__read :: Prelude.Int -> Prelude.IO
                        (Prelude.Maybe
                        BaseTypes.Coq_value)
_DiskAllocator__read a =
  case (Prelude.<) a
         _DiskAllocatorParams__num_of_blocks of {
   Prelude.True -> (Prelude.>>=) (
    (unsafeCoerce (Transaction.read
      _DiskAllocatorParams__bitmap_addr))) (\v ->
    let {
     bits = BaseTypes.value_to_bits
              (unsafeCoerce v)}
    in
    case List.nth_error bits a of {
     Prelude.Just b ->
      case b of {
       Prelude.True -> (Prelude.>>=) (
        (unsafeCoerce (Transaction.read
          ((Prelude.+)
            _DiskAllocatorParams__bitmap_addr
            (Prelude.succ a))))) (\v0 ->
        Prelude.return (Prelude.Just
        (unsafeCoerce v0)));
       Prelude.False -> Prelude.return
        Prelude.Nothing};
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing});
   Prelude.False -> Prelude.return
    Prelude.Nothing}

_DiskAllocator__write :: Prelude.Int ->
                         BaseTypes.Coq_value ->
                         Prelude.IO
                         (Prelude.Maybe ())
_DiskAllocator__write a b =
  case (Prelude.<) a
         _DiskAllocatorParams__num_of_blocks of {
   Prelude.True -> (Prelude.>>=) (
    (unsafeCoerce (Transaction.read
      _DiskAllocatorParams__bitmap_addr))) (\v ->
    let {
     bits = BaseTypes.value_to_bits
              (unsafeCoerce v)}
    in
    case List.nth_error bits a of {
     Prelude.Just b0 ->
      case b0 of {
       Prelude.True -> 
        (unsafeCoerce (Transaction.write
          ((Prelude.+)
            _DiskAllocatorParams__bitmap_addr
            (Prelude.succ a)) b));
       Prelude.False -> Prelude.return
        Prelude.Nothing};
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing});
   Prelude.False -> Prelude.return
    Prelude.Nothing}

auth_then_exec :: Inode.Inum -> (Inode.Inum ->
                  LayerImplementation.Coq_prog
                  (Prelude.Maybe a1)) ->
                  Prelude.IO (Prelude.Maybe a1)
auth_then_exec inum p =
  (Prelude.>>=)
    (timeItNamed internalTimes "Internal InodeGetOwner" GHC.Base.$ (unsafeCoerce Inode.get_owner inum))
    (\mo ->
    case unsafeCoerce mo of {
     Prelude.Just owner -> (Prelude.>>=)
      (timeItNamed internalTimes "Internal Auth" GHC.Base.$ (
        (unsafeCoerce
          ((\u -> do uid <- System.Posix.User.getEffectiveUserID; Prelude.return (u Prelude.== uid))
          owner)))) (\ok ->
      case unsafeCoerce ok of {
       Prelude.Just _ -> (Prelude.>>=)
        ( (unsafeCoerce p inum)) (\r ->
        case unsafeCoerce r of {
         Prelude.Just v -> (Prelude.>>=)
          (timeItNamed internalTimes "Internal Commit" GHC.Base.$ ( (unsafeCoerce Transaction.commit)))
          (\_ -> Prelude.return (Prelude.Just v));
         Prelude.Nothing -> (Prelude.>>=)
          (timeItNamed internalTimes "Internal Abort" GHC.Base.$ ( (unsafeCoerce Transaction.abort)))
          (\_ -> Prelude.return Prelude.Nothing)});
       Prelude.Nothing -> (Prelude.>>=)
        (timeItNamed internalTimes "Internal Abort" GHC.Base.$ ( (unsafeCoerce Transaction.abort)))
        (\_ -> Prelude.return Prelude.Nothing)});
     Prelude.Nothing -> (Prelude.>>=)
      (timeItNamed internalTimes "Internal Abort" GHC.Base.$ ( (unsafeCoerce Transaction.abort)))
      (\_ -> Prelude.return Prelude.Nothing)})

read_inner :: Prelude.Int -> Prelude.Int ->
              Prelude.IO
              (Prelude.Maybe BaseTypes.Coq_value)
read_inner off inum = timeItNamed internalTimes "Internal ReadInner" GHC.Base.$
  (Prelude.>>=)
    (unsafeCoerce Inode.get_block_number inum
      off) (\r ->
    case unsafeCoerce r of {
     Prelude.Just block_number -> (Prelude.>>=)
      (unsafeCoerce _DiskAllocator__read
        block_number) (\r0 ->
      case unsafeCoerce r0 of {
       Prelude.Just v -> Prelude.return
        (Prelude.Just v);
       Prelude.Nothing -> Prelude.return
        Prelude.Nothing});
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing})

write_inner :: Prelude.Int -> BaseTypes.Coq_value
               -> Prelude.Int -> Prelude.IO
               (Prelude.Maybe ())
write_inner off v inum = timeItNamed internalTimes "Internal WriteInner" GHC.Base.$
  (Prelude.>>=)
    (unsafeCoerce Inode.get_block_number inum
      off) (\r ->
    case unsafeCoerce r of {
     Prelude.Just block_number ->
      _DiskAllocator__write block_number v;
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing})

change_owner_inner :: BaseTypes.Coq_user ->
                      Prelude.Int -> Prelude.IO
                      (Prelude.Maybe ())
change_owner_inner owner inum =
  Inode.change_owner inum owner

delete_inner :: Prelude.Int -> Prelude.IO
                (Prelude.Maybe ())
delete_inner inum = timeItNamed internalTimes "Internal DeleteInner" GHC.Base.$
  (Prelude.>>=)
    (unsafeCoerce Inode.get_all_block_numbers
      inum) (\mbl ->
    case unsafeCoerce mbl of {
     Prelude.Just block_numbers -> (Prelude.>>=)
      (unsafeCoerce _DiskAllocator__free_all
        block_numbers) (\ok ->
      case unsafeCoerce ok of {
       Prelude.Just _ -> Inode.free inum;
       Prelude.Nothing -> Prelude.return
        Prelude.Nothing});
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing})

extend_inner :: BaseTypes.Coq_value ->
                Prelude.Int -> Prelude.IO
                (Prelude.Maybe ())
extend_inner v inum = timeItNamed internalTimes "Internal ExtendInner" GHC.Base.$
  (Prelude.>>=)
    (unsafeCoerce _DiskAllocator__alloc v)
    (\mbn ->
    case unsafeCoerce mbn of {
     Prelude.Just block_num ->
      Inode.extend inum block_num;
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing})

get_file_size_inner :: Prelude.Int -> Prelude.IO
                       (Prelude.Maybe
                       Prelude.Int)
get_file_size_inner inum =
  (Prelude.>>=)
    (unsafeCoerce Inode.get_all_block_numbers
      inum) (\mbl ->
    case unsafeCoerce mbl of {
     Prelude.Just block_numbers -> Prelude.return
      (Prelude.Just
      (Datatypes.length block_numbers));
     Prelude.Nothing -> Prelude.return
      Prelude.Nothing})

read :: Inode.Inum -> Prelude.Int -> Prelude.IO
        (Prelude.Maybe BaseTypes.Coq_value)
read inum off =
  auth_then_exec inum (read_inner off)

write :: Inode.Inum -> Prelude.Int ->
         BaseTypes.Coq_value -> Prelude.IO
         (Prelude.Maybe ())
write inum off v =
  auth_then_exec inum (write_inner off v)

extend :: Inode.Inum -> BaseTypes.Coq_value ->
          Prelude.IO (Prelude.Maybe ())
extend inum v =
  auth_then_exec inum (extend_inner v)

change_owner :: Inode.Inum -> BaseTypes.Coq_user
                -> Prelude.IO (Prelude.Maybe ())
change_owner inum owner =
  auth_then_exec inum (change_owner_inner owner)

delete :: Inode.Inum -> Prelude.IO
          (Prelude.Maybe ())
delete inum =
  auth_then_exec inum delete_inner

get_file_size :: Inode.Inum -> Prelude.IO
                 (Prelude.Maybe Prelude.Int)
get_file_size inum =
  auth_then_exec inum get_file_size_inner

create :: BaseTypes.Coq_user -> Prelude.IO
          (Prelude.Maybe Prelude.Int)
create owner =
  (Prelude.>>=)
    (timeItNamed internalTimes "Internal InodeAlloc" GHC.Base.$ (unsafeCoerce Inode.alloc owner)) (\r ->
    case unsafeCoerce r of {
     Prelude.Just inum -> (Prelude.>>=)
      (timeItNamed internalTimes "Internal Commit" GHC.Base.$ ( (unsafeCoerce Transaction.commit)))
      (\_ -> Prelude.return (Prelude.Just inum));
     Prelude.Nothing -> (Prelude.>>=)
      (timeItNamed internalTimes "Internal Abort" GHC.Base.$ ( (unsafeCoerce Transaction.abort)))
      (\_ -> Prelude.return Prelude.Nothing)})

recover :: Prelude.IO ()
recover =
   ( (unsafeCoerce Transaction.recover))

init :: Prelude.IO ()
init =
   (
    (unsafeCoerce (Transaction.init ((:) ((,)
      Inode._InodeAllocatorParams__bitmap_addr
      (BaseTypes.bits_to_value
        BaseTypes.zero_bitlist)) ((:) ((,)
      _DiskAllocatorParams__bitmap_addr
      (BaseTypes.bits_to_value
        BaseTypes.zero_bitlist)) ([]))))))

