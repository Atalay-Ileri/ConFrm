{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LogCache where

import qualified Prelude
import qualified BaseTypes
import qualified Compare_dec
import qualified Datatypes
import qualified FSParameters
import qualified List
import qualified ListUtils
import qualified Log
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

write_batch_to_cache :: (([]) BaseTypes.Coq_addr)
                        -> (([])
                        BaseTypes.Coq_value) ->
                        Prelude.IO ()
write_batch_to_cache al vl =
  case al of {
   ([]) -> Prelude.return ();
   (:) a al' ->
    case vl of {
     ([]) -> Prelude.return ();
     (:) v vl' -> (Prelude.>>=)
      ( (
        (unsafeCoerce (Interpreter.cacheWrite a
          v)))) (\_ ->
      write_batch_to_cache al' vl')}}

coq_Forall_dec :: (a1 -> Prelude.Bool) -> (([])
                  a1) -> Prelude.Bool
coq_Forall_dec p_dec l =
  Datatypes.list_rec Prelude.True (\a _ iHl ->
    let {s = p_dec a} in
    case s of {
     Prelude.True -> iHl;
     Prelude.False -> Prelude.False}) l

write :: (([]) Prelude.Int) -> (([])
         BaseTypes.Coq_value) -> Prelude.IO 
         ()
write addr_l data_l =
  case coq_Forall_dec (\a ->
         (Prelude.<) a FSParameters.data_length)
         addr_l of {
   Prelude.True ->
    case ListUtils.coq_NoDup_dec
           BaseTypes.addr_dec addr_l of {
     Prelude.True ->
      case (Prelude.==) (Datatypes.length addr_l)
             (Datatypes.length data_l) of {
       Prelude.True ->
        case Compare_dec.le_dec
               ((Prelude.+)
                 (Datatypes.length
                   (BaseTypes.addr_list_to_blocks
                     (List.map
                       ((Prelude.+)
                         FSParameters.data_start)
                       addr_l)))
                 (Datatypes.length data_l))
               FSParameters.log_length of {
         Prelude.True -> (Prelude.>>=)
          (timeItNamed internalTimes "Internal LogCommit" GHC.Base.$ 
            (unsafeCoerce Log.commit
              (BaseTypes.addr_list_to_blocks
                (List.map
                  ((Prelude.+)
                    FSParameters.data_start)
                  addr_l)) data_l))
          (\committed -> (Prelude.>>=)
          (case unsafeCoerce committed of {
            Prelude.True -> Prelude.return
             (unsafeCoerce ());
            Prelude.False -> (Prelude.>>=)
             (timeItNamed internalTimes "Internal LogApply" GHC.Base.$  (unsafeCoerce Log.apply_log))
             (\_ -> (Prelude.>>=)
             ( (
               (unsafeCoerce
                 Interpreter.cacheFlush))) (\_ ->
             (Prelude.>>=)
             (timeItNamed internalTimes "Internal LogCommit" GHC.Base.$ 
               (unsafeCoerce Log.commit
                 (BaseTypes.addr_list_to_blocks
                   (List.map
                     ((Prelude.+)
                       FSParameters.data_start)
                     addr_l)) data_l)) (\_ ->
             Prelude.return (unsafeCoerce ()))))})
          (\_ -> timeItNamed internalTimes "Internal WriteBatch" GHC.Base.$ 
          write_batch_to_cache
            (List.map
              ((Prelude.+)
                FSParameters.data_start) addr_l)
            data_l));
         Prelude.False -> Prelude.return ()};
       Prelude.False -> Prelude.return ()};
     Prelude.False -> Prelude.return ()};
   Prelude.False -> Prelude.return ()}

read :: Prelude.Int -> Prelude.IO
        BaseTypes.Coq_value
read a =
  case (Prelude.<) a FSParameters.data_length of {
   Prelude.True -> (Prelude.>>=)
    ( (
      (unsafeCoerce (Interpreter.cacheRead
        ((Prelude.+) FSParameters.data_start a)))))
    (\mv ->
    case unsafeCoerce mv of {
     Prelude.Just v -> (Prelude.>>=)
      ( (
        (unsafeCoerce (Interpreter.cacheWrite
          ((Prelude.+) FSParameters.data_start a)
          v)))) (\_ -> Prelude.return v);
     Prelude.Nothing -> (Prelude.>>=)
      (
        ( (
          (unsafeCoerce (Interpreter.diskRead
            ((Prelude.+) FSParameters.data_start
              a)))))) (\v -> (Prelude.>>=)
      ( (
        (unsafeCoerce (Interpreter.cacheWrite
          ((Prelude.+) FSParameters.data_start a)
          v)))) (\_ -> Prelude.return
      (unsafeCoerce v)))});
   Prelude.False -> Prelude.return
    BaseTypes.value0}

write_lists_to_cache :: (([])
                        ((,)
                        (([]) BaseTypes.Coq_addr)
                        (([])
                        BaseTypes.Coq_value))) ->
                        Prelude.IO ()
write_lists_to_cache l_al_vl =
  case l_al_vl of {
   ([]) -> Prelude.return ();
   (:) al_vl l -> (Prelude.>>=)
    (unsafeCoerce write_batch_to_cache
      (Datatypes.fst al_vl)
      (Datatypes.snd al_vl)) (\_ ->
    write_lists_to_cache l)}

recover :: Prelude.IO ()
recover =
  (Prelude.>>=)
    ( ( (unsafeCoerce Interpreter.cacheFlush)))
    (\_ -> (Prelude.>>=)
    ( (unsafeCoerce Log.recover)) (\log ->
    write_lists_to_cache (unsafeCoerce log)))

init :: (([])
        ((,) Prelude.Int BaseTypes.Coq_value)) ->
        Prelude.IO ()
init l_av =
  let {l_a = List.map Datatypes.fst l_av} in
  let {l_v = List.map Datatypes.snd l_av} in
  (Prelude.>>=)
  ( ( (unsafeCoerce Interpreter.cacheFlush)))
  (\_ ->
  
    (Log.init
      (List.combine
        (List.map
          ((Prelude.+) FSParameters.data_start)
          l_a) l_v)))

