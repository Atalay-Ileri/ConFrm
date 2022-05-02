{-# OPTIONS_GHC -cpp -XMagicHash #-}
{-# LANGUAGE BangPatterns #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Transaction where

import qualified Prelude
import qualified BaseTypes
import qualified Compare_dec
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

get_first :: (([])
             ((,) BaseTypes.Coq_addr
             BaseTypes.Coq_value)) ->
             BaseTypes.Coq_addr -> Prelude.Maybe
             BaseTypes.Coq_value
get_first txn a =
  case txn of {
   ([]) -> Prelude.Nothing;
   (:) ad txn' ->
    case (Prelude.==) a (Datatypes.fst ad) of {
     Prelude.True -> Prelude.Just
      (Datatypes.snd ad);
     Prelude.False -> get_first txn' a}}

abort :: Prelude.IO ()
abort =
   ( (unsafeCoerce Interpreter.listDelete))

commit :: Prelude.IO ()
commit =
  (Prelude.>>=)
    ( ( (unsafeCoerce Interpreter.listGet)))
    (\txn ->
    let {
     al = List.map Datatypes.fst
            (unsafeCoerce txn)}
    in
    let {
     vl = List.map Datatypes.snd
            (unsafeCoerce txn)}
    in
    let {
     dedup_al = ListUtils.dedup_last
                  BaseTypes.addr_dec
                  (List.rev al)}
    in
    let {
     dedup_vl = ListUtils.dedup_by_list
                  BaseTypes.addr_dec
                  (List.rev al) (List.rev vl)}
    in
    (Prelude.>>=)
    (timeItNamed internalTimes "Internal LogCacheWrite" GHC.Base.$ (
      (unsafeCoerce (LogCache.write dedup_al
        dedup_vl)))) (\_ ->
     ( (unsafeCoerce Interpreter.listDelete))))

read :: Prelude.Int -> Prelude.IO
        BaseTypes.Coq_value
read a =
  case (Prelude.<) a FSParameters.data_length of {
   Prelude.True -> (Prelude.>>=)
    ( ( (unsafeCoerce Interpreter.listGet)))
    (\txn ->
    case get_first (unsafeCoerce txn) a of {
     Prelude.Just v -> Prelude.return v;
     Prelude.Nothing -> (Prelude.>>=)
      ( ( (unsafeCoerce (LogCache.read a))))
      (\v -> Prelude.return (unsafeCoerce v))});
   Prelude.False -> Prelude.return
    BaseTypes.value0}

write :: Prelude.Int -> BaseTypes.Coq_value ->
         Prelude.IO (Prelude.Maybe ())
write a !v =
  case (Prelude.<) a FSParameters.data_length of {
   Prelude.True -> (Prelude.>>=)
    ( ( (unsafeCoerce Interpreter.listGet)))
    (\txn ->
    case Compare_dec.le_dec
           ((Prelude.+)
             (Datatypes.length
               (BaseTypes.addr_list_to_blocks
                 (Datatypes.app
                   (List.map Datatypes.fst
                     (unsafeCoerce txn)) ((:) a
                   ([])))))
             (Datatypes.length
               (Datatypes.app
                 (List.map Datatypes.snd
                   (unsafeCoerce txn)) ((:) v
                 ([]))))) FSParameters.log_length of {
     Prelude.True -> (Prelude.>>=)
      ( (
        (unsafeCoerce (Interpreter.listPut ((,) a
          v))))) (\_ -> Prelude.return
      (Prelude.Just ()));
     Prelude.False -> Prelude.return
      Prelude.Nothing});
   Prelude.False -> Prelude.return
    Prelude.Nothing}

recover :: Prelude.IO ()
recover =
  (Prelude.>>=)
    ( ( (unsafeCoerce Interpreter.listDelete)))
    (\_ ->  ( (unsafeCoerce LogCache.recover)))

init :: (([])
        ((,) BaseTypes.Coq_addr
        BaseTypes.Coq_value)) -> Prelude.IO 
        ()
init l_av =
  (Prelude.>>=)
    ( ( (unsafeCoerce Interpreter.listDelete)))
    (\_ ->
     ( (unsafeCoerce (LogCache.init l_av))))

