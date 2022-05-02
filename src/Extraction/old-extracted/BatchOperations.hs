{-# OPTIONS_GHC -cpp -XMagicHash #-}
{-# LANGUAGE BangPatterns #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module BatchOperations where

import qualified Prelude
import qualified BaseTypes
import qualified Datatypes
import qualified List
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

read_consecutive :: BaseTypes.Coq_addr ->
                    Prelude.Int -> Prelude.IO
                    (([]) BaseTypes.Coq_value)
read_consecutive a count =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.return ([]))
    (\count' -> (Prelude.>>=)
    ( ( (unsafeCoerce (Interpreter.diskRead a))))
    (\v -> (Prelude.>>=)
    (unsafeCoerce read_consecutive (Prelude.succ
      a) count') (\vl -> Prelude.return ((:)
    (unsafeCoerce v) (unsafeCoerce vl)))))
    count

write_batch :: (([]) BaseTypes.Coq_addr) -> (([])
               BaseTypes.Coq_value) -> Prelude.IO
               ()
write_batch al !vl =
  case al of {
   ([]) -> Prelude.return ();
   (:) a al' ->
    case vl of {
     ([]) -> Prelude.return ();
     (:) v vl' -> (Prelude.>>=)
      ( (
        (timeItNamed internalTimes "Internal DiskWriteBatch" GHC.Base.$ unsafeCoerce (Interpreter.diskWrite a
          v)))) (\_ -> (Prelude.>>=)
      (unsafeCoerce write_batch al' vl') (\_ ->
      Prelude.return ()))}}

write_consecutive :: Prelude.Int -> (([])
                     BaseTypes.Coq_value) ->
                     Prelude.IO ()
write_consecutive a vl =
  write_batch (List.seq a (Datatypes.length vl))
    vl

encrypt_all :: BaseTypes.Coq_key -> (([])
               BaseTypes.Coq_value) -> Prelude.IO
               (([]) BaseTypes.Coq_value)
encrypt_all k vl =
  case vl of {
   ([]) -> Prelude.return ([]);
   (:) v vl' -> (Prelude.>>=)
    ( (
      (unsafeCoerce (Interpreter.cryptoEncrypt k
        v)))) (\ev -> (Prelude.>>=)
    (unsafeCoerce encrypt_all k vl') (\evl' ->
    Prelude.return ((:) (unsafeCoerce ev)
    (unsafeCoerce evl'))))}

decrypt_all :: BaseTypes.Coq_key -> (([])
               BaseTypes.Coq_value) -> Prelude.IO
               (([]) BaseTypes.Coq_value)
decrypt_all k evl =
  case evl of {
   ([]) -> Prelude.return ([]);
   (:) ev evl' -> (Prelude.>>=)
    ( (
      (unsafeCoerce (Interpreter.cryptoDecrypt k
        ev)))) (\v -> (Prelude.>>=)
    (unsafeCoerce decrypt_all k evl') (\vl' ->
    Prelude.return ((:) (unsafeCoerce v)
    (unsafeCoerce vl'))))}

hash_all :: BaseTypes.Coq_hash -> (([])
            BaseTypes.Coq_value) -> Prelude.IO
            BaseTypes.Coq_hash
hash_all h vl =
  case vl of {
   ([]) -> Prelude.return h;
   (:) v vl' -> (Prelude.>>=)
    ( (
      (unsafeCoerce (Interpreter.cryptoHash h v))))
    (\h' -> (Prelude.>>=)
    (unsafeCoerce hash_all h' vl') (\h'' ->
    Prelude.return (unsafeCoerce h'')))}

