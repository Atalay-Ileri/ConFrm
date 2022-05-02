module ListUtils where

import qualified Prelude
import qualified BaseTypes
import qualified Datatypes
import qualified List
import qualified Specif

updn :: (([]) a1) -> Prelude.Int -> a1 -> ([]) a1
updn vs n v =
  case vs of {
   ([]) -> ([]);
   (:) v' vs' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> (:) v vs')
      (\n' -> (:) v' (updn vs' n' v))
      n}

dedup_last :: (a1 -> a1 -> Prelude.Bool) -> (([])
              a1) -> ([]) a1
dedup_last aEQ la =
  case la of {
   ([]) -> ([]);
   (:) a la' ->
    case List.in_dec aEQ a la' of {
     Prelude.True -> dedup_last aEQ la';
     Prelude.False -> (:) a (dedup_last aEQ la')}}

dedup_by_list :: (a1 -> a1 -> Prelude.Bool) ->
                 (([]) a1) -> (([]) a2) -> ([])
                 a2
dedup_by_list aEQ la lb =
  case la of {
   ([]) -> ([]);
   (:) a la' ->
    case lb of {
     ([]) -> ([]);
     (:) b lb' ->
      case List.in_dec aEQ a la' of {
       Prelude.True -> dedup_by_list aEQ la' lb';
       Prelude.False -> (:) b
        (dedup_by_list aEQ la' lb')}}}

coq_NoDup_dec :: (BaseTypes.EqDec a1) -> (([])
                 a1) -> Prelude.Bool
coq_NoDup_dec tEQ l =
  Datatypes.list_rec Prelude.True (\a l0 iHl ->
    Specif.sumbool_rec (\_ ->
      let {s = List.in_dec tEQ a l0} in
      case s of {
       Prelude.True -> Prelude.False;
       Prelude.False -> Prelude.True}) (\_ ->
      Prelude.False) iHl) l

