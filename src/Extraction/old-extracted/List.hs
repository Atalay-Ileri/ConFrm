module List where

import qualified Prelude
import qualified Datatypes

in_dec :: (a1 -> a1 -> Prelude.Bool) -> a1 ->
          (([]) a1) -> Prelude.Bool
in_dec h a l =
  Datatypes.list_rec Prelude.False (\a0 _ iHl ->
    let {s = h a0 a} in
    case s of {
     Prelude.True -> Prelude.True;
     Prelude.False -> iHl}) l

nth_error :: (([]) a1) -> Prelude.Int ->
             Prelude.Maybe a1
nth_error l n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) x _ -> Prelude.Just x})
    (\n0 ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) _ l0 -> nth_error l0 n0})
    n

rev :: (([]) a1) -> ([]) a1
rev l =
  case l of {
   ([]) -> ([]);
   (:) x l' ->
    Datatypes.app (rev l') ((:) x ([]))}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

combine :: (([]) a1) -> (([]) a2) -> ([])
           ((,) a1 a2)
combine l l' =
  case l of {
   ([]) -> ([]);
   (:) x tl ->
    case l' of {
     ([]) -> ([]);
     (:) y tl' -> (:) ((,) x y) (combine tl tl')}}

firstn :: Prelude.Int -> (([]) a1) -> ([]) a1
firstn n l =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\n0 ->
    case l of {
     ([]) -> ([]);
     (:) a l0 -> (:) a (firstn n0 l0)})
    n

skipn :: Prelude.Int -> (([]) a1) -> ([]) a1
skipn n l =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> l)
    (\n0 ->
    case l of {
     ([]) -> ([]);
     (:) _ l0 -> skipn n0 l0})
    n

seq :: Prelude.Int -> Prelude.Int -> ([])
       Prelude.Int
seq start len =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\len0 -> (:) start
    (seq (Prelude.succ start) len0))
    len

repeat :: a1 -> Prelude.Int -> ([]) a1
repeat x n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\k -> (:) x (repeat x k))
    n

