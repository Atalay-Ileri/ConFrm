module PeanoNat where

import qualified Prelude

_Nat__ltb :: Prelude.Int -> Prelude.Int ->
             Prelude.Bool
_Nat__ltb n m =
  (Prelude.<=) (Prelude.succ n) m

