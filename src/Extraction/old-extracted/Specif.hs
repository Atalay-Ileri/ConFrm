module Specif where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

sumbool_rect :: (() -> a1) -> (() -> a1) ->
                Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) ->
               Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

