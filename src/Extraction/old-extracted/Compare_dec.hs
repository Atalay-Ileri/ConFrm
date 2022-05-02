module Compare_dec where

import qualified Prelude

le_gt_dec :: Prelude.Int -> Prelude.Int ->
             Prelude.Bool
le_gt_dec =
  (Prelude.<=)

le_dec :: Prelude.Int -> Prelude.Int ->
          Prelude.Bool
le_dec =
  le_gt_dec

