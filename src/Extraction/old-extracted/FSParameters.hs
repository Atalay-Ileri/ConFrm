module FSParameters where

import qualified Prelude
import qualified BaseTypes
import qualified Nat

hdr_block_num :: Prelude.Int
hdr_block_num =
  0

log_start :: Prelude.Int
log_start =
  Prelude.succ 0

log_length :: Prelude.Int
log_length = 512

data_start :: Prelude.Int
data_start =
  Prelude.succ log_length

data_length :: Prelude.Int
data_length =
  Nat.sub BaseTypes.disk_size data_start

inode_blocks_start :: Prelude.Int
inode_blocks_start =
  0

inode_count :: Prelude.Int
inode_count = 4096

file_blocks_start :: Prelude.Int
file_blocks_start =
  Prelude.succ inode_count

file_blocks_count :: Prelude.Int
file_blocks_count = 4096

