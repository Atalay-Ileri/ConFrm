#! /bin/sh

rm -rf -f ./extracted
mkdir extracted
cp ./*.hs ./extracted
cp ./Interpreter/*.hs ./extracted
cd extracted

# Write imports to proper files

sed -ie '/^module/a import qualified Helpers' Log.hs
sed -ie '/^module/a import Data.Serialize' Log.hs
sed -ie '/^module/a import GHC.Generics (Generic)' Log.hs
sed -i '2s/^/{-# LANGUAGE DeriveGeneric #-}\n/' Log.hs

sed -ie '/^   Build_txn_record BaseTypes.Coq_key/a \ \ \ deriving (Generic)\ninstance Serialize Coq_txn_record' Log.hs
sed -ie '/^   Build_header_part BaseTypes.Coq_hash/a \ \ \ deriving (Generic)\ninstance Serialize Coq_header_part' Log.hs
sed -ie '/^   Build_header Coq_header_part/a \ \ \ deriving (Generic)\ninstance Serialize Coq_header' Log.hs

sed -ie '/^module/a import qualified LogCache' Transaction.hs

sed -ie '/^module/a import qualified Helpers' Inode.hs
sed -ie '/^module/a import qualified Transaction' Inode.hs
sed -ie '/^module/a import System.Posix.Types' Inode.hs
sed -ie '/^module/a import Data.Serialize' Inode.hs
sed -ie '/^module/a import GHC.Generics (Generic)' Inode.hs
sed -i '2s/^/{-# LANGUAGE DeriveGeneric #-}\n/' Inode.hs
sed -ie '/^   Build_Inode BaseTypes.Coq_user/a \ \ \ deriving (Generic)\n\ninstance Serialize System.Posix.Types.CUid where\n' Inode.hs
sed -ie '/^instance Serialize System.Posix.Types.CUid/a \ \ \ put (CUid c) = do\n\ \ \ \ \ put c\n\n\ \ \ get = do\n\ \ \ \ \ c <- get\n\ \ \ \ \ Prelude.return (CUid c)\n\ninstance Serialize Inode' Inode.hs

sed -ie '/^module/a import qualified Transaction' File.hs
sed -ie '/^module/a import qualified System.Posix.User' File.hs
sed -ie '/^module/a import qualified Interpreter' File.hs

sed -ie '/^module/a import qualified Interpreter' BatchOperations.hs
sed -ie '/^module/a import qualified Interpreter' Log.hs
sed -ie '/^module/a import qualified Interpreter' LogCache.hs
sed -ie '/^module/a import qualified Interpreter' Transaction.hs
sed -ie '/^module/a import qualified Interpreter' Inode.hs

sed -ie '/^module/a import qualified System.Posix.Types' BaseTypes.hs
sed -ie '/^module/a import qualified Data.ByteString' BaseTypes.hs
sed -ie '/^module/a import qualified Data.Word' BaseTypes.hs
sed -ie '/^module/a import qualified Data.List' BaseTypes.hs
sed -ie '/^module/a import qualified Data.List.Split' BaseTypes.hs
sed -ie '/^module/a import qualified Data.Int' BaseTypes.hs
sed -ie '/^module/a import qualified Helpers' BaseTypes.hs
sed -ie '/^module/a import qualified Crypto.Hash' BaseTypes.hs
sed -ie '/^module/a import qualified Crypto.Hash.Algorithms' BaseTypes.hs
sed -ie '/^module/a import Prelude' BaseTypes.hs

# Compile Haskell files 
ghc -prof -fprof-auto -rtsopts -O2 -threaded ConFs.hs
ghc -prof -fprof-auto -rtsopts -O2 -threaded mkfs.hs

