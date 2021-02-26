#! /bin/bash

rm -rf ./extracted
mkdir extracted
mv ./*.hs ./extracted
cd extracted

# Write imports to proper files
sed -ie '/^module/a import qualified LogCache' Transaction.hs
sed -ie '/^module/a import qualified Transaction' Inode.hs
sed -ie '/^module/a import qualified Transaction' File.hs
sed -ie '/^module/a import qualified System.Posix.User' File.hs
sed -ie '/^module/a import qualified System.Posix.Types' BaseTypes.hs

# Compile Haskell files 
ghc File.hs
