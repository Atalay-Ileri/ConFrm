import Prelude
import Helpers
import qualified File
import qualified BaseTypes
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Serialize as BIN
import qualified Data.List.Split as L
import System.Posix.Types
import System.Posix.User
import Data.Maybe

repeatNTimes 0 _ = return ()
repeatNTimes n action =
 do
  action n
  repeatNTimes (n-1) action


main :: IO ()
main = do 
{-
    let l = replicate 2000 128
    let intsPerBlock = div BaseTypes.block_size Helpers.intSize
    print (padList intsPerBlock l)
    print ((L.chunksOf intsPerBlock . padList intsPerBlock) l)
    print (map (BS.length . BIN.encode) $ (L.chunksOf intsPerBlock . padList intsPerBlock) l)
    print (map BS.length (BaseTypes.addr_list_to_blocks l))
    print (BaseTypes.blocks_to_addr_list (BaseTypes.addr_list_to_blocks l))
-}

  do
    File.init
    userId <- getEffectiveUserID
    
    fn <- File.create userId
    print fn
    let fileName = fromJust fn
    repeatNTimes 510 (\ i ->  File.extend fileName (stringToBlock (div BaseTypes.block_size 8) "I love you <3"))
    repeatNTimes 510 (\ i -> do
      dat <- File.read fileName (i-1)
      print ((blockToString . fromJust) dat))

    File.write fileName 0 (stringToBlock (div BaseTypes.block_size 8) "Goodbye World!")
    dat <- File.read fileName 0
    print ((blockToString . fromJust) dat)

    ret <- File.delete fileName
    print (isJust ret)
    dat <- File.read fileName 0
    print (isNothing dat) --Should fail
  
    fn <- File.create userId
    print fn
    fa <- File.create (CUid 123)
    print fa
    let fileName = fromJust fn
    dat <- File.read fileName 0
    print (isNothing dat) --should fail

    File.extend fileName (stringToBlock (div BaseTypes.block_size 8) "")
    dat <- File.read fileName 0
    print ((blockToString . fromJust) dat)

    ret <- File.change_owner fileName userId
    print (isJust ret) --should succeed
    dat <- File.read fileName 0
    print ((blockToString . fromJust) dat)

    ret <- File.change_owner fileName (CUid 123)
    print (isJust ret)

    dat <- File.read fileName 0
    print (isNothing dat) --should fail

    ret <- File.change_owner fileName userId
    print (isNothing dat) --should fail

    fn <- File.create userId
    print fn
    return ()
