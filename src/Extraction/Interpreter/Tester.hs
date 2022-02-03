import Prelude
import Helpers
import qualified ConFs
import qualified File
import qualified BaseTypes
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Serialize as BIN
import qualified Data.List.Split as L
import System.Posix.Types
import System.Posix.User
import Data.Maybe
import Data.Time.Clock
import Data.IORef

repeatNTimes 0 _ = return ()
repeatNTimes n action =
 do
  action n
  repeatNTimes (n-1) action

repeatUntil' start end duration action count = do
  r <- action
  curTime <- getCurrentTime
  beginTime <- readIORef start
  -- print (show (diffUTCTime curTime beginTime))
  case r of
    Nothing -> do
      writeIORef end curTime
      return (count + 1)
    Just _ -> do
      if diffUTCTime curTime beginTime < duration then
        repeatUntil' start end duration action (count + 1)
      else do
        writeIORef end curTime
        return (count + 1)
    
repeatUntil start end duration action = repeatUntil' start end duration action 0

smallWriteSize :: Int
smallWriteSize = 100

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
    ConFs.confsInit "disk_file"
    -- small file
    print "Starting Small File Test"
    userId <- getEffectiveUserID
    time <- getCurrentTime
    begin <- newIORef time
    end <- newIORef time
    count <- repeatUntil begin end (50 :: NominalDiffTime) (do 
      mfn <- File.create userId
      case mfn of
        Just fn -> do 
          r <- ConFs.confsWrite "" fn (BS.replicate 100 128) 0
          case r of 
            Left _ -> do 
              print "Write error"
              return Nothing
            Right _ -> return (Just ())
        Nothing -> do 
          print "Create error"
          return Nothing) 
    begin <- readIORef begin
    end <- readIORef end
    print (show begin)
    print (show end)
    print (show (diffUTCTime end begin))
    print (show count) 
    return ()
