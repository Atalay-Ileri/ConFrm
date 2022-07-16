{-# LANGUAGE PackageImports, BangPatterns #-}
module Directory where

import Prelude
import Data.Map
import Data.IORef
import BaseTypes
import GHC.IO.Unsafe
import qualified Interpreter
import Data.Persist
import Foreign.C.Error
import Data.Maybe
import qualified Data.List as L
import Data.String
import qualified Helpers
import qualified Data.ByteString as BS
{-
Haskell implemented directories all names should be unique
-}
dirMapAddr :: Int
dirMapAddr = 128 * 1024


-- This is a map from directory names to list of files/dirs under it.
-- if it is a file, then second field contains its inode number, which should be used as the file descriptor
dirMap :: IORef (Map String (Either [String] Coq_addr))
{-# NOINLINE dirMap #-}
dirMap = unsafePerformIO (newIORef (insert "/" (Left []) empty))

initializeDirMap :: IO ()
initializeDirMap = do
  writeIORef dirMap (insert "/" (Left []) empty)
  persistDirMap

recoverDirMap :: IO ()
recoverDirMap = do
  dirBlock <- Interpreter.diskRead dirMapAddr
  let edm = (decode dirBlock)
  ---- print "--Recovering dirMap"
  ---- print edm
  case edm of
    Left e -> 
      -- print e
      return ()
    Right dm -> 
      writeIORef dirMap dm


persistDirMap :: IO ()
persistDirMap = do
  dm <- readIORef dirMap
  let dmBlock = Helpers.setToBlockSize (div Interpreter.block_size 8) (encode dm) 
  Interpreter.diskWrite dirMapAddr dmBlock
  Interpreter.diskSync
  return()


getInum :: String -> Map String (Either [String] Coq_addr) -> Maybe Coq_addr
getInum fn dm =
  case Data.Map.lookup fn dm of
    Nothing -> Nothing
    Just e ->
      case e of
        Right i -> Just i
        Left sl -> Nothing

getInumPath :: [String] -> Map String (Either [String] Coq_addr) -> Maybe Coq_addr
getInumPath [] _ = Nothing
getInumPath [fn] dm = getInum fn dm
getInumPath (d:rest) dm =
  if isValidFilePath (d:rest) dm then
    getInumPath rest dm
  else
    Nothing

getSubdirs :: String -> Map String (Either [String] Coq_addr) -> Maybe [String]
getSubdirs fn dm =
  case Data.Map.lookup fn dm of
    Nothing -> Nothing
    Just e ->
      case e of
        Right _ -> Nothing
        Left sl -> Just sl

isDir ::  String -> Map String (Either [String] Coq_addr) -> Bool
isDir d dm = isJust (getSubdirs d dm)

isSubdir ::  String -> String -> Map String (Either [String] Coq_addr) -> Bool
isSubdir parent child dm =
  case Data.Map.lookup parent dm of
    Nothing -> False
    Just e ->
      case e of
        Right _ -> False
        Left sl -> elem child sl

isFile :: String -> Map String (Either [String] Coq_addr) -> Bool
isFile d dm = isJust (getInum d dm)

isValidPath :: [String] -> Map String (Either [String] Coq_addr) -> Bool
isValidPath [] dm = True
isValidPath [c] dm = isDir c dm || isFile c dm
isValidPath (p : c : rest) dm = isSubdir p c dm && isValidPath (c:rest) dm

isValidDirPath :: [String] -> Map String (Either [String] Coq_addr) -> Bool
isValidDirPath [] dm = True
isValidDirPath [c] dm = isDir c dm
isValidDirPath (p : c : rest) dm = isSubdir p c dm && isValidDirPath (c:rest) dm

isValidFilePath :: [String] -> Map String (Either [String] Coq_addr) -> Bool
isValidFilePath [] dm = True
isValidFilePath [c] dm = isFile c dm
isValidFilePath (p : c : rest) dm = isSubdir p c dm && isValidFilePath (c:rest) dm

-- for some reason library function is not working
delete :: String -> [String] -> [String]
delete s [] = []
delete s (s':rest) = if s == s' then rest else s':(Directory.delete s rest)

{- Modifiers -}
rename_with_parent :: String -> String -> String -> String -> Map String (Either [String] Coq_addr) -> (Map String (Either [String] Coq_addr) , Errno)
rename_with_parent sp sc dp dc dm =
  if sp == dp && sc == dc then
    (dm, eOK)
  else
    case Data.Map.lookup sp dm of
    Nothing -> (dm, eIO)
    Just spd ->
      case spd of
      Right _ -> (dm, eIO)
      Left sl -> 
        case Data.Map.lookup dp dm of
        Nothing -> (dm, eIO)
        Just dpd ->
          case dpd of
          Right _ -> (dm, eIO)
          Left dl -> 
            case Data.Map.lookup sc dm of
            Nothing -> (dm, eIO)
            Just scf ->
              if sp == dp then
                (Data.Map.insert dc scf 
                (Data.Map.insert dp (Left (Directory.delete sc sl))
                (Data.Map.delete sc dm)), eOK)
              else
                (Data.Map.insert dc scf 
                (Data.Map.insert dp (Left (dc:dl)) 
                (Data.Map.insert sp (Left (Directory.delete sc sl))
                (Data.Map.delete sc dm))), eOK)

rename_single :: String -> String -> Map String (Either [String] Coq_addr) -> (Map String (Either [String] Coq_addr) , Errno)
rename_single sc dc dm =
    case Data.Map.lookup sc dm of
    Nothing -> (dm, eIO)
    Just scf ->
      (Data.Map.insert dc scf (Data.Map.delete sc dm), eOK)

rename :: [String] -> [String] -> Map String (Either [String] Coq_addr) -> (Map String (Either [String] Coq_addr) , Errno)
rename [sc] [dc] dm = rename_single sc dc dm
rename [sp, sc] [dp, dc] dm = rename_with_parent sp sc dp dc dm
rename (sp : sc : srest) (dp : dc : drest) dm = 
  let (dm', e) = rename (sc:srest) (dc:drest) dm in
    case e of
      eOK -> rename_with_parent sp sc dp dc dm'
      _ -> (dm, e)
    

removeDir :: [String] -> Map String (Either [String] Coq_addr) -> (Map String (Either [String] Coq_addr) , Errno)
removeDir [c] dm = (Data.Map.delete c dm, eOK)
removeDir [p, c] dm = 
  case Data.Map.lookup p dm of
    Nothing -> (dm, eIO)
    Just dpd ->
      case dpd of
        Right _ -> (dm, eIO)
        Left pl ->
          case Data.Map.lookup c dm of
            Nothing -> (dm, eIO)
            Just dcd ->
              case dcd of
                Right _ -> (dm, eIO)
                Left cl ->
                  if cl == [] then
                    (Data.Map.delete c 
                    (Data.Map.insert p (Left (Directory.delete c pl)) dm), eOK)
                  else
                    (dm, eIO)
removeDir (p : c : rest) dm = 
  if (isSubdir p c dm) then
    removeDir (c:rest) dm
  else
    (dm, eIO)

removeFile :: [String] -> Map String (Either [String] Coq_addr) -> (Map String (Either [String] Coq_addr) , Errno)
removeFile [p, c] dm = 
  case Data.Map.lookup p dm of
    Nothing -> (dm, eIO)
    Just dpd ->
      case dpd of
        Right _ -> (dm, eIO)
        Left pl ->
            if (isFile c dm) then 
              (Data.Map.delete c (Data.Map.insert p (Left (Directory.delete c pl)) dm), eOK)
            else
              (dm, eIO)

removeFile (p : c : rest) dm = 
  if (isSubdir p c dm) then
    removeFile (c:rest) dm
  else
    (dm, eIO)

removeFile [c] dm = 
  if (isFile c dm) then 
    (Data.Map.delete c dm, eOK)
  else
    (dm, eIO)

addDir :: [String] -> Map String (Either [String] Coq_addr) -> (Map String (Either [String] Coq_addr) , Errno)
addDir [c] dm = 
  if (isFile c dm) || (isDir c dm) then 
    (dm, eIO)
  else
    (Data.Map.insert c (Left []) dm, eOK)
addDir [p, c] dm = 
      case Data.Map.lookup p dm of
        Nothing -> (dm, eIO)
        Just dpd ->
          case dpd of
            Right _ -> (dm, eIO)
            Left pl ->
                if (isFile c dm) || (isDir c dm) then 
                  (dm, eIO)
                else
                  (Data.Map.insert c (Left []) (Data.Map.insert p (Left (c : pl)) dm), eOK)
                  
    
addDir (p : c : rest) dm = 
  if (isSubdir p c dm) then
    addDir (c:rest) dm
  else
    (dm, eIO)

addFile :: [String] -> Coq_addr -> Map String (Either [String] Coq_addr) -> (Map String (Either [String] Coq_addr) , Errno)
addFile [c] inum dm = 
  if (isFile c dm) || (isDir c dm) then 
    (dm, eIO)
  else
    (Data.Map.insert c (Right inum) dm, eOK)

addFile [p, c] inum dm = 
  case Data.Map.lookup p dm of
    Nothing -> (dm, eIO)
    Just dpd ->
      case dpd of
        Right _ -> (dm, eIO)
        Left pl ->
            if (isFile c dm) || (isDir c dm) then 
              (dm, eIO)
            else
              (Data.Map.insert c (Right inum)
              (Data.Map.insert p (Left (c:pl)) dm), eOK)
              
        
addFile (p : c : rest) inum dm = 
  if (isSubdir p c dm) then
    addFile (c:rest) inum dm
  else
    (dm, eIO)

onDirMap :: (Map String (Either [String] Coq_addr) -> a) -> IO a
onDirMap f = Interpreter.timeItNamed Interpreter.opTimes "Directory Read"
  (do
  dm <- readIORef dirMap
  return (f dm))

modifyDirMap :: (Map String (Either [String] Coq_addr) -> (Map String (Either [String] Coq_addr) , a)) -> IO a
modifyDirMap f = do 
  r <- (Interpreter.timeItNamed Interpreter.opTimes "Directory Modify" (do 
    dm <- readIORef dirMap
    -- print "**modifyDirMap**"
    -- print "Old Map:"
    -- print dm
    let (newMap, ret) = f dm
    writeIORef dirMap newMap
    return ret))
  persistDirMap
  -- print "New Map:"
  -- print newMap
  -- print "***************"
  return r