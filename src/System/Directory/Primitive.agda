module System.Directory.Primitive where

open import Data.Unit
open import Data.Bool.Base
open import Data.List.Base
open import IO.Primitive
open import System.FilePath.Posix

postulate

  -- Actions on directories

  createDirectory           : FilePath → IO ⊤
  createDirectoryIfMissing  : Bool → FilePath → IO ⊤
  removeDirectory           : FilePath → IO ⊤
  removeDirectoryRecursive  : FilePath → IO ⊤
  removePathForcibly        : FilePath → IO ⊤
  renameDirectory           : FilePath → FilePath → IO ⊤
  listDirectory             : FilePath → IO (List FilePath)

  -- Current working directory

  getDirectoryContents      : FilePath → IO (List FilePath)
  getCurrentDirectory       : IO FilePath
  setCurrentDirectory       : FilePath → IO ⊤
  withCurrentDirectory      : ∀ {a} {A : Set a} → FilePath → IO A → IO A

  -- Pre-defined directories

  getHomeDirectory          : IO FilePath
  getUserDocumentsDirectory : IO FilePath
  getTemporaryDirectory     : IO FilePath

  -- Actions on filepath

  makeAbsolute : FilePath → IO FilePath

  -- Existence tests

  doesPathExist      : FilePath -> IO Bool
  doesFileExist      : FilePath -> IO Bool
  doesDirectoryExist : FilePath -> IO Bool


{-# FOREIGN GHC import System.Directory #-}
{-# COMPILE createDirectory createDirectory #-}

{-# COMPILE GHC createDirectoryIfMissing  = createDirectoryIfMissing      #-}
{-# COMPILE GHC removeDirectory           = removeDirectory               #-}
{-# COMPILE GHC removeDirectoryRecursive  = removeDirectoryRecursive      #-}
{-# COMPILE GHC removePathForcibly        = removePathForcibly            #-}
{-# COMPILE GHC renameDirectory           = renameDirectory               #-}
{-# COMPILE GHC listDirectory             = listDirectory                 #-}
{-# COMPILE GHC getDirectoryContents      = getDirectoryContents          #-}
{-# COMPILE GHC getCurrentDirectory       = getCurrentDirectory           #-}
{-# COMPILE GHC setCurrentDirectory       = setCurrentDirectory           #-}
{-# COMPILE GHC withCurrentDirectory      = \ _ _ -> withCurrentDirectory #-}
{-# COMPILE GHC getHomeDirectory          = getHomeDirectory              #-}
{-# COMPILE GHC getUserDocumentsDirectory = getUserDocumentsDirectory     #-}
{-# COMPILE GHC getTemporaryDirectory     = getTemporaryDirectory         #-}
{-# COMPILE GHC makeAbsolute              = makeAbsolute                  #-}
{-# COMPILE GHC doesPathExist             = doesPathExist                 #-}
{-# COMPILE GHC doesFileExist             = doesFileExist                 #-}
{-# COMPILE GHC doesDirectoryExist        = doesDirectoryExist            #-}
