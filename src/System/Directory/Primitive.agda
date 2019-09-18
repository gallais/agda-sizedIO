module System.Directory.Primitive where

open import Data.Unit
open import Data.Bool.Base
open import Data.List.Base
open import IO.Primitive
open import System.FilePath.Posix

variable
  m n : Nature

postulate

  -- Actions on directories

  createDirectory           : FilePath n → IO ⊤
  createDirectoryIfMissing  : Bool → FilePath n → IO ⊤
  removeDirectory           : FilePath n → IO ⊤
  removeDirectoryRecursive  : FilePath n → IO ⊤
  removePathForcibly        : FilePath n → IO ⊤
  renameDirectory           : FilePath m → FilePath n → IO ⊤
  listDirectory             : FilePath n → IO (List (FilePath relative))

  -- Current working directory

  getDirectoryContents      : FilePath n → IO (List (FilePath relative))
  getCurrentDirectory       : IO (FilePath absolute)
  setCurrentDirectory       : FilePath n → IO ⊤
  withCurrentDirectory      : ∀ {a} {A : Set a} → FilePath n → IO A → IO A

  -- Pre-defined directories

  getHomeDirectory          : IO (FilePath absolute)
  getUserDocumentsDirectory : IO (FilePath absolute)
  getTemporaryDirectory     : IO (FilePath absolute)

  -- Actions on filepath

  makeAbsolute : FilePath n → IO (FilePath absolute)

  -- Existence tests

  doesPathExist      : FilePath n → IO Bool
  doesFileExist      : FilePath n → IO Bool
  doesDirectoryExist : FilePath n → IO Bool


{-# FOREIGN GHC import System.Directory #-}
{-# COMPILE createDirectory createDirectory #-}

{-# COMPILE GHC createDirectoryIfMissing  = const createDirectoryIfMissing  #-}
{-# COMPILE GHC removeDirectory           = const removeDirectory           #-}
{-# COMPILE GHC removeDirectoryRecursive  = const removeDirectoryRecursive  #-}
{-# COMPILE GHC removePathForcibly        = const removePathForcibly        #-}
{-# COMPILE GHC renameDirectory           = \ _ _ -> renameDirectory        #-}
{-# COMPILE GHC listDirectory             = const listDirectory             #-}
{-# COMPILE GHC getDirectoryContents      = const getDirectoryContents      #-}
{-# COMPILE GHC getCurrentDirectory       = getCurrentDirectory             #-}
{-# COMPILE GHC setCurrentDirectory       = const setCurrentDirectory       #-}
{-# COMPILE GHC withCurrentDirectory      = \ _ _ _ -> withCurrentDirectory #-}
{-# COMPILE GHC getHomeDirectory          = getHomeDirectory                #-}
{-# COMPILE GHC getUserDocumentsDirectory = getUserDocumentsDirectory       #-}
{-# COMPILE GHC getTemporaryDirectory     = getTemporaryDirectory           #-}
{-# COMPILE GHC makeAbsolute              = const makeAbsolute              #-}
{-# COMPILE GHC doesPathExist             = const doesPathExist             #-}
{-# COMPILE GHC doesFileExist             = const doesFileExist             #-}
{-# COMPILE GHC doesDirectoryExist        = const doesDirectoryExist        #-}
