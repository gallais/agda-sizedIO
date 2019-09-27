module System.Directory.Primitive where

open import Data.Unit
open import Data.Bool.Base
open import Data.List.Base
open import Foreign.Haskell.Maybe
open import Data.Nat.Base
open import Data.String.Base
open import IO.Primitive
open import System.FilePath.Posix

{-# FOREIGN GHC import System.Directory #-}
{-# FOREIGN GHC import Data.Text        #-}

data XdgDirectory : Set where
  XdgData XdgConfig XdgCache : XdgDirectory

data XdgDirectoryList : Set where
  XdgDataDirs XdgConfigDirs : XdgDirectoryList

{-# COMPILE GHC XdgDirectory     = data XdgDirectory (XdgData|XdgConfig|XdgCache)    #-}
{-# COMPILE GHC XdgDirectoryList = data XdgDirectoryList (XdgDataDirs|XdgConfigDirs) #-}

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
  listDirectory             : FilePath n → IO (List RelativePath)
  getDirectoryContents      : FilePath n → IO (List RelativePath)

  -- Current working directory

  getCurrentDirectory       : IO AbsolutePath
  setCurrentDirectory       : FilePath n → IO ⊤
  withCurrentDirectory      : ∀ {a} {A : Set a} → FilePath n → IO A → IO A

  -- Pre-defined directories

  getHomeDirectory          : IO AbsolutePath
  getXdgDirectory           : XdgDirectory → RelativePath → IO AbsolutePath
  getXdgDirectoryList       : XdgDirectoryList → IO (List AbsolutePath)
  getAppUserDataDirectory   : RelativePath → IO AbsolutePath
  getUserDocumentsDirectory : IO AbsolutePath
  getTemporaryDirectory     : IO AbsolutePath

  -- Actions on files
  removeFile                     : FilePath m → IO ⊤
  renameFile                     : FilePath m → FilePath n → IO ⊤
  renamePath                     : FilePath m → FilePath n → IO ⊤
  copyFile                       : FilePath m → FilePath n → IO ⊤
  copyFileWithMetadata           : FilePath m → FilePath n → IO ⊤
  getFileSize                    : FilePath n → IO ℕ
  canonicalizePath               : FilePath n → IO AbsolutePath
  makeAbsolute                   : FilePath n → IO AbsolutePath
  makeRelativeToCurrentDirectory : FilePath n → IO RelativePath

  -- Existence tests

  doesPathExist                : FilePath n → IO Bool
  doesFileExist                : FilePath n → IO Bool
  doesDirectoryExist           : FilePath n → IO Bool
  findExecutable               : String → IO (Maybe AbsolutePath)
  findExecutables              : String → IO (List AbsolutePath)
  findExecutablesInDirectories : List (FilePath n) → String → IO (List (FilePath n))
  findFile                     : List (FilePath n) → String → IO (Maybe (FilePath n))
  findFiles                    : List (FilePath n) → String → IO (List (FilePath n))
  findFileWith                 : (FilePath n → IO Bool) → List (FilePath n) → String → IO (Maybe (FilePath n))
  findFilesWith                : (FilePath n → IO Bool) → List (FilePath n) → String → IO (List (FilePath n))
  exeExtension                 : String

{-# COMPILE GHC createDirectory                = const createDirectory                                #-}
{-# COMPILE GHC createDirectoryIfMissing       = const createDirectoryIfMissing                       #-}
{-# COMPILE GHC removeDirectory                = const removeDirectory                                #-}
{-# COMPILE GHC removeDirectoryRecursive       = const removeDirectoryRecursive                       #-}
{-# COMPILE GHC removePathForcibly             = const removePathForcibly                             #-}
{-# COMPILE GHC renameDirectory                = \ _ _ -> renameDirectory                             #-}
{-# COMPILE GHC listDirectory                  = const listDirectory                                  #-}
{-# COMPILE GHC getDirectoryContents           = const getDirectoryContents                           #-}

{-# COMPILE GHC getCurrentDirectory            = getCurrentDirectory                                  #-}
{-# COMPILE GHC setCurrentDirectory            = const setCurrentDirectory                            #-}
{-# COMPILE GHC withCurrentDirectory           = \ _ _ _ -> withCurrentDirectory                      #-}

{-# COMPILE GHC getHomeDirectory               = getHomeDirectory                                     #-}
{-# COMPILE GHC getXdgDirectory                = getXdgDirectory                                      #-}
{-# COMPILE GHC getXdgDirectoryList            = getXdgDirectoryList                                  #-}
{-# COMPILE GHC getAppUserDataDirectory        = getAppUserDataDirectory                              #-}
{-# COMPILE GHC getUserDocumentsDirectory      = getUserDocumentsDirectory                            #-}
{-# COMPILE GHC getTemporaryDirectory          = getTemporaryDirectory                                #-}

{-# COMPILE GHC removeFile                     = const removeFile                                     #-}
{-# COMPILE GHC renameFile                     = \ _ _ -> renameFile                                  #-}
{-# COMPILE GHC renamePath                     = \ _ _ -> renamePath                                  #-}
{-# COMPILE GHC copyFile                       = \ _ _ -> copyFile                                    #-}
{-# COMPILE GHC copyFileWithMetadata           = \ _ _ -> copyFileWithMetadata                        #-}
{-# COMPILE GHC getFileSize                    = const getFileSize                                    #-}
{-# COMPILE GHC canonicalizePath               = const canonicalizePath                               #-}
{-# COMPILE GHC makeAbsolute                   = const makeAbsolute                                   #-}
{-# COMPILE GHC makeRelativeToCurrentDirectory = const makeRelativeToCurrentDirectory                 #-}

{-# COMPILE GHC doesPathExist                  = const doesPathExist                                  #-}
{-# COMPILE GHC doesFileExist                  = const doesFileExist                                  #-}
{-# COMPILE GHC doesDirectoryExist             = const doesDirectoryExist                             #-}
{-# COMPILE GHC findExecutable                 = findExecutable . unpack                              #-}
{-# COMPILE GHC findExecutables                = findExecutables . unpack                             #-}
{-# COMPILE GHC findExecutablesInDirectories   = \ _ fps -> findExecutablesInDirectories fps . unpack #-}
{-# COMPILE GHC findFile                       = \ _ fps -> findFile fps . unpack                     #-}
{-# COMPILE GHC findFiles                      = \ _ fps -> findFiles fps . unpack                    #-}
{-# COMPILE GHC findFileWith                   = \ _ p fps -> findFileWith p fps . unpack             #-}
{-# COMPILE GHC findFilesWith                  = \ _ p fps -> findFilesWith p fps . unpack            #-}
{-# COMPILE GHC exeExtension                   = pack exeExtension                                    #-}
