module System.FilePath.Posix.Primitive where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Foreign.Haskell as FFI

postulate

  FilePath     : Set
  mkFilePath   : String → FilePath
  getFilePath  : FilePath → String

  Extension    : Set
  mkExtension  : String → Extension
  getExtension : Extension → String

{-# FOREIGN GHC import Data.Text             #-}
{-# FOREIGN GHC import System.FilePath.Posix #-}
{-# COMPILE GHC FilePath     = type FilePath #-}
{-# COMPILE GHC mkFilePath   = unpack        #-}
{-# COMPILE GHC getFilePath  = pack          #-}
{-# COMPILE GHC Extension    = type String   #-}
{-# COMPILE GHC mkExtension  = unpack        #-}
{-# COMPILE GHC getExtension = pack          #-}

postulate

  splitExtension : FilePath → Pair FilePath Extension
  splitExtensions : FilePath → Pair FilePath Extension

  takeExtension : FilePath → Extension
  takeExtensions : FilePath → Extension

  replaceExtension : FilePath → Extension → FilePath
  replaceExtensions : FilePath → Extension → FilePath

  dropExtension : FilePath → FilePath
  dropExtensions : FilePath → FilePath

  addExtension : FilePath → Extension → FilePath
  hasExtension : FilePath → Bool

  stripExtension : Extension → FilePath → FFI.Maybe FilePath

  splitFileName : FilePath → Pair FilePath FilePath
  takeFileName : FilePath → FilePath
  replaceFileName : FilePath → FilePath → FilePath
  dropFileName : FilePath → FilePath
  takeBaseName : FilePath → String
  replaceBaseName : FilePath → String → FilePath
  takeDirectory : FilePath → FilePath
  replaceDirectory : FilePath → FilePath → FilePath
  combine : FilePath → FilePath → FilePath
  splitPath : FilePath → List FilePath
  joinPath : List FilePath → FilePath
  splitDirectories : FilePath → List FilePath
  normalise : FilePath → FilePath

{-# COMPILE GHC splitExtension = splitExtension #-}
{-# COMPILE GHC splitExtensions = splitExtensions #-}
{-# COMPILE GHC takeExtension = takeExtension #-}
{-# COMPILE GHC takeExtensions = takeExtensions #-}
{-# COMPILE GHC replaceExtension = replaceExtension #-}
{-# COMPILE GHC replaceExtensions = replaceExtensions #-}
{-# COMPILE GHC dropExtension = dropExtension #-}
{-# COMPILE GHC dropExtensions = dropExtensions #-}
{-# COMPILE GHC addExtension = addExtension #-}
{-# COMPILE GHC hasExtension = hasExtension #-}
{-# COMPILE GHC stripExtension = stripExtension #-}
{-# COMPILE GHC splitFileName = splitFileName #-}
{-# COMPILE GHC takeFileName = takeFileName #-}
{-# COMPILE GHC replaceFileName = replaceFileName  #-}
{-# COMPILE GHC dropFileName = dropFileName #-}
{-# COMPILE GHC takeBaseName = pack . takeBaseName #-}
{-# COMPILE GHC replaceBaseName = fmap (. unpack)replaceBaseName #-}
{-# COMPILE GHC takeDirectory = takeDirectory #-}
{-# COMPILE GHC replaceDirectory = replaceDirectory #-}
{-# COMPILE GHC combine = combine #-}
{-# COMPILE GHC splitPath = splitPath #-}
{-# COMPILE GHC joinPath = joinPath #-}
{-# COMPILE GHC splitDirectories = splitDirectories #-}
{-# COMPILE GHC normalise = normalise #-}
