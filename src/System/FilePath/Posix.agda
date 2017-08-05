module System.FilePath.Posix where

open import Agda.Builtin.String

postulate
  FilePath    : Set
  mkFilePath  : String → FilePath
  getFilePath : FilePath → String

{-# FOREIGN GHC import Data.Text            #-}
{-# COMPILE GHC FilePath    = type FilePath #-}
{-# COMPILE GHC mkFilePath  = unpack        #-}
{-# COMPILE GHC getFilePath = pack          #-}
