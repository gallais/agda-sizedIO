module System.FilePath.Posix where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Maybe.Base
open import Data.Product
open import Function

open import Foreign.Haskell.Coerce

open import System.FilePath.Posix.Primitive as Prim
  using ( FilePath
        ; mkFilePath
        ; getFilePath
        ; Extension
        ; mkExtension
        ; getExtension
        ; takeExtension
        ; takeExtensions
        ; replaceExtension
        ; replaceExtensions
        ; dropExtension
        ; dropExtensions
        ; addExtension
        ; hasExtension
        ; takeFileName
        ; replaceFileName
        ; dropFileName
        ; takeBaseName
        ; replaceBaseName
        ; takeDirectory
        ; replaceDirectory
        ; combine
        ; splitPath
        ; joinPath
        ; splitDirectories
        ; normalise
        )
  public

splitExtension  : FilePath → FilePath × Extension
splitExtension = coerce Prim.splitExtension

splitExtensions : FilePath → FilePath × Extension
splitExtensions = coerce Prim.splitExtensions

stripExtension : Extension → FilePath → Maybe FilePath
stripExtension = coerce Prim.stripExtension

splitFileName : FilePath → FilePath × FilePath
splitFileName = coerce Prim.splitFileName
