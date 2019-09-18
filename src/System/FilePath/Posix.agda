module System.FilePath.Posix where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Maybe.Base
open import Data.Product
open import Data.Sum.Base
open import Function

open import Foreign.Haskell.Coerce

open import System.FilePath.Posix.Primitive as Prim
  using ( Nature
        ; absolute
        ; relative
        ; FilePath
        ; mkFilePath
        ; getFilePath
        ; AbsolutePath
        ; RelativePath
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
        ; isRelative
        ; isAbsolute
        )
  public

private
  variable
    m n : Nature

splitExtension  : ∀ {n} → FilePath n → FilePath n × Extension
splitExtension = coerce Prim.splitExtension

splitExtensions : ∀ {n} → FilePath n → FilePath n × Extension
splitExtensions = coerce Prim.splitExtensions

stripExtension : ∀ {n} → Extension → FilePath n → Maybe (FilePath n)
stripExtension = coerce Prim.stripExtension

splitFileName : ∀ {n} → FilePath n → FilePath n × RelativePath
splitFileName = coerce Prim.splitFileName
