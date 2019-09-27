module System.FilePath.Posix where

open import Level
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Codata.IO.Core
open import Data.Maybe.Base
open import Data.Product
open import Data.Sum.Base
open import Function

open import Foreign.Haskell.Coerce

private
  variable
    ℓ : Level

open import System.FilePath.Posix.Primitive as Prim
  using ( module Nature
        ; Nature
        ; FilePath
        ; mkFilePath
        ; getFilePath
        ; AbsolutePath
        ; RelativePath
        ; Extension
        ; mkExtension
        ; getExtension
     -- Separator predicates
        ; pathSeparator
        ; pathSeparators
        ; isPathSeparator
        ; searchPathSeparator
        ; isSearchPathSeparator
        ; extSeparator
        ; isExtSeparator
     -- $PATH methods
        ; splitSearchPath
     -- ; getSearchPath see below: lift needed
     -- Extension functions
     -- ; splitExtension see below: coerce needed
        ; takeExtension
        ; replaceExtension
        ; dropExtension
        ; addExtension
        ; hasExtension
        ; takeExtensions
        ; replaceExtensions
        ; dropExtensions
        ; isExtensionOf
     -- ; stripExtension see below: coerce needed
     -- Filename/directory functions
     -- ; splitFileName see below: coerce needed
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
      -- Trailing slash functions
        ; hasTrailingPathSeparator
        ; addTrailingPathSeparator
        ; dropTrailingPathSeparator
     -- File name manipulations
        ; normalise
        ; equalFilePath
        ; makeRelative
     -- ; checkFilePath see below: coerce neededc
        ; isRelative
        ; isAbsolute
        ; isValid
        ; makeValid
        ) public

private
  variable
    m n : Nature

-- singleton type for Nature
data KnownNature : Nature → Set where
  instance
    absolute : KnownNature Nature.absolute
    relative : KnownNature Nature.relative

splitExtension  : FilePath n → FilePath n × Extension
splitExtension = coerce Prim.splitExtension

splitExtensions : FilePath n → FilePath n × Extension
splitExtensions = coerce Prim.splitExtensions

stripExtension : Extension → FilePath n → Maybe (FilePath n)
stripExtension = coerce Prim.stripExtension

getSearchPath : IO ℓ (List (FilePath Nature.unknown))
getSearchPath = lift Prim.getSearchPath

splitFileName : FilePath n → FilePath n × RelativePath
splitFileName = coerce Prim.splitFileName

checkFilePath : FilePath n → RelativePath ⊎ AbsolutePath
checkFilePath = coerce Prim.checkFilePath
