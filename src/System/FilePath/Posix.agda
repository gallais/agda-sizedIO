module System.FilePath.Posix where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Maybe.Base
open import Data.Product
open import Function
open import Foreign.Haskell.Extras

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
splitExtension = Pair.fromForeign ∘′ Prim.splitExtension

splitExtensions : FilePath → FilePath × Extension
splitExtensions = Pair.fromForeign ∘′ Prim.splitExtensions

stripExtension : Extension → FilePath → Maybe FilePath
stripExtension ext fp = Maybe.fromForeign (Prim.stripExtension ext fp)

splitFileName : FilePath → FilePath × FilePath
splitFileName = Pair.fromForeign ∘′ Prim.splitFileName
