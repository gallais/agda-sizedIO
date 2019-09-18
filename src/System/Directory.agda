module System.Directory where

open import Level
open import Codata.IO
open import Data.Unit
open import Data.Bool.Base
open import Data.List.Base
open import Function
open import System.FilePath.Posix
import System.Directory.Primitive as Prim

variable
  ℓ  : Level
  n : Nature

-- Actions on directories

createDirectory           : FilePath n → IO ℓ ⊤
createDirectoryIfMissing  : Bool → FilePath n → IO ℓ ⊤
removeDirectory           : FilePath n → IO ℓ ⊤
removeDirectoryRecursive  : FilePath n → IO ℓ ⊤
removePathForcibly        : FilePath n → IO ℓ ⊤
renameDirectory           : FilePath n → FilePath n → IO ℓ ⊤
listDirectory             : FilePath n → IO ℓ (List RelativePath)

-- Current working directory

getDirectoryContents      : FilePath n → IO ℓ (List RelativePath)
getCurrentDirectory       : IO ℓ AbsolutePath
setCurrentDirectory       : FilePath n → IO ℓ ⊤
withCurrentDirectory      : ∀ {a} {A : Set a} → {{a ≤ˡ ℓ}} → FilePath n → IO ℓ A → IO ℓ A

-- Pre-defined directories

getHomeDirectory          : IO ℓ AbsolutePath
getUserDocumentsDirectory : IO ℓ AbsolutePath
getTemporaryDirectory     : IO ℓ AbsolutePath

-- Action on files

makeAbsolute : FilePath n → IO ℓ AbsolutePath

-- Existence tests

doesPathExist      : FilePath n -> IO ℓ Bool
doesFileExist      : FilePath n -> IO ℓ Bool
doesDirectoryExist : FilePath n -> IO ℓ Bool

createDirectory           = lift ∘′ Prim.createDirectory
createDirectoryIfMissing  = λ b → lift ∘′ Prim.createDirectoryIfMissing b
removeDirectory           = lift ∘′ Prim.removeDirectory
removeDirectoryRecursive  = lift ∘′ Prim.removeDirectoryRecursive
removePathForcibly        = lift ∘′ Prim.removePathForcibly
renameDirectory           = λ fp → lift ∘′ Prim.renameDirectory fp
listDirectory             = lift ∘′ Prim.listDirectory
getDirectoryContents      = lift ∘′ Prim.getDirectoryContents
getCurrentDirectory       = lift Prim.getCurrentDirectory
setCurrentDirectory       = lift ∘′ Prim.setCurrentDirectory
withCurrentDirectory      = λ fp ma → lift (Prim.withCurrentDirectory fp (run ma))
getHomeDirectory          = lift Prim.getHomeDirectory
getUserDocumentsDirectory = lift Prim.getUserDocumentsDirectory
getTemporaryDirectory     = lift Prim.getTemporaryDirectory
makeAbsolute              = lift ∘′ Prim.makeAbsolute
doesPathExist             = lift ∘′ Prim.doesPathExist
doesFileExist             = lift ∘′ Prim.doesFileExist
doesDirectoryExist        = lift ∘′ Prim.doesDirectoryExist
