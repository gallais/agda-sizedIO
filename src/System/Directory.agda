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
  ℓ : Level

-- Actions on directories

createDirectory           : FilePath → IO ℓ ⊤
createDirectoryIfMissing  : Bool → FilePath → IO ℓ ⊤
removeDirectory           : FilePath → IO ℓ ⊤
removeDirectoryRecursive  : FilePath → IO ℓ ⊤
removePathForcibly        : FilePath → IO ℓ ⊤
renameDirectory           : FilePath → FilePath → IO ℓ ⊤
listDirectory             : FilePath → IO ℓ (List FilePath)

-- Current working directory

getDirectoryContents      : FilePath → IO ℓ (List FilePath)
getCurrentDirectory       : IO ℓ FilePath
setCurrentDirectory       : FilePath → IO ℓ ⊤
withCurrentDirectory      : ∀ {a} {A : Set a} → {{a ≤ˡ ℓ}} → FilePath → IO ℓ A → IO ℓ A

-- Pre-defined directories

getHomeDirectory          : IO ℓ FilePath
getUserDocumentsDirectory : IO ℓ FilePath
getTemporaryDirectory     : IO ℓ FilePath

-- Action on files

makeAbsolute : FilePath → IO ℓ FilePath

-- Existence tests

doesPathExist      : FilePath -> IO ℓ Bool
doesFileExist      : FilePath -> IO ℓ Bool
doesDirectoryExist : FilePath -> IO ℓ Bool

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
