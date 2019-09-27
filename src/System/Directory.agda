module System.Directory where

open import Level
open import Codata.IO
open import Data.Unit
open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.String.Base
open import Foreign.Haskell.Coerce
open import Function
open import System.FilePath.Posix

open import System.Directory.Primitive as Prim
  using ( XdgDirectory
        ; XdgData
        ; XdgConfig
        ; XdgCache
        ; XdgDirectoryList
        ; XdgDataDirs
        ; XdgConfigDirs
        ; exeExtension
        ) public

variable
  ℓ  : Level
  m n : Nature

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
getXdgDirectory           : XdgDirectory → RelativePath → IO ℓ AbsolutePath
getXdgDirectoryList       : XdgDirectoryList → IO ℓ (List AbsolutePath)
getAppUserDataDirectory   : RelativePath → IO ℓ AbsolutePath
getUserDocumentsDirectory : IO ℓ AbsolutePath
getTemporaryDirectory     : IO ℓ AbsolutePath

-- Action on files
removeFile           : FilePath m → IO ℓ ⊤
renameFile           : FilePath m → FilePath n → IO ℓ ⊤
renamePath           : FilePath m → FilePath n → IO ℓ ⊤
copyFile             : FilePath m → FilePath n → IO ℓ ⊤
copyFileWithMetadata : FilePath m → FilePath n → IO ℓ ⊤
getFileSize          : FilePath n → IO ℓ ℕ
canonicalizePath     : FilePath n → IO ℓ AbsolutePath
makeAbsolute         : FilePath n → IO ℓ AbsolutePath
makeRelative         : FilePath n → IO ℓ RelativePath

toKnownNature : KnownNature m → FilePath n → IO ℓ (FilePath m)
toKnownNature absolute = makeAbsolute
toKnownNature relative = makeRelative

relativeToKnownNature : KnownNature n → RelativePath → IO ℓ (FilePath n)
absoluteToKnownNature : KnownNature n → AbsolutePath → IO ℓ (FilePath n)

relativeToKnownNature absolute = makeAbsolute
relativeToKnownNature relative = pure

absoluteToKnownNature absolute = pure
absoluteToKnownNature relative = makeRelative

-- Existence tests

doesPathExist                : FilePath n -> IO ℓ Bool
doesFileExist                : FilePath n -> IO ℓ Bool
doesDirectoryExist           : FilePath n -> IO ℓ Bool
findExecutable               : String → IO ℓ (Maybe AbsolutePath)
findExecutables              : String → IO ℓ (List AbsolutePath)
findExecutablesInDirectories : List (FilePath n) → String → IO ℓ (List (FilePath n))
findFile                     : List (FilePath n) → String → IO ℓ (Maybe (FilePath n))
findFiles                    : List (FilePath n) → String → IO ℓ (List (FilePath n))
findFileWith                 : (FilePath n → IO ℓ Bool) → List (FilePath n) → String → IO ℓ (Maybe (FilePath n))
findFilesWith                : (FilePath n → IO ℓ Bool) → List (FilePath n) → String → IO ℓ (List (FilePath n))

createDirectory          = lift ∘′ Prim.createDirectory
createDirectoryIfMissing = λ b → lift ∘′ Prim.createDirectoryIfMissing b
removeDirectory          = lift ∘′ Prim.removeDirectory
removeDirectoryRecursive = lift ∘′ Prim.removeDirectoryRecursive
removePathForcibly       = lift ∘′ Prim.removePathForcibly
renameDirectory          = λ fp → lift ∘′ Prim.renameDirectory fp
listDirectory            = lift ∘′ Prim.listDirectory
getDirectoryContents     = lift ∘′ Prim.getDirectoryContents

getCurrentDirectory  = lift Prim.getCurrentDirectory
setCurrentDirectory  = lift ∘′ Prim.setCurrentDirectory
withCurrentDirectory = λ fp ma → lift (Prim.withCurrentDirectory fp (run ma))

getHomeDirectory          = lift Prim.getHomeDirectory
getXdgDirectory           = λ d fp → lift (Prim.getXdgDirectory d fp)
getXdgDirectoryList       = lift ∘′ Prim.getXdgDirectoryList
getAppUserDataDirectory   = lift ∘′ Prim.getAppUserDataDirectory
getUserDocumentsDirectory = lift Prim.getUserDocumentsDirectory
getTemporaryDirectory     = lift Prim.getTemporaryDirectory

removeFile           = lift ∘′ Prim.removeFile
renameFile           = λ a b → lift (Prim.renameFile a b)
renamePath           = λ a b → lift (Prim.renamePath a b)
copyFile             = λ a b → lift (Prim.copyFile a b)
copyFileWithMetadata = λ a b → lift (Prim.copyFileWithMetadata a b)
getFileSize          = lift ∘′ Prim.getFileSize
canonicalizePath     = lift ∘′ Prim.canonicalizePath
makeAbsolute         = lift ∘′ Prim.makeAbsolute
makeRelative         = lift ∘′ Prim.makeRelativeToCurrentDirectory

doesPathExist                = lift ∘′ Prim.doesPathExist
doesFileExist                = lift ∘′ Prim.doesFileExist
doesDirectoryExist           = lift ∘′ Prim.doesDirectoryExist
findExecutable               = lift ∘′ coerce ∘′ Prim.findExecutable
findExecutables              = lift ∘′ Prim.findExecutables
findExecutablesInDirectories = λ fps str → lift (Prim.findExecutablesInDirectories fps str)
findFile                     = λ fps str → lift (coerce Prim.findFile fps str)
findFiles                    = λ fps str → lift (Prim.findFiles fps str)
findFileWith                 = λ p fps str → lift (coerce Prim.findFileWith (run ∘′ p) fps str)
findFilesWith                = λ p fps str → lift (Prim.findFilesWith (run ∘′ p) fps str)
