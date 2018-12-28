module cat where

open import Level
open import Foreign.Haskell
open import Codata.Colist
open import Codata.Musical.Colist using (fromMusical)
open import Function
open import Sized.IO
open import System.FilePath.Posix
open import System.Environment

cat : FilePath → IO zero Unit
cat fp = do
  cstr ← readFile fp
  ColistIO.mapM′ putChar (fromMusical cstr)

main = run $ do
  fps ← getArgs
  ListIO.mapM′ (cat ∘′ mkFilePath) fps