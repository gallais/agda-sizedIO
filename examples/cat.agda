module cat where

open import Foreign.Haskell
open import Sized.Colist
open import Function
open import Sized.IO
open import System.FilePath.Posix
open import System.Environment

cat : FilePath → IO _
cat fp = readFile fp >>= λ cstr →
         ColistIO.mapM putChar (fromLegacy cstr)

main : Main
main = run $ getArgs >>= λ fps →
             unit <$ ListIO.mapM′ (cat ∘ mkFilePath) fps
