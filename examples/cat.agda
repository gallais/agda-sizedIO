module cat where

open import Foreign.Haskell
open import Agda.Builtin.List
open import Data.Char.Base
open import Data.String.Base
open import Data.Colist as C
open import Sized.Colist
open import Function
open import Sized.IO
open import System.FilePath.Posix
open import System.Environment

putChar : Char → IO _
putChar c = putStr (C.fromList (c ∷ []))

cat : FilePath → IO _
cat fp = readFile fp >>= λ cstr →
         ColistIO.mapM putChar (fromLegacy cstr)

main : _
main = run $ getArgs >>= λ fps →
             ListIO.mapM′ (cat ∘ mkFilePath) fps
