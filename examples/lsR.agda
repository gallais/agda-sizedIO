module lsR where

open import Level
open import Size
open import Data.Unit
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base
open import Data.Product
open import Data.String.Base
open import Data.String.Extras
open import Codata.IO
open import Codata.Thunk
open import Function
open import System.Environment
open import System.FilePath.Posix
open import System.Directory
open import System.Directory.Tree

printTree : ∀ {i} → String → List (IO′ 0ℓ RelativeTree i) → IO′ 0ℓ ⊤ i
printTree pad []           = pure _
printTree pad (iot ∷ iots) = iot >>=ᵗ λ where
  (dir ∋ fs :< ds) .force → do
    putStrLn (pad ++ getFilePath dir)
    let pad′ = "  " ++ pad
    ListIO.mapM′ (λ fp → putStrLn (pad′ ++ getFilePath fp)) fs
    let ds = List.map ((tree# <$>_) ∘′ proj₂) ds
    printTree pad′ ds
    printTree pad iots

usage : IO 0ℓ _
usage = putStrLn "Requires one argument: root filepath"

main = run $ do
  (fp ∷ []) ← getArgs where _ → usage
  let dtree = tree =<< makeAbsolute (mkFilePath fp)
  printTree "" (dtree ∷ [])
