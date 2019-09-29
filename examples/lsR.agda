module lsR where

open import Level
open import Size
open import Data.Bool
open import Data.Unit
open import Data.List.Base as List using (List; []; _∷_; _∷ʳ_)
open import Data.Nat.Base
open import Data.Nat.GeneralisedArithmetic as ℕ
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

padding : Bool → List Bool → String
padding dir? []       = ""
padding dir? (b ∷ bs) =
  (if dir? ∧ List.null bs
   then if b then " ├ " else " └ "
   else if b then " │"  else "  ")
  ++ padding dir? bs

prefixes : ℕ → List Bool
prefixes n = List.replicate (n ∸ 1) true ∷ʳ false

printTree : ∀ {i} → List (List Bool × IO′ 0ℓ RelativeTree i) → IO′ 0ℓ ⊤ i
printTree []                  = pure _
printTree ((bs , iot) ∷ iots) = iot >>=ᵗ λ where
  (dir ∋ fs :< ds) .force → do
    let bs′ = List.reverse bs
    putStrLn (padding true bs′ ++ getFilePath dir)
    let pad = padding false bs′
    let pads = prefixes (List.length fs + List.length ds)
    ListIO.forM′ (List.zip pads fs) $ λ (b , fp) → do
      putStrLn (pad ++ (if b then " ├ " else " └ ") ++ getFilePath fp)
    let ds = List.map ((tree# <$>_) ∘′ proj₂) ds
    let bs = List.map (_∷ bs) (prefixes (List.length ds))
    printTree (List.zip bs ds)
    printTree iots

usage : IO 0ℓ _
usage = putStrLn "Requires one argument: root filepath"

main = run $ do
  (fp ∷ []) ← getArgs where _ → usage
  let dtree = tree =<< makeAbsolute (mkFilePath fp)
  printTree (([] , dtree) ∷ [])
