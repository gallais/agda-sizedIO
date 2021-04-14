module lsR where

open import Level
open import Size
open import Data.Bool
open import Data.Unit
open import Data.List.Base as List using (List; []; _∷_; _∷ʳ_)
import Data.List.Categorical as List; open List.TraversableA
open import Data.Maybe.Base using (Maybe; nothing; just)
import Data.Maybe.Categorical as Maybe
open import Data.Nat.Base
open import Data.Product
open import Data.String.Base
open import Codata.IO
open import Codata.Thunk
open import Function
open import System.Environment
open import System.FilePath.Posix
open import System.Directory
open import System.Directory.Tree

padding : Bool → List Bool → String
padding dir? = concat ∘′ go [] where

  go : List String → List Bool → List String
  go acc []       = acc
  go acc (b ∷ bs) = go (hd ∷ acc) bs where

    hd : String
    hd = if dir? ∧ List.null acc
           then if b then " ├ " else " └ "
           else if b then " │"  else "  "

prefixes : ℕ → List Bool
prefixes n = List.replicate (n ∸ 1) true ∷ʳ false

printSubTrees : ∀ {i} → List (List Bool × IO′ 0ℓ (Tree n) i) → IO′ 0ℓ ⊤ i
printSubTrees []                  = pure _
printSubTrees ((bs , iot) ∷ iots) = iot >>=ᵗ λ where
  (dir ∋ fs :< ds) .force → do
    putStrLn padding true bs ++ getFilePath dir
    let pad = padding false bs
    let pads = prefixes (List.length fs + List.length ds)
    ListIO.forM′ (List.zip pads fs) $ λ (b , fp) → do
      putStrLn (pad ++ (if b then " ├ " else " └ ") ++ getFilePath fp)
    let ds = List.map ((tree# <$>_) ∘′ proj₂) ds
    let bs = List.map (_∷ bs) (prefixes (List.length ds))
    printSubTrees (List.zip bs ds)
    printSubTrees iots

printTree : Tree n → IO 0ℓ ⊤
printTree t = printSubTrees (([] , pure t) ∷ [])

printTreeAt : FilePath n → IO 0ℓ ⊤
printTreeAt fp = printTree =<< tree {{relative}} fp

usage : IO 0ℓ _
usage = putStrLn "Requires a non-empty list of paths to directories"

isDirectoryPath : String → IO ℓ (Maybe SomePath)
isDirectoryPath str = do
  let fp = mkFilePath str
  b ← doesDirectoryExist fp
  pure $ if b then just fp else nothing

main = run $ do
  -- make sure all the arguments passed are paths to directories
  fps ← ListIO.mapM isDirectoryPath =<< getArgs
  case sequenceA Maybe.applicative fps of λ where
    -- make sure at least one argument was passed
    (just fps@(_ ∷ _)) → ListIO.mapM′ printTreeAt fps
    _ → usage
