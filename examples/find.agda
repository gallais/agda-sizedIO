module find where

open import Level
open import Size
open import Codata.IO
open import Codata.Thunk
open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base as List hiding (_++_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product
open import Data.String
open import Data.Sum.Base
open import Function
open import System.Environment
open import System.FilePath.Posix
open import System.Directory
open import System.Directory.Tree

-- @find str iots@ looks depth-first for a file with name @str@ in the
-- list of subdirectories @iots@ left to process.

find : String → ∀ {i} → List (IO′ 0ℓ RelativeTree i) → IO′ 0ℓ (Maybe AbsolutePath) i
find str []           = pure nothing
find str (iot ∷ iots) = iot >>=ᵗ λ where
  (dir ∋ fs :< ds) .force → do
    case List.filter ((str ≟_) ∘ getFilePath) fs of λ where
      -- if we have found a suitable file in the current directory
      -- then we return it immediately
      (fp ∷ _) → pure (just (combine dir fp))
      -- otherwise we look for it in its subdirectories. If we fail
      -- then we look at the next directory in the list.
      []       → do
        let ds = List.map ((tree# <$>_) ∘′ proj₂) ds
        nothing ← find str ds where fp@(just _) → pure fp
        find str iots

usage : IO 0ℓ _
usage = putStrLn "Requires two arguments: root filepath and target file name"

main = run $ do
  -- the user should call e.g. @find src/ Clock.agda@
  (fp ∷ str ∷ []) ← getArgs where _ → usage
  let dtree = tree =<< makeAbsolute (mkFilePath fp)
  mfp ← find str (dtree ∷ [])
  case mfp of λ where
    nothing   → putStrLn $ "Could not find file with name " ++ str
    (just fp) → putStrLn $ "Found: " ++ getFilePath fp
