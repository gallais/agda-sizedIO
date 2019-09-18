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

{-# NO_UNIVERSE_CHECK #-}
data Tree′ (i : Size) : Set where
  _∋_:<_ :
    AbsolutePath →                               -- path to the root of the tree
    List AbsolutePath →                          -- list of files in it
    List (AbsolutePath × IO 0ℓ (Thunk Tree′ i)) → -- trees for subdirectories
    Tree′ i

Tree : Set
Tree = Tree′ _

treeᵗ : ∀ {i} → AbsolutePath → IO 0ℓ (Thunk Tree′ i)
treeᵗ fp = do
  -- set current directory: makeAbsolute will now consider this
  -- to be the root
  setCurrentDirectory fp
  -- get content of the current directory and make paths absolute
  vs ← listDirectory fp
  vs ← ListIO.mapM makeAbsolute vs
  -- tag each file with whether it is a directory or not
  bvs ← ListIO.mapM (λ fp → _, fp <$> doesDirectoryExist fp) vs
  -- partition into a list ds of directories and one fs of files
  let (ds , fs) = partitionSumsWith (λ (b , a) → if b then inj₁ a else inj₂ a) bvs
  -- return the files together with the ability to further explore the tree
  pure (λ where .force → fp ∋ fs :< List.map (λ fp → fp , treeᵗ fp) ds)

tree# : Thunk Tree′ _ → Tree
tree# t = t .force

tree : AbsolutePath → IO 0ℓ Tree
tree fp = tree# <$> treeᵗ fp

-- @find str iots@ looks depth-first for a file with basename @str@ in the
-- list of subdirectories @iots@ left to process.

find : String → ∀ {i} → List (IO′ 0ℓ Tree i) → IO′ 0ℓ (Maybe AbsolutePath) i
find str []           = pure nothing
find str (iot ∷ iots) = iot >>=ᵗ λ where
  (_ ∋ fs :< ds) .force → do
    case List.filter ((str ≟_) ∘ takeBaseName) fs of λ where
      -- if we have found a suitable file in the current directory
      -- then we return it immediately
      (fp ∷ _) → pure (just fp)
      -- otherwise we look for it in its subdirectories. If we fail
      -- then we look at the next directory in the list.
      []       → do
        let ds = List.map ((tree# <$>_) ∘′ proj₂) ds
        nothing ← find str ds where fp@(just _) → pure fp
        find str iots

usage : IO 0ℓ _
usage = putStrLn "Requires two arguments: root filepath and target file name"

main = run $ do
  -- the user should call e.g. @find src/ Clock@
  (fp ∷ str ∷ []) ← getArgs where _ → usage
  let dtree = tree =<< makeAbsolute (mkFilePath fp)
  mfp ← find str (dtree ∷ [])
  case mfp of λ where
    nothing   → putStrLn $ "Could not find file with name " ++ str
    (just fp) → putStrLn $ "Found: " ++ getFilePath fp
