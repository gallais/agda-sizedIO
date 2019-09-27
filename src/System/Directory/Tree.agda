module System.Directory.Tree where

open import Level
open import Size

open import Codata.IO
open import Codata.Thunk
open import Data.Bool.Base
open import Data.List.Base as List
open import Data.Product as Prod
open import Data.Sum.Base
open import Function
open import System.Directory
open import System.FilePath.Posix

{-# NO_UNIVERSE_CHECK #-}
data Tree′ n (i : Size) : Set where
  _∋_:<_ :
    AbsolutePath →                               -- path to the root of the tree
    List (FilePath n) →                          -- list of files in it
    List (FilePath n × IO 0ℓ (Thunk (Tree′ n) i)) → -- trees for subdirectories
    Tree′ n i

Tree : Nature → Set
Tree n = Tree′ n _

AbsoluteTree : Set
AbsoluteTree = Tree Nature.absolute

RelativeTree : Set
RelativeTree = Tree Nature.relative

treeᵗ : ∀ {i} → KnownNature n → AbsolutePath → IO 0ℓ (Thunk (Tree′ n) i)
treeᵗ n fp = do
  -- set current directory: makeAbsolute will now consider this
  -- to be the root
  setCurrentDirectory fp
  -- get content of the current directory
  vs ← listDirectory fp
  -- tag each filepath with whether it points to a directory
  bvs ← ListIO.forM vs $ λ fp → do
    fp   ← toKnownNature n fp
    true ← doesDirectoryExist fp where false → pure (inj₂ fp)
    inj₁ ∘′ (fp ,_) <$> makeAbsolute fp
  -- partition into a list ds of directories and one fs of files
  let (ds , fs) = partitionSums bvs
  -- return the files together with the ability to further explore the tree
  pure (λ where .force → fp ∋ fs :< List.map (Prod.map₂ (treeᵗ n)) ds)

tree# : Thunk (Tree′ n) ∞ → Tree n
tree# t = t .force

tree : {{KnownNature n}} → AbsolutePath → IO 0ℓ (Tree n)
tree {{n}} fp = tree# <$> treeᵗ n fp
