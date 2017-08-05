module Foreign.Haskell.Extras where

open import Level
open import Foreign.Haskell

data Pair {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  mkPair : A → B → Pair A B

{-# FOREIGN GHC type Pair a b = (,) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Foreign.Haskell.Extras.Pair ((,)) #-}

