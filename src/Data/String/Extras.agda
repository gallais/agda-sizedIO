module Data.String.Extras where

open import Data.Char.Base
open import Data.String
open import Data.Nat

pad : Char → ℕ → String → String
pad c n str = replicate (n ∸ length str) c

padLeft : Char → ℕ → String → String
padLeft c n str = pad c n str ++ str

padRight : Char → ℕ → String → String
padRight c n str = str ++ pad c n str
