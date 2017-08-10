module Data.String.Extras where

open import Data.Char.Base
open import Data.String
open import Data.List.Base hiding (_++_)
open import Data.Nat

pad : Char → ℕ → String → String
pad c n str =
  let m = length (toList str)
  in fromList (replicate (n ∸ m) c)

padLeft : Char → ℕ → String → String
padLeft c n str = pad c n str ++ str

padRight : Char → ℕ → String → String
padRight c n str = str ++ pad c n str
