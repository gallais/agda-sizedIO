module read where

open import Agda.Builtin.Unit
open import Level as L
open import Codata.IO
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.String
open import Codata.Musical.Costring
open import Data.Product
open import Function

data Type : Set → Set where
  N : Type ℕ
  B : Type Bool

readSet : ∀ {ℓ} → IO (L.suc ℓ) (∃ Type)
readSet = do
  str ← getLine
  return $ if str == "Nat" then -, N else -, B

record StringOf (T : Set) : Set where
  constructor mkStringOf
  field string : String

instance
  valueℕ : StringOf ℕ
  valueℕ = mkStringOf "0"

  valueBool : StringOf Bool
  valueBool = mkStringOf "true"

it : {X : Set} → {{_ : X}} → X
it {{x}} = x

dispatch : {S : Set} → Type S → StringOf S
dispatch N = it
dispatch B = it

read : IO (L.suc L.zero) ⊤
read = do
  (s , S) ← readSet
  let str = StringOf.string (dispatch S)
  putStrLn $ toCostring str

main : Main
main = run read
