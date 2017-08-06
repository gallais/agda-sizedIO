module Sized.Covec where

open import Size
open import Sized.Conat
open import Sized.Colist

data    Covec′ {a} (i : Size) (A : Set a) : Conat′ i → Set a
record ∞Covec′ {a} (i : Size) (A : Set a) (n : ∞Conat′ i) : Set a

data Covec′ i A where
  []  : Covec′ i A zero
  _∷_ : ∀ {n : ∞Conat′ i} → A → ∞Covec′ i A n → Covec′ i A (suc n)

record ∞Covec′ i A n where
  coinductive
  constructor delay
  field force : {j : Size< i} → Covec′ j A (∞Conat′.force n)

module _ {a} {A : Set a} where

 fromColist  : ∀ {i} (xs : Colist′ i A) → Covec′ i A (colength xs)
 ∞fromColist : ∀ {i} (xs : ∞Colist′ i A) → ∞Covec′ i A (∞colength xs)

 fromColist []       = []
 fromColist (x ∷ xs) = x ∷ ∞fromColist xs
 ∞Covec′.force (∞fromColist xs) = fromColist (∞Colist′.force xs)
