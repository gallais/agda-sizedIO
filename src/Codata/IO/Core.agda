module Codata.IO.Core where

open import Level
open import Size

open import Agda.Builtin.Equality
open import Codata.Thunk
import IO.Primitive as Prim

_≤ˡ_ : Level → Level → Set
a ≤ˡ b = a ⊔ b ≡ b

instance
  a≤a : ∀ {a} → a ≤ˡ a
  a≤a = refl

{-# NO_UNIVERSE_CHECK #-}
data IO′ {a} (ℓ : Level) (A : Set a) (i : Size) : Set (suc ℓ) where
  lift   : {{eq : a ≤ˡ ℓ}} → Prim.IO {a} A → IO′ ℓ A i
  return : {{eq : a ≤ˡ ℓ}} → A → IO′ ℓ A i
  bind   : ∀ {b} {B : Set b} →
           Thunk (IO′ ℓ B) i →
           (B → Thunk (IO′ ℓ A) i) → IO′ ℓ A i

pure : ∀ {a ℓ} {A : Set a} {i} → {{a ≤ˡ ℓ}} → A → IO′ ℓ A i
pure = return

IO : ∀ {a} (ℓ : Level) → Set a → Set (suc ℓ)
IO ℓ A = IO′ ℓ A ∞
