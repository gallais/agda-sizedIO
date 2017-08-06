module Sized.Conat where

open import Size

data    Conat′ (i : Size) : Set
record ∞Conat′ (i : Size) : Set

data Conat′ i where
  zero : Conat′ i
  suc  : ∞Conat′ i → Conat′ i

record ∞Conat′ i where
  coinductive
  constructor delay
  field force : {j : Size< i} → Conat′ j

Conat : Set
Conat = Conat′ ∞

∞Conat : Set
∞Conat = ∞Conat′ ∞

_+_  : ∀ {i} → Conat′ i → Conat′ i → Conat′ i
_∞+_ : ∀ {i} → ∞Conat′ i → Conat′ i → ∞Conat′ i

zero  + n = n
suc m + n = suc (m ∞+ n)
∞Conat′.force (m ∞+ n) = ∞Conat′.force m + n

_⊓_  : ∀ {i} → Conat′ i → Conat′ i → Conat′ i
_∞⊓_ : ∀ {i} → ∞Conat′ i → ∞Conat′ i → ∞Conat′ i

zero  ⊓ n     = zero
m     ⊓ zero  = zero
suc m ⊓ suc n = suc (m ∞⊓ n)
∞Conat′.force (m ∞⊓ n) = ∞Conat′.force m ⊓ ∞Conat′.force n


_⊔_  : ∀ {i} → Conat′ i → Conat′ i → Conat′ i
_∞⊔_ : ∀ {i} → ∞Conat′ i → ∞Conat′ i → ∞Conat′ i

zero  ⊔ n     = n
m     ⊔ zero  = m
suc m ⊔ suc n = suc (m ∞⊔ n)
∞Conat′.force (m ∞⊔ n) = ∞Conat′.force m ⊔ ∞Conat′.force n

data   _≈_  {i} : (m n : Conat′ i) → Set
record _∞≈_ {i} (m n : ∞Conat′ i) : Set

data _≈_ {i} where
  zero : zero {i} ≈ zero
  suc  : ∀ {m n : ∞Conat′ i} → m ∞≈ n → suc m ≈ suc n

record _∞≈_ {i} m n where
  coinductive
  constructor delay
  field force : {j : Size< i} → ∞Conat′.force m {j} ≈ ∞Conat′.force n

module ≈ where

  refl  : ∀ {i} {m : Conat′ i} → m ≈ m
  ∞refl : ∀ {i} {m : ∞Conat′ i} → m ∞≈ m

  refl {m = zero}  = zero
  refl {m = suc m} = suc ∞refl
  _∞≈_.force ∞refl = refl

  sym  : ∀ {i} {m n : Conat′ i} → m ≈ n → n ≈ m
  ∞sym : ∀ {i} {m n : ∞Conat′ i} → m ∞≈ n → n ∞≈ m

  sym zero    = zero
  sym (suc p) = suc (∞sym p)
  _∞≈_.force (∞sym p) = sym (_∞≈_.force p)

  trans  : ∀ {i} {m n p : Conat′ i} → m ≈ n → n ≈ p → m ≈ p
  ∞trans : ∀ {i} {m n p : ∞Conat′ i} → m ∞≈ n → n ∞≈ p → m ∞≈ p

  trans zero    zero    = zero
  trans (suc p) (suc q) = suc (∞trans p q)
  _∞≈_.force (∞trans p q) = trans (_∞≈_.force p) (_∞≈_.force q)


data   _≤_  {i} : (m n : Conat′ i) → Set
record _∞≤_ {i} (m n : ∞Conat′ i) : Set

data _≤_ {i} where
  z≤n : ∀ {m : Conat′ i} → zero ≤ m
  s≤s : ∀ {m n : ∞Conat′ i} → m ∞≤ n → suc m ≤ suc n

record _∞≤_ {i} m n where
  coinductive
  constructor delay
  field force : {j : Size< i} → ∞Conat′.force m {j} ≤ ∞Conat′.force n

module ≤ where

  refl  : ∀ {i} {m : Conat′ i} → m ≤ m
  ∞refl : ∀ {i} {m : ∞Conat′ i} → m ∞≤ m

  refl {m = zero}  = z≤n
  refl {m = suc m} = s≤s ∞refl
  _∞≤_.force ∞refl = refl


  antisym  : ∀ {i} {m n : Conat′ i} → m ≤ n → n ≤ m → m ≈ n
  ∞antisym : ∀ {i} {m n : ∞Conat′ i} → m ∞≤ n → n ∞≤ m → m ∞≈ n

  antisym z≤n     z≤n     = zero
  antisym (s≤s p) (s≤s q) = suc (∞antisym p q)
  _∞≈_.force (∞antisym p q) = antisym (_∞≤_.force p) (_∞≤_.force q)

  trans  : ∀ {i} {m n p : Conat′ i} → m ≤ n → n ≤ p → m ≤ p
  ∞trans : ∀ {i} {m n p : ∞Conat′ i} → m ∞≤ n → n ∞≤ p → m ∞≤ p

  trans z≤n     _       = z≤n
  trans (s≤s p) (s≤s q) = s≤s (∞trans p q)
  _∞≤_.force (∞trans p q) = trans (_∞≤_.force p) (_∞≤_.force q)
