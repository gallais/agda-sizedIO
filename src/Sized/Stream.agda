module Sized.Stream where

open import Size
open import Function
open import Data.Product hiding (map)

record Stream′ {a} (i : Size) (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field head : A
        tail : {j : Size< i} → Stream′ j A

Stream : ∀ {a} → Set a → Set a
Stream = Stream′ ∞

module _ {a b} {A : Set a} {B : Set b} where

 map : ∀ {i} → (A → B) → Stream′ i A → Stream′ i B
 Stream′.head (map f xs) = f (Stream′.head xs)
 Stream′.tail (map f xs) = map f (Stream′.tail xs)

 unfold : (A → B × A) → A → Stream B
 Stream′.head (unfold step seed) = proj₁ (step seed)
 Stream′.tail (unfold step seed) = unfold step (proj₂ $ step seed)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 zipWith : ∀ {i} → (A → B → C) → Stream′ i A → Stream′ i B → Stream′ i C
 Stream′.head (zipWith f xs ys) = f (Stream′.head xs) (Stream′.head ys)
 Stream′.tail (zipWith f xs ys) = zipWith f (Stream′.tail xs) (Stream′.tail ys)

module Finite {a} {A : Set a} where

  open import Data.Nat.Base
  open import Data.Vec hiding (take)

  take : (n : ℕ) → Stream A → Vec A n
  take zero    xs = []
  take (suc n) xs = Stream′.head xs ∷ take n (Stream′.tail xs)

module Cofinite {a} {A : Set a} where

  open import Sized.Conat
  open import Sized.Colist hiding (take)

  take  : ∀ {i} (n : Conat′ i) → Stream′ i A → Colist′ i A
  ∞take : ∀ {i} (n : ∞Conat′ i) → Stream′ i A → ∞Colist′ i A

  take zero    xs = []
  take (suc n) xs = Stream′.head xs ∷ ∞take n xs
  ∞Colist′.force (∞take n xs) = take (∞Conat′.force n) (Stream′.tail xs)
