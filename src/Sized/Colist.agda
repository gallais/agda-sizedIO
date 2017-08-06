module Sized.Colist where

open import Size
open import Agda.Builtin.List
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Function

data    Colist′ {a} (i : Size) (A : Set a) : Set a
record ∞Colist′ {a} (i : Size) (A : Set a) : Set a

data Colist′ i A where
  []  : Colist′ i A
  _∷_ : A → ∞Colist′ i A → Colist′ i A

record ∞Colist′ i A where
  coinductive
  constructor delay
  field force : {j : Size< i} → Colist′ j A

Colist : ∀ {a} → Set a → Set a
Colist = Colist′ ∞ 

∞Colist : ∀ {a} → Set a → Set a
∞Colist = ∞Colist′ ∞ 

module _ {a} {A : Set a} where

 fromList : List A → Colist A
 fromList []       = []
 fromList (x ∷ xs) = x ∷ delay (fromList xs)

 open import Data.Nat
 open import Data.BoundedVec as BV using (BoundedVec)

 take : (n : ℕ) → Colist A → BoundedVec A n
 take 0       _        = BV.[]
 take n       []       = BV.[]
 take (suc n) (x ∷ xs) = x BV.∷ take n (∞Colist′.force xs)

 import Data.Colist as CL
 open CL using ([] ; _∷_)
 import Coinduction as CI

 fromLegacy  : ∀ {i} → CL.Colist A → Colist′ i A
 ∞fromLegacy : ∀ {i} → CI.∞ (CL.Colist A) → ∞Colist′ i A

 fromLegacy []       = []
 fromLegacy (x ∷ xs) = x ∷ ∞fromLegacy xs
 ∞Colist′.force (∞fromLegacy xs) = fromLegacy (CI.♭ xs)

 open import Sized.Conat

 colength  : ∀ {i} → Colist′ i A → Conat′ i
 ∞colength : ∀ {i} → ∞Colist′ i A → ∞Conat′ i

 colength []       = zero
 colength (x ∷ xs) = suc (∞colength xs)
 ∞Conat′.force (∞colength xs) {j} = colength (∞Colist′.force xs {j})

module _ {a b} {A : Set a} {B : Set b} where

 map  : ∀ {i} → (A → B) → Colist′ i A → Colist′ i B
 ∞map : ∀ {i} → (A → B) → ∞Colist′ i A → ∞Colist′ i B

 map f []        = []
 map f (x ∷ ∞xs) = f x ∷ ∞map f ∞xs
 ∞Colist′.force (∞map f ∞xs) = map f (∞Colist′.force ∞xs)

 unfold  : (A → Maybe (B × A)) → A → Colist B
 ∞unfold : (A → Maybe (B × A)) → A → ∞Colist B

 unfold step seed with step seed
 ... | nothing = []
 ... | just v  = proj₁ v ∷ ∞unfold step (proj₂ v)
 ∞Colist′.force (∞unfold step seed) = unfold step seed

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 zipWith  : ∀ {i} → (A → B → C) → Colist′ i A → Colist′ i B → Colist′ i C
 ∞zipWith : ∀ {i} → (A → B → C) → ∞Colist′ i A → ∞Colist′ i B → ∞Colist′ i C

 zipWith f []        ys        = []
 zipWith f xs        []        = []
 zipWith f (x ∷ ∞xs) (y ∷ ∞ys) = f x y ∷ ∞zipWith f ∞xs ∞ys
 ∞Colist′.force (∞zipWith f ∞xs ∞ys) = zipWith f (∞Colist′.force ∞xs) (∞Colist′.force ∞ys)

