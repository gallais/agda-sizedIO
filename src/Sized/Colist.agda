module Sized.Colist where

open import Size
open import Agda.Builtin.List

data    Colist′ {a} (i : Size) (A : Set a) : Set a
record ∞Colist′ {a} (i : Size) (A : Set a) : Set a

data Colist′ i A where
  []  : Colist′ i A
  _∷_ : A → ∞Colist′ i A → Colist′ i A

record ∞Colist′ i A where
  coinductive
  constructor delay
  field force : {j : Size< i} → Colist′ i A

Colist : ∀ {a} → Set a → Set a
Colist = Colist′ ∞ 

∞Colist : ∀ {a} → Set a → Set a
∞Colist = ∞Colist′ ∞ 

fromList : ∀ {a} {A : Set a} → List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ delay (fromList xs)

map  : ∀ {i a b} {A : Set a} {B : Set b} →
       (A → B) → Colist′ i A → Colist′ i B
∞map : ∀ {i a b} {A : Set a} {B : Set b} →
       (A → B) → ∞Colist′ i A → ∞Colist′ i B

map f []        = []
map f (x ∷ ∞xs) = f x ∷ ∞map f ∞xs
∞Colist′.force (∞map f ∞xs) = map f (∞Colist′.force ∞xs)


import Data.Colist as CL
open CL using ([] ; _∷_)
import Coinduction as CI

fromLegacy  : ∀ {i a} {A : Set a} → CL.Colist A → Colist′ i A
∞fromLegacy : ∀ {i a} {A : Set a} → CI.∞ (CL.Colist A) → ∞Colist′ i A

fromLegacy []       = []
fromLegacy (x ∷ xs) = x ∷ ∞fromLegacy xs

∞Colist′.force (∞fromLegacy xs) = fromLegacy (CI.♭ xs)

zipWith  : ∀ {i a b c} {A : Set a} {B : Set b} {C : Set c} →
           (A → B → C) → Colist′ i A → Colist′ i B → Colist′ i C
∞zipWith : ∀ {i a b c} {A : Set a} {B : Set b} {C : Set c} →
           (A → B → C) → ∞Colist′ i A → ∞Colist′ i B → ∞Colist′ i C

zipWith f []        ys        = []
zipWith f xs        []        = []
zipWith f (x ∷ ∞xs) (y ∷ ∞ys) = f x y ∷ ∞zipWith f ∞xs ∞ys
∞Colist′.force (∞zipWith f ∞xs ∞ys) = zipWith f (∞Colist′.force ∞xs) (∞Colist′.force ∞ys)
