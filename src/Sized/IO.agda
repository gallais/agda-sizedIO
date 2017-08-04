module Sized.IO where

import IO.Primitive as Prim
open import Level
open import Size
open import Function

data    IO′ {a} (i : Size) (A : Set a) : Set (suc a)
record ∞IO′ {a} (i : Size) (A : Set a) : Set (suc a)

data IO′ {a} i A where
  lift   : Prim.IO A → IO′ i A
  return : A → IO′ i A
  bind   : {B : Set a} → ∞IO′ i B → (B → ∞IO′ i A) → IO′ i A

record ∞IO′ i A where
  coinductive
  constructor delay
  field force : {j : Size< i} → IO′ j A

IO : ∀ {a} → Set a → Set (suc a)
IO = IO′ ∞
∞IO : ∀ {a} → Set a → Set (suc a)
∞IO = ∞IO′ ∞

map  : ∀ {a i} {A B : Set a} → (A → B) → IO′ i A → IO′ i B
∞map : ∀ {a i} {A B : Set a} → (A → B) → ∞IO′ i A → ∞IO′ i B

map f (lift m)   = lift (m Prim.>>= Prim.return ∘′ f)
map f (return a) = return (f a)
map f (bind m g) = bind m (∞map f ∘′ g)
∞IO′.force (∞map f io) = map f (∞IO′.force io)

infixl 1 _>>=_ _>>_ _<<_
_>>=_ : ∀ {a} {A B : Set a} → IO A → (A → IO B) → IO B
m >>= f = bind (delay m) (λ a → delay (f a))

_>>_  : ∀ {a} {A B : Set a} → IO A → IO B → IO B
a >> b = a >>= λ _ → b

_<<_  : ∀ {a} {A B : Set a} → IO A → IO B → IO A
a << b = a >>= λ a → b >> return a
