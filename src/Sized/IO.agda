module Sized.IO where

import IO.Primitive as Prim

open import Level
open import Size

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

module _ {a} {A B : Set a} where

 map  : ∀ {i} → (A → B) → IO′ i A → IO′ i B
 ∞map : ∀ {i} → (A → B) → ∞IO′ i A → ∞IO′ i B

 map f (lift m)   = lift (m Prim.>>= λ a → Prim.return (f a))
 map f (return a) = return (f a)
 map f (bind m g) = bind m (λ a → ∞map f (g a))
 ∞IO′.force (∞map f io) = map f (∞IO′.force io)

 infixl 1 _>>=_

 _>>=_ : IO A → (A → IO B) → IO B
 m >>= f = bind (delay m) (λ a → delay (f a))

module _ {a} {A B : Set a} where

 infixl 1 _>>_ _<<_ _<$_

 _<$_ : A → IO B → IO A
 a <$ mb = mb >>= λ _ → return a 

 _>>_ : IO A → IO B → IO B
 ma >> mb = ma >>= λ _ → mb

 _<<_ : IO A → IO B → IO A
 ma << mb = ma >>= λ a → a <$ mb

open import Data.String
open import System.FilePath.Posix
open import Foreign.Haskell

getContents    : IO Costring
readFile       : FilePath → IO Costring
writeFile      : FilePath → Costring → IO Unit
appendFile     : FilePath → Costring → IO Unit
putStr         : Costring → IO Unit
putStrLn       : Costring → IO Unit
readFiniteFile : FilePath → IO String

getContents    = lift Prim.getContents
readFile       = λ fp → lift (Prim.readFile (getFilePath fp))
writeFile      = λ fp cstr → lift (Prim.writeFile (getFilePath fp) cstr)
appendFile     = λ fp cstr → lift (Prim.appendFile (getFilePath fp) cstr)
putStr         = λ cstr → lift (Prim.putStr cstr)
putStrLn       = λ cstr → lift (Prim.putStrLn cstr)
readFiniteFile = λ fp → lift (Prim.readFiniteFile (getFilePath fp))

{-# NON_TERMINATING #-}
run : ∀ {a} {A : Set a} → IO A → Prim.IO A
run (lift io)  = io
run (return a) = Prim.return a
run (bind m f) = run (∞IO′.force m) Prim.>>= λ a → run (∞IO′.force (f a))
