module Codata.IO where

import IO.Primitive as Prim
open import Agda.Builtin.Unit
open import Foreign.Haskell.Extras

Main : Set
Main = Prim.IO ⊤

open import Level
open import Size
open import Codata.Thunk using (Thunk; force)
open import Agda.Builtin.Equality
open import Data.Maybe.Base using (Maybe)
open import Function

_≤ˡ_ : Level → Level → Set
a ≤ˡ b = a ⊔ b ≡ b

instance
  a≤a : ∀ {a} → a ≤ˡ a
  a≤a = refl

{-# NO_UNIVERSE_CHECK #-}
data IO′ {a} (i : Size) (ℓ : Level) (A : Set a) : Set (suc ℓ) where
  lift   : {{eq : a ≤ˡ ℓ}} → Prim.IO {a} A → IO′ i ℓ A
  return : {{eq : a ≤ˡ ℓ}} → A → IO′ i ℓ A
  bind   : ∀ {b} {B : Set b} →
           Thunk (λ i → IO′ i ℓ B) i →
           (B → Thunk (λ i → IO′ i ℓ A) i) → IO′ i ℓ A


IO : ∀ {a} (ℓ : Level) → Set a → Set (suc ℓ)
IO = IO′ ∞

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b
    i : Size

map  : {B : Set b} {{_ : b ≤ˡ ℓ}} → (A → B) → IO′ i ℓ A → IO′ i ℓ B
map f (lift m)   = lift (m Prim.>>= λ a → Prim.return (f a))
map f (return a) = return (f a)
map f (bind m g) = bind m $ λ a → λ where .force → map f (g a .force)

infixr 1 _>>=_ _ᵗ>>=_ _>>=ᵗ_

_>>=_ : IO′ i ℓ A → (A → IO′ i ℓ B) → IO′ i ℓ B
m >>= f = bind (λ where .force → m) (λ a → λ where .force → f a)

_ᵗ>>=_ : Thunk (λ i → IO′ i ℓ A) i → (A → IO′ i ℓ B) → IO′ i ℓ B
m ᵗ>>= f = bind m (λ a → λ where .force → f a)

_>>=ᵗ_ : IO′ i ℓ A → (A → Thunk (λ i → IO′ i ℓ B) i) → IO′ i ℓ B
m >>=ᵗ f = bind (λ where .force → m) f

infixr 1 _>>_
infixl 1 _<<_ _<$_ _<$>_ _<*>_

_<$>_ : {B : Set b} {{_ : b ≤ˡ ℓ}} → (A → B) → IO′ i ℓ A → IO′ i ℓ B
f <$> m = m >>= λ a → return (f a)

_<$_ : {A : Set a} {{_ : a ≤ˡ ℓ}} → A → IO ℓ B → IO ℓ A
a <$ mb = mb >>= λ _ → return a

_<*>_ : {B : Set b} {{_ : b ≤ˡ ℓ}} → IO′ i ℓ (A → B) → IO′ i ℓ A → IO′ i ℓ B
f <*> m = f >>= (_<$> m)

_>>_ : IO ℓ A → IO ℓ B → IO ℓ B
ma >> mb = ma >>= λ _ → mb

_<<_ : {A : Set a} {{_ : a ≤ˡ ℓ}} → IO ℓ A → IO ℓ B → IO ℓ A
ma << mb = ma >>= λ a → a <$ mb

module ListIO where

  open import Data.List.Base as List using (List; []; _∷_)

  sequence : {A : Set a} {{_ : a ≤ˡ ℓ}} →
             List (IO ℓ A) → IO ℓ (List A)
  sequence []         = return []
  sequence (mx ∷ mxs) = mx           >>= λ x →
                        sequence mxs >>= λ xs →
                        return (x ∷ xs)

  module _ {B : Set b} {{_ : b ≤ˡ ℓ}} where

    mapM : (A → IO ℓ B) → List A → IO ℓ (List B)
    mapM f xs = sequence (List.map f xs)

    mapM′ : (A → IO ℓ B) → List A → IO ℓ ⊤
    mapM′ f xs = tt <$ mapM f xs

module ColistIO where

  open import Codata.Colist as Colist using (Colist; []; _∷_)

  sequence : {A : Set a} {{_ : a ≤ˡ ℓ}} →
             Colist (IO′ i ℓ A) ∞ → IO′ i ℓ (Colist A ∞)
  sequence []         = return []
  sequence (mx ∷ mxs) =
    mx                                        >>= λ x →
    (λ where .force → sequence (mxs .force)) ᵗ>>= λ xs →
    return (x ∷ λ where .force → xs)

  module _  {B : Set b} {{_ : b ≤ˡ ℓ}} where

    mapM : (A → IO ℓ B) → Colist A ∞ → IO ℓ (Colist B ∞)
    mapM f xs = sequence (Colist.map f xs)

    mapM′ : (A → IO ℓ B) → Colist A ∞ → IO ℓ ⊤
    mapM′ f xs = tt <$ mapM f xs

open import Agda.Builtin.Char
open import Data.String
open import Codata.Musical.Costring
open import System.FilePath.Posix
import Codata.IO.Primitive as Prim

open import Codata.IO.Types
  using ( BufferMode
        ; NoBuffering
        ; LineBuffering
        ; BlockBuffering
        )
  public
open import Codata.IO.Primitive
  using ( Handle
        ; stdin
        ; stdout
        ; stderr
        )
  public


hSetBuffering  : Handle → BufferMode → IO ℓ ⊤
hGetBuffering  : Handle → IO ℓ BufferMode
hFlush         : Handle → IO ℓ ⊤
interact       : (String → String) → IO ℓ ⊤
getChar        : IO ℓ Char
getLine        : IO ℓ String
getContents    : IO ℓ Costring
readFile       : FilePath → IO ℓ Costring
writeFile      : FilePath → Costring → IO ℓ ⊤
appendFile     : FilePath → Costring → IO ℓ ⊤
putChar        : Char → IO ℓ ⊤
putStr         : Costring → IO ℓ ⊤
putStrLn       : Costring → IO ℓ ⊤
readFiniteFile : FilePath → IO ℓ String

hSetBuffering h b = lift (Prim.hSetBuffering h (BufferMode.toForeign b))
hGetBuffering h = BufferMode.fromForeign <$> lift (Prim.hGetBuffering h)
hFlush         = λ h → lift (Prim.hFlush h)
interact       = λ f → lift (Prim.interact f)
getChar        = lift Prim.getChar
getLine        = lift Prim.getLine
getContents    = lift Prim.getContents
readFile       = λ fp → lift (Prim.readFile (getFilePath fp))
writeFile      = λ fp cstr → lift (Prim.writeFile (getFilePath fp) cstr)
appendFile     = λ fp cstr → lift (Prim.appendFile (getFilePath fp) cstr)
putChar        = λ c → lift (Prim.putChar c)
putStr         = λ cstr → lift (Prim.putStr cstr)
putStrLn       = λ cstr → lift (Prim.putStrLn cstr)
readFiniteFile = λ fp → lift (Prim.readFiniteFile (getFilePath fp))

{-# NON_TERMINATING #-}
run : IO ℓ A → Prim.IO A
run (lift io)  = io
run (return a) = Prim.return a
run (bind m f) = run (m .force) Prim.>>= λ a → run (f a .force)
