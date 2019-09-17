module Codata.IO where

import IO.Primitive as Prim
open import Codata.IO.Types hiding (module FFI) public
open import Agda.Builtin.Unit

Main : Set
Main = Prim.IO ⊤

open import Level
open import Size
open import Codata.Thunk using (Thunk; force)
open import Agda.Builtin.Equality
open import Data.Maybe.Base using (Maybe)
open import Function
open import Foreign.Haskell.Coerce

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

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b
    i : Size

map  : {B : Set b} {{_ : b ≤ˡ ℓ}} → (A → B) → IO′ ℓ A i → IO′ ℓ B i
map f (lift m)   = lift (m Prim.>>= λ a → Prim.return (f a))
map f (return a) = return (f a)
map f (bind m g) = bind m $ λ a → λ where .force → map f (g a .force)

delay : {A : Set a} {{_ : a ≤ˡ ℓ}} → Thunk (IO′ ℓ A) i → IO′ ℓ A i
delay m = bind m λ a → λ where .force → return a

infixr 1 _>>=_ _ᵗ>>=_ _>>=ᵗ_

_>>=_ : IO′ ℓ A i → (A → IO′ ℓ B i) → IO′ ℓ B i
m >>= f = bind (λ where .force → m) (λ a → λ where .force → f a)

_=<<_ : (A → IO′ ℓ B i) → IO′ ℓ A i → IO′ ℓ B i
f =<< m = m >>= f

_ᵗ>>=_ : Thunk (IO′ ℓ A) i → (A → IO′ ℓ B i) → IO′ ℓ B i
m ᵗ>>= f = bind m (λ a → λ where .force → f a)

_>>=ᵗ_ : IO′ ℓ A i → (A → Thunk (IO′ ℓ B) i) → IO′ ℓ B i
m >>=ᵗ f = bind (λ where .force → m) f

infixr 1 _>>_
infixl 1 _<<_ _<$_ _<$>_ _<*>_

_<$>_ : {B : Set b} {{_ : b ≤ˡ ℓ}} → (A → B) → IO′ ℓ A i → IO′ ℓ B i
f <$> m = m >>= λ a → return (f a)

_<$_ : {A : Set a} {{_ : a ≤ˡ ℓ}} → A → IO′ ℓ B i → IO′ ℓ A i
a <$ mb = mb >>= λ _ → return a

_<*>_ : {B : Set b} {{_ : b ≤ˡ ℓ}} → IO′ ℓ (A → B) i → IO′ ℓ A i → IO′ ℓ B i
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

    forM : List A → (A → IO ℓ B) → IO ℓ (List B)
    forM  = flip mapM

    forM′ : List A → (A → IO ℓ B) → IO ℓ ⊤
    forM′ = flip mapM′

module ColistIO where

  open import Codata.Colist as Colist using (Colist; []; _∷_)

  sequence : {A : Set a} {{_ : a ≤ˡ ℓ}} →
             Colist (IO′ ℓ A i) ∞ → IO′ ℓ (Colist A ∞) i
  sequence []         = return []
  sequence (mx ∷ mxs) =
    mx                                        >>= λ x →
    (λ where .force → sequence (mxs .force)) ᵗ>>= λ xs →
    return (x ∷ λ where .force → xs)

  module _  {B : Set b} {{_ : b ≤ˡ ℓ}} where

    mapM : (A → IO′ ℓ B i) → Colist A ∞ → IO′ ℓ (Colist B ∞) i
    mapM f xs = sequence (Colist.map f xs)

    mapM′ : (A → IO′ ℓ B i) → Colist A ∞ → IO′ ℓ ⊤ i
    mapM′ f xs = tt <$ mapM f xs

    forM : Colist A ∞ → (A → IO′ ℓ B i) → IO′ ℓ (Colist B ∞) i
    forM  = flip mapM

    forM′ : Colist A ∞ → (A → IO′ ℓ B i) → IO′ ℓ ⊤ i
    forM′ = flip mapM′

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
putCoStr       : Costring → IO ℓ ⊤
putCoStrLn     : Costring → IO ℓ ⊤
putStr         : String → IO ℓ ⊤
putStrLn       : String → IO ℓ ⊤
readFiniteFile : FilePath → IO ℓ String

hSetBuffering h b = lift (coerce Prim.hSetBuffering h b)
hGetBuffering h   = coerce <$> lift (Prim.hGetBuffering h)
hFlush            = λ h → lift (Prim.hFlush h)
interact          = λ f → lift (Prim.interact f)
getChar           = lift Prim.getChar
getLine           = lift Prim.getLine
getContents       = lift Prim.getContents
readFile          = λ fp → lift (Prim.readFile (getFilePath fp))
writeFile         = λ fp cstr → lift (Prim.writeFile (getFilePath fp) cstr)
appendFile        = λ fp cstr → lift (Prim.appendFile (getFilePath fp) cstr)
putChar           = λ c → lift (Prim.putChar c)
putCoStr          = λ cstr → lift (Prim.putStr cstr)
putCoStrLn        = λ cstr → lift (Prim.putStrLn cstr)
putStr            = putCoStr ∘′ toCostring
putStrLn          = putCoStrLn ∘′ toCostring
readFiniteFile    = λ fp → lift (Prim.readFiniteFile (getFilePath fp))

{-# NON_TERMINATING #-}
run : IO ℓ A → Prim.IO A
run (lift io)  = io
run (return a) = Prim.return a
run (bind m f) = run (m .force) Prim.>>= λ a → run (f a .force)
