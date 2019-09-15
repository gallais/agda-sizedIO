{-# OPTIONS --without-K --sized-types --safe --cumulativity #-}

open import Level using (Level; suc; _⊔_)

module Codata.IO
  (F     : ∀ l → Set l → Set l)
  (liftF : ∀ {l A} l' → F l A → F (l ⊔ l') A)
  (mapF  : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → F a A → F b B)
  where

open import Size
open import Codata.Thunk using (Thunk; force)
open import Agda.Builtin.Equality
open import Data.Maybe.Base using (Maybe)
open import Function

data IO′ (l : Level) (A : Set l) (i : Size) : Set (suc l) where
  action : F l A → IO′ l A i
  return : A → IO′ l A i
  bind   : ∀ (B : Set l) → Thunk (IO′ l B) i → (B → Thunk (IO′ l A) i) → IO′ l A i

lift′ : ∀ {i l A} l' → IO′ l A i → IO′ (l ⊔ l') A i
lift′ l' (action x) = action (liftF l' x)
lift′ l' (return a) = return a
lift′ l' (bind B m f) =
  bind B (λ where .force → lift′ l' (m .force)) λ b →
         (λ where .force → lift′ l' (f b .force))

IO : (l : Level) → Set l → Set (suc l)
IO l A = IO′ l A ∞

module _ {a b} {A : Set a} {B : Set b} where

  map : ∀ {i} → (A → B) → IO′ a A i → IO′ (a ⊔ b) B i
  map f (action x) = action (mapF f x)
  map f (return a) = return (f a)
  map f (bind B m g) =
    bind B (λ where .force → lift′ b (m .force)) λ b →
           (λ where .force → map f (g b .force))

  infixr 1 _>>=_ _ᵗ>>=_ _>>=ᵗ_

  _>>=_ : ∀ {i} → IO′ a A i → (A → IO′ b B i) → IO′ (a ⊔ b) B i
  m >>= f = bind A (λ where .force → lift′ b m) (λ x → λ where .force → lift′ a (f x))

  _ᵗ>>=_ : ∀ {i} → Thunk {ℓ = suc a} (IO′ a A) i → (A → IO′ b B i) → IO′ (a ⊔ b) B i
  m ᵗ>>= f = bind A (λ where .force → lift′ b (m .force)) (λ x → λ where .force → lift′ a (f x))

  _>>=ᵗ_ : ∀ {i} → IO′ a A i → (A → Thunk {ℓ = suc b} (IO′ b B) i) → IO′ (a ⊔ b) B i
  m >>=ᵗ f = bind A (λ where .force → lift′ b m) λ x → λ where .force → lift′ a (f x .force)

{-
infixr 1 _>>_
infixl 1 _<<_ _<$_ _<$>_ _<*>_

_<$>_ : {B : Set b} {{_ : b ≤ˡ l}} → (A → B) → IO′ i l A → IO′ i l B
f <$> m = m >>= λ a → return (f a)

_<$_ : {A : Set a} {{_ : a ≤ˡ l}} → A → IO l B → IO l A
a <$ mb = mb >>= λ _ → return a

_<*>_ : {B : Set b} {{_ : b ≤ˡ l}} → IO′ i l (A → B) → IO′ i l A → IO′ i l B
f <*> m = f >>= (_<$> m)

_>>_ : IO l A → IO l B → IO l B
ma >> mb = ma >>= λ _ → mb

_<<_ : {A : Set a} {{_ : a ≤ˡ l}} → IO l A → IO l B → IO l A
ma << mb = ma >>= λ a → a <$ mb

module ListIO where

  open import Data.List.Base as List using (List; []; _∷_)

  sequence : {A : Set a} {{_ : a ≤ˡ l}} →
             List (IO l A) → IO l (List A)
  sequence []         = return []
  sequence (mx ∷ mxs) = mx           >>= λ x →
                        sequence mxs >>= λ xs →
                        return (x ∷ xs)

  module _ {B : Set b} {{_ : b ≤ˡ l}} where

    mapM : (A → IO l B) → List A → IO l (List B)
    mapM f xs = sequence (List.map f xs)

    mapM′ : (A → IO l B) → List A → IO l ⊤
    mapM′ f xs = tt <$ mapM f xs

module ColistIO where

  open import Codata.Colist as Colist using (Colist; []; _∷_)

  sequence : {A : Set a} {{_ : a ≤ˡ l}} →
             Colist (IO′ i l A) ∞ → IO′ i l (Colist A ∞)
  sequence []         = return []
  sequence (mx ∷ mxs) =
    mx                                        >>= λ x →
    (λ where .force → sequence (mxs .force)) ᵗ>>= λ xs →
    return (x ∷ λ where .force → xs)

  module _  {B : Set b} {{_ : b ≤ˡ l}} where

    mapM : (A → IO l B) → Colist A ∞ → IO l (Colist B ∞)
    mapM f xs = sequence (Colist.map f xs)

    mapM′ : (A → IO l B) → Colist A ∞ → IO l ⊤
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
-}
