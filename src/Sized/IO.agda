module Sized.IO where

import IO.Primitive as Prim
open import Foreign.Haskell

Main : Set
Main = Prim.IO Unit

import IO
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

size<_  : ∀ {i a} {A : Set a} {j : Size< i} → IO′ i A → IO′ j A
∞size<_ : ∀ {i a} {A : Set a} {j : Size< i} → ∞IO′ i A → ∞IO′ j A

size< lift io  = lift io
size< return a = return a
size< bind m f = bind (∞size< m) (λ a → ∞size< (f a))

mkDelay : ∀ {i a} {A : Set a} → IO′ i A → ∞IO′ i A
∞IO′.force (mkDelay io) = size< io

∞IO′.force (∞size< m) = ∞IO′.force m

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

 infixr 1 _>>=_

 _>>=_ : ∀ {i} → IO′ i A → (A → IO′ i B) → IO′ i B
 m >>= f = bind (mkDelay m) (λ a → mkDelay (f a))

open import Data.List.Base as List

module _ {a} {A : Set a} where

module _ {a} {A B : Set a} where

 infixr 1 _>>_
 infixl 1 _<<_ _<$_ _<$>_ _<*>_

 _<$>_ : ∀ {i} → (A → B) → IO′ i A → IO′ i B
 f <$> m = bind (mkDelay m) (λ a → mkDelay (return (f a)))

 _<$_ : A → IO B → IO A
 a <$ mb = mb >>= λ _ → return a 

 _<*>_ : ∀ {i} → IO′ i (A → B) → IO′ i A → IO′ i B
 f <*> m = f >>= (_<$> m)

 _>>_ : IO A → IO B → IO B
 ma >> mb = ma >>= λ _ → mb

 _<<_ : IO A → IO B → IO A
 ma << mb = ma >>= λ a → a <$ mb

module ListIO where

 module _ {a} {A : Set a} where

  sequence : List (IO A) → IO (List A)
  sequence []         = return []
  sequence (mx ∷ mxs) = mx           >>= λ x →
                        sequence mxs >>= λ xs →
                        return (x ∷ xs)

 module _ {a} {A B : Set a} where

  mapM : (A → IO B) → List A → IO (List B)
  mapM f xs = sequence (List.map f xs)

  mapM′ : (A → IO B) → List A → IO (Lift Unit)
  mapM′ f xs = lift unit <$ mapM f xs

open import Sized.Colist as Colist
open import Coinduction

module ColistIO where

 module _ {a} {A : Set a} where

  sequence  : ∀ {i} → Colist (IO′ i A) → IO′ i (Colist A)
  ∞sequence : ∀ {i} → ∞Colist (IO′ i A) → ∞IO′ i (Colist A)

  sequence []         = return []
  sequence (mx ∷ mxs) = bind (mkDelay mx) $ λ x →
                        mkDelay $ bind (∞sequence mxs) $ λ xs →
                        mkDelay $ return (x ∷ delay xs)

  ∞IO′.force (∞sequence mxs) = sequence (∞Colist′.force mxs)

 module _ {a} {A B : Set a} where

  mapM : (A → IO B) → Colist A → IO (Colist B)
  mapM f xs = sequence (Colist.map f xs)

  mapM′ : (A → IO B) → Colist A → IO (Lift Unit)
  mapM′ f xs = lift unit <$ mapM f xs

open import Agda.Builtin.Char
open import Data.String
open import System.FilePath.Posix
import Sized.IO.Primitive as Prim
open import Sized.IO.Primitive
  using (BufferMode ; NoBuffering ; LineBuffering ; BlockBuffering ;
         Handle ; stdin ; stdout ; stderr)
  public

hSetBuffering  : Handle → BufferMode → IO Unit
hGetBuffering  : Handle → IO BufferMode
hFlush         : Handle → IO Unit
interact       : (String → String) → IO Unit
getChar        : IO Char
getLine        : IO String
getContents    : IO Costring
readFile       : FilePath → IO Costring
writeFile      : FilePath → Costring → IO Unit
appendFile     : FilePath → Costring → IO Unit
putChar        : Char → IO Unit
putStr         : Costring → IO Unit
putStrLn       : Costring → IO Unit
readFiniteFile : FilePath → IO String

hSetBuffering  = λ h b → lift (Prim.hSetBuffering h b)
hGetBuffering  = λ h → lift (Prim.hGetBuffering h)
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
run : ∀ {a} {A : Set a} → IO A → Prim.IO A
run (lift io)  = io
run (return a) = Prim.return a
run (bind m f) = run (∞IO′.force m) Prim.>>= λ a → run (∞IO′.force (f a))
