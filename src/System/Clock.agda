module System.Clock where

open import Agda.Builtin.Nat
open import Sized.IO
open import Foreign.Haskell.Extras
import System.Clock.Primitive as Prim

record Time : Set where
  constructor mkTime
  field seconds     : Nat
        nanoseconds : Nat
open Time public

getRealTime : IO Time
getRealTime = (λ { (mkPair a b) → mkTime a b }) <$> lift Prim.getRealTime
