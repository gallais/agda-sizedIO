module System.Clock where

open import Data.Bool.Base
open import Agda.Builtin.Nat
open import Sized.IO
open import Foreign.Haskell.Extras
open import System.Clock.Primitive as Prim
  using (Clock ; Monotonic ; Realtime ; ProcessCPUTime
               ; ThreadCPUTime ; MonotonicRaw ; Boottime
               ; MonotonicCoarse ; RealtimeCoarse) public

record Time : Set where
  constructor mkTime
  field seconds     : Nat
        nanoseconds : Nat
open Time public

diff : Time → Time → Time
diff (mkTime ss sns) (mkTime es ens) =
  if ens < sns
  then mkTime (es - suc ss) ((1000000000 + ens) - sns)
  else mkTime (es - ss) (ens - sns)

getTime : Clock → IO Time
getTime c = (λ { (mkPair a b) → mkTime a b }) <$> lift (Prim.getTime c)
