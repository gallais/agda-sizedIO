module System.Clock where

open import Data.Bool.Base
open import Data.Product
open import Agda.Builtin.Nat
open import Sized.IO
open import Function
open import Foreign.Haskell
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

getTime : ∀ {ℓ} → Clock → IO ℓ Time
getTime c = do
  (a , b) ← lift (Prim.getTime c)
  return $ mkTime a b

module _ {ℓ a} {A : Set a} {{_ : a ≤ˡ ℓ}} where

  time : IO ℓ A → IO ℓ (A × Time)
  time io = do
    start ← getTime Realtime
    a     ← io
    end   ← getTime Realtime
    return (a , diff start end)

  time′ : IO ℓ A → IO ℓ Time
  time′ io = proj₂ <$> time io

open import Data.Nat.Base as ℕ
import Data.Nat.Show as NatShow
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Fin
open import Data.String.Base hiding (show)
open import Data.String.Extras
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

show : Time → Fin 9 → String
show (mkTime s ns) prec = secs ++ "s" ++ padLeft '0' decimals nsecs where
  decimals  = toℕ prec
  secs      = NatShow.show s
  nsecs     = NatShow.show ((ns div (10 ^ (9 ∸ decimals)))
                           {exp-nz 10 (9 ∸ decimals)})

   where

    exp-nz : ∀ x n {x≠0 : False (x ℕ.≟ 0)} → False (x ^ n ℕ.≟ 0)
    exp-nz x n {x≠0} = fromWitnessFalse (toWitnessFalse x≠0 ∘′ i^j≡0⇒i≡0 x n)
