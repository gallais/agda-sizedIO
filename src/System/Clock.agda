module System.Clock where

open import Data.Bool.Base
open import Data.Product
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

getTime : ∀ {ℓ} → Clock → IO ℓ Time
getTime c = (λ { (mkPair a b) → mkTime a b }) <$> lift (Prim.getTime c)

module _ {ℓ a} {A : Set a} {{_ : a ≤ˡ ℓ}} where

  time : IO ℓ A → IO ℓ (A × Time)
  time io = getTime Realtime >>= λ start →
            io               >>= λ a     →
            getTime Realtime >>= λ end   →
            return (a , diff start end)

  time′ : IO ℓ A → IO ℓ Time
  time′ io = proj₂ <$> time io

open import Data.Unit
open import Data.Nat.Base as ℕ
import Data.Nat.Show as NatShow
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Fin
open import Data.String.Base hiding (show)
open import Data.String.Extras
open import Data.Sum
open import Relation.Nullary
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
    exp-nz x zero    = tt
    exp-nz x (suc n) {x≠0} with x ^ (suc n) ℕ.≟ 0
    ... | no ¬p = tt
    ... | yes p with i*j≡0⇒i≡0∨j≡0 x p
    ... | inj₁ x≡0   rewrite x≡0 = x≠0
    ... | inj₂ x^n≡0 = subst (λ x → False (x ℕ.≟ 0)) x^n≡0 (exp-nz x n {x≠0})
