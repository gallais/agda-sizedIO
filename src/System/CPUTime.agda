module System.CPUTime where

import System.CPUTime.Primitive as Prim
open Prim using (cpuTimePrecision) public
open import Sized.IO
open import Data.Nat.Base

getCPUTime : ∀ {ℓ} → IO ℓ ℕ
getCPUTime = lift Prim.getCPUTime
