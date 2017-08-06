module System.CPUTime where

import System.CPUTime.Primitive as Prim
open Prim using (cpuTimePrecision) public
open import Sized.IO
open import Data.Nat.Base

getCPUTime : IO ℕ
getCPUTime = lift Prim.getCPUTime
