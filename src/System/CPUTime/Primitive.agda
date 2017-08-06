module System.CPUTime.Primitive where

open import Agda.Builtin.Nat
open import IO.Primitive

postulate
  getCPUTime : IO Nat
  cpuTimePrecision : Nat

{-# FOREIGN GHC import qualified System.CPUTime as CPT  #-}
{-# COMPILE GHC getCPUTime = CPT.getCPUTime             #-}
{-# COMPILE GHC cpuTimePrecision = CPT.cpuTimePrecision #-}
