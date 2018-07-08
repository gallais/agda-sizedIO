module System.Clock.Primitive where

open import Agda.Builtin.Nat
open import IO.Primitive
open import Foreign.Haskell

data Clock : Set where
  Monotonic Realtime ProcessCPUTime : Clock
  ThreadCPUTime MonotonicRaw Boottime : Clock
  MonotonicCoarse RealtimeCoarse : Clock

{-# COMPILE GHC Clock = data Clock (Monotonic | Realtime | ProcessCPUTime
                                   | ThreadCPUTime | MonotonicRaw | Boottime
                                   | MonotonicCoarse | RealtimeCoarse )
#-}

postulate getTime : Clock → IO (Pair Nat Nat)

{-# FOREIGN GHC import System.Clock  #-}
{-# FOREIGN GHC import Data.Function #-}
{-# COMPILE GHC getTime = fmap (\ (TimeSpec a b) -> ((,) `on` fromIntegral) a b) . getTime #-}
