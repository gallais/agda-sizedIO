module System.Clock.Primitive where

open import Agda.Builtin.Nat
open import IO.Primitive
open import Foreign.Haskell.Extras

postulate getRealTime : IO (Pair Nat Nat)

{-# FOREIGN GHC import System.Clock  #-}
{-# FOREIGN GHC import Data.Function #-}
{-# COMPILE GHC getRealTime = fmap (\ (TimeSpec a b) -> ((,) `on` fromIntegral) a b) (getTime Realtime) #-}
