module System.Info where

open import Data.String

postulate
  os           : String
  arch         : String
  compilerName : String

{-# FOREIGN GHC import System.Info #-}
{-# FOREIGN GHC import Data.Text   #-}

{-# COMPILE GHC os           = pack os           #-}
{-# COMPILE GHC arch         = pack arch         #-}
{-# COMPILE GHC compilerName = pack compilerName #-}
