module README where

-- # agda-sizedIO
-- Experimental IO using sized types and copatterns

-- This library currently relies on:

-- * Agda with support for the NO_UNIVERSE_CHECK pragam,
--   i.e. post commit be89d4a8b264dd2719cb8c601a2c7f45a95ba220

-- * Agda's stdlib with:
--   - the new codata modules
--   - binding to `Pair` in `Foreign.Haskell`

-- Examples

import cat
import read
import stopwatch

-- Main module

import Sized.IO

-- Example of Bindings from Haskell's Prelude

import System.Environment.Primitive
import System.Environment
