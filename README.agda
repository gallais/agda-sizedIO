module README where

-- # agda-sizedIO
-- Experimental IO using sized types and copatterns

-- This library currently relies on:

-- * Agda with support for the NO_UNIVERSE_CHECK pragam, and
--   a strictly positive IO builtin.
--   i.e. post commit eabd7f5d27f7cf91ee4d70d64ea187a0fd99dab0

-- * Agda's stdlib with:
--   - the new codata modules
--   - the new Foreign.Haskell.Coerce module

-- * The following Haskell packages:
--   - directory >= 1.3.2.0
--   - filepath  >= 1.4.2.1


-- Examples

import cat
import read
import stopwatch
import find

-- Main module

import Codata.IO

-- Example of bindings

import System.Clock.Primitive
import System.Clock

import System.CPUTime.Primitive
import System.CPUTime

import System.Environment.Primitive
import System.Environment

import System.FilePath.Posix.Primitive
import System.FilePath.Posix

import System.Directory.Primitive
import System.Directory

import System.Info

-- Example of a high-level library function built on top

import System.Directory.Tree
