module Sized.IO.Primitive where

open import IO.Primitive
open import Agda.Builtin.Char
open import Agda.Builtin.String

postulate
  getChar : IO Char
  getLine : IO String

{-# FOREIGN GHC import Data.Text            #-}
{-# COMPILE GHC getChar = getChar           #-}
{-# COMPILE GHC getLine = fmap pack getLine #-}
