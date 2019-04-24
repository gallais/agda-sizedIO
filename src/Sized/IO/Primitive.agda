module Sized.IO.Primitive where

open import IO.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Foreign.Haskell.Extras

postulate
  interact : (String → String) → IO ⊤
  putChar  : Char → IO ⊤
  getChar  : IO Char
  getLine  : IO String

{-# FOREIGN GHC import Data.Text #-}
{-# COMPILE GHC interact = \ f -> interact (unpack . f . pack) #-}
{-# COMPILE GHC putChar = putChar #-}
{-# COMPILE GHC getChar = getChar #-}
{-# COMPILE GHC getLine = fmap pack getLine #-}

postulate
  Handle : Set
  stdin stdout stderr : Handle
  hSetBuffering : Handle → BufferMode.BufferMode → IO ⊤
  hGetBuffering : Handle → IO BufferMode.BufferMode
  hFlush : Handle → IO ⊤

{-# FOREIGN GHC import System.IO #-}
{-# FOREIGN GHC import MAlonzo.Code.Foreign.Haskell.Extras #-}
{-# COMPILE GHC Handle = type Handle #-}
{-# COMPILE GHC stdin = stdin #-}
{-# COMPILE GHC stdout = stdout #-}
{-# COMPILE GHC stderr = stderr #-}
{-# COMPILE GHC hSetBuffering = \ h bm -> hSetBuffering h (toBufferMode bm) #-}
{-# COMPILE GHC hGetBuffering = \ h -> fmap fromBufferMode (hGetBuffering h) #-}
{-# COMPILE GHC hFlush = hFlush #-}
