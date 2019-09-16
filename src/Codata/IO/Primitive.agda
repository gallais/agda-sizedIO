module Codata.IO.Primitive where

open import IO.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Codata.IO.Types
open import Foreign.Haskell.Coerce

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
  hSetBuffering : Handle → FFI.BufferMode → IO ⊤
  hGetBuffering : Handle → IO FFI.BufferMode
  hFlush : Handle → IO ⊤

{-# FOREIGN GHC import System.IO #-}
{-# COMPILE GHC Handle = type Handle #-}
{-# COMPILE GHC stdin = stdin #-}
{-# COMPILE GHC stdout = stdout #-}
{-# COMPILE GHC stderr = stderr #-}
{-# FOREIGN GHC import MAlonzo.Code.Codata.IO.Types #-}
{-# COMPILE GHC hSetBuffering = \ h -> hSetBuffering h . toBufferMode #-}
{-# COMPILE GHC hGetBuffering = fmap fromBufferMode . hGetBuffering #-}
{-# COMPILE GHC hFlush = hFlush #-}
