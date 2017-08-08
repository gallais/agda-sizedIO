module Sized.IO.Primitive where

open import IO.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Data.Maybe.Base
open import Foreign.Haskell

postulate
  interact : (String → String) → IO Unit
  putChar  : Char → IO Unit
  getChar  : IO Char
  getLine  : IO String

{-# FOREIGN GHC import Data.Text #-}
{-# COMPILE GHC interact = \ f -> interact (unpack . f . pack) #-}
{-# COMPILE GHC putChar = putChar #-}
{-# COMPILE GHC getChar = getChar #-}
{-# COMPILE GHC getLine = fmap pack getLine #-}

data BufferMode : Set where
  NoBuffering LineBuffering : BufferMode
  BlockBuffering : Maybe Nat → BufferMode

postulate
  Handle : Set
  stdin stdout stderr : Handle
  hSetBuffering : Handle → BufferMode → IO Unit
  hGetBuffering : Handle → IO BufferMode
  hFlush : Handle → IO Unit

{-# FOREIGN GHC import System.IO #-}
{-# FOREIGN GHC import qualified MAlonzo.Code.Data.Maybe.Base #-}
{-# FOREIGN GHC data AgdaBufferMode = AgdaNoBuffering | AgdaLineBuffering | AgdaBlockBuffering (Maybe Integer) #-}
{-# FOREIGN GHC toBufferMode = \ x -> case x of
                                        AgdaNoBuffering -> NoBuffering
                                        AgdaLineBuffering -> LineBuffering
                                        AgdaBlockBuffering m -> BlockBuffering (fmap fromIntegral m)
#-}
{-# FOREIGN GHC fromBufferMode = \ x -> case x of
                                          NoBuffering -> AgdaNoBuffering
                                          LineBuffering -> AgdaLineBuffering
                                          BlockBuffering m -> AgdaBlockBuffering (fmap fromIntegral m)
#-}
{-# COMPILE GHC BufferMode = data AgdaBufferMode (AgdaNoBuffering | AgdaLineBuffering | AgdaBlockBuffering) #-}
{-# COMPILE GHC Handle = type Handle #-}
{-# COMPILE GHC stdin = stdin #-}
{-# COMPILE GHC stdout = stdout #-}
{-# COMPILE GHC stderr = stderr #-}
{-# COMPILE GHC hSetBuffering = fmap (. toBufferMode) hSetBuffering #-}
{-# COMPILE GHC hGetBuffering = fmap fromBufferMode . hGetBuffering #-}
{-# COMPILE GHC hFlush = hFlush #-}
