module Codata.IO.Types where

open import Data.Maybe.Base
open import Data.Nat.Base

data BufferMode : Set where
  NoBuffering LineBuffering : BufferMode
  BlockBuffering : Maybe ℕ → BufferMode
