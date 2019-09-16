module Codata.IO.Types where

open import Data.Maybe.Base
open import Data.Nat.Base
open import Foreign.Haskell.Coerce

module FFI where

  import Foreign.Haskell as FFI

  data BufferMode : Set where
    NoBuffering LineBuffering : BufferMode
    BlockBuffering : FFI.Maybe ℕ → BufferMode

data BufferMode : Set where
  NoBuffering LineBuffering : BufferMode
  BlockBuffering : Maybe ℕ → BufferMode

instance

  bufferMode-fromFFI : Coercible FFI.BufferMode BufferMode
  bufferMode-fromFFI = TrustMe

  bufferMode-toFFI : Coercible BufferMode FFI.BufferMode
  bufferMode-toFFI = TrustMe
