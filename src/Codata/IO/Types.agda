module Codata.IO.Types where

open import Data.Maybe.Base
open import Data.Nat.Base
open import Foreign.Haskell.Coerce

module FFI where

  import Foreign.Haskell as FFI

  data BufferMode : Set where
    NoBuffering LineBuffering : BufferMode
    BlockBuffering : FFI.Maybe ℕ → BufferMode
  {-# FOREIGN GHC import qualified System.IO as SIO #-}
  {-# FOREIGN GHC
      data AgdaBufferMode
        = NoBuffering
        | LineBuffering
        | BlockBuffering (Maybe Integer)
      toBufferMode :: AgdaBufferMode -> SIO.BufferMode
      toBufferMode x = case x of
        NoBuffering       -> SIO.NoBuffering
        LineBuffering     -> SIO.LineBuffering
        BlockBuffering mi -> SIO.BlockBuffering (fromIntegral <$> mi)
      fromBufferMode :: SIO.BufferMode -> AgdaBufferMode
      fromBufferMode x = case x of
        SIO.NoBuffering       -> NoBuffering
        SIO.LineBuffering     -> LineBuffering
        SIO.BlockBuffering mi -> BlockBuffering (fromIntegral <$> mi)
  #-}

  {-# COMPILE GHC BufferMode = data AgdaBufferMode
                             ( NoBuffering
                             | LineBuffering
                             | BlockBuffering
                             )
  #-}

data BufferMode : Set where
  NoBuffering LineBuffering : BufferMode
  BlockBuffering : Maybe ℕ → BufferMode


instance

  bufferMode-fromFFI : Coercible FFI.BufferMode BufferMode
  bufferMode-fromFFI = TrustMe

  bufferMode-toFFI : Coercible BufferMode FFI.BufferMode
  bufferMode-toFFI = TrustMe
