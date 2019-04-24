module Foreign.Haskell.Extras where

module Maybe where

  data Maybe {a} (A : Set a) : Set a where
    just    : A → Maybe A
    nothing : Maybe A

  {-# FOREIGN GHC type AgdaMaybe l = Maybe #-}

  {-# COMPILE GHC Maybe = data AgdaMaybe (Just | Nothing) #-}

  import Data.Maybe.Base as Maybe

  toForeign : ∀ {a} {A : Set a} → Maybe.Maybe A → Maybe A
  toForeign = Maybe.maybe′ just nothing

  fromForeign : ∀ {a} {A : Set a} → Maybe A → Maybe.Maybe A
  fromForeign (just a) = Maybe.just a
  fromForeign nothing  = Maybe.nothing

module Pair where

  open import Foreign.Haskell
  open import Data.Product

  fromForeign : ∀ {a b} {A : Set a} {B : Set b} → Pair A B → A × B
  fromForeign (a , b) = a , b

  toForeign : ∀ {a b} {A : Set a} {B : Set b} → A × B → Pair A B
  toForeign (a , b) = a , b

module BufferMode where

  open import Agda.Builtin.Nat

  data BufferMode : Set where
    NoBuffering LineBuffering : BufferMode
    BlockBuffering : Maybe.Maybe Nat → BufferMode

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

  open import Codata.IO.Types as Types hiding (BufferMode)

  fromForeign : BufferMode → Types.BufferMode
  fromForeign NoBuffering         = NoBuffering
  fromForeign LineBuffering       = LineBuffering
  fromForeign (BlockBuffering mn) = BlockBuffering (Maybe.fromForeign mn)

  toForeign : Types.BufferMode → BufferMode
  toForeign NoBuffering         = NoBuffering
  toForeign LineBuffering       = LineBuffering
  toForeign (BlockBuffering mn) = BlockBuffering (Maybe.toForeign mn)
