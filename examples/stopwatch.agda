module stopwatch where

open import Data.Fin using (#_)
open import Sized.IO
open import Function
open import System.Clock as Clock
open import Foreign.Haskell
open import Data.String using (toCostring)

import IO.Primitive as Prim
postulate hNoBuffering : Prim.IO Unit
{-# FOREIGN GHC import System.IO #-}
{-# COMPILE GHC hNoBuffering = hSetBuffering stdin NoBuffering #-}

main = run $ lift hNoBuffering >>
             getTime Realtime >>= λ start →
             getChar >>
             getTime Realtime >>= λ end →
             let dff = diff start end
             in unit <$ putStrLn (toCostring $ Clock.show dff (# 3))
