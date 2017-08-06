module stopwatch where

open import Sized.IO
open import Function
open import System.Clock
open import Foreign.Haskell
open import Agda.Builtin.Nat
open import Data.Nat.DivMod
open import Data.Bool.Base
open import Data.Nat.Show
open import Data.String using (toCostring ; _++_)

import IO.Primitive as Prim
postulate hNoBuffering : Prim.IO Unit
{-# FOREIGN GHC import System.IO #-}
{-# COMPILE GHC hNoBuffering = hSetBuffering stdin NoBuffering #-}

main = run $ lift hNoBuffering >>
             getTime Realtime >>= λ start →
             getChar >>
             getTime Realtime >>= λ end →
             let dff = diff start end
                 str = show (seconds dff)
                     ++ "s"
                     ++ show (nanoseconds dff div 1000000)
             in unit <$ putStrLn (toCostring str)
