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

diff : Time → Time → Time
diff (mkTime ss sns) (mkTime es ens) =
  if ens < sns
  then mkTime (es - suc ss) ((1000000000 + ens) - sns)
  else mkTime (es - ss) (ens - sns)

import IO.Primitive as Prim
postulate hNoBuffering : Prim.IO Unit
{-# FOREIGN GHC import System.IO #-}
{-# COMPILE GHC hNoBuffering = hSetBuffering stdin NoBuffering #-}

main = run $ lift hNoBuffering >>
             getRealTime >>= λ start →
             getChar >>
             getRealTime >>= λ end →
             let dff = diff start end
                 str = show (seconds dff) ++ "s" ++ show (nanoseconds dff div 1000000)
             in unit <$ putStrLn (toCostring str)
