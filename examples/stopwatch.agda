module stopwatch where

open import Level using (zero)
open import Data.Fin using (#_)
open import Codata.IO
open import Function
open import System.Clock as Clock
open import Codata.Musical.Costring

main : Main
main = run $ (IO zero _ ∋_) $ do
  hSetBuffering stdin NoBuffering
  dff ← time′ getChar
  putStrLn (Clock.show dff (# 3))
