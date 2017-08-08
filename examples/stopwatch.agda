module stopwatch where

open import Data.Fin using (#_)
open import Sized.IO
open import Function
open import System.Clock as Clock
open import Data.String using (toCostring)

main : Main
main = run $ hSetBuffering stdin NoBuffering >>
             time′ getChar >>= λ dff →
             putStrLn (toCostring $ Clock.show dff (# 3))
