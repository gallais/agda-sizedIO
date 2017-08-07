module stopwatch where

open import Data.Fin using (#_)
open import Sized.IO
open import Function
open import System.Clock as Clock
open import Data.String using (toCostring)

main : Main
main = run $ hSetBuffering stdin NoBuffering >>
             getTime Realtime >>= λ start →
             getChar >>
             getTime Realtime >>= λ end →
             let dff = diff start end
             in putStrLn (toCostring $ Clock.show dff (# 3))
