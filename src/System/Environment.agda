module System.Environment where

open import Agda.Builtin.String
open import Foreign.Haskell
open import Foreign.Haskell.Extras
open import System.FilePath.Posix

open import Data.Maybe.Base
open import Agda.Builtin.List
import System.Environment.Primitive as Prim


-- TOGGLE THESE TO CHANGE ERROR
-------------------------------

open import Sized.IO
import IO.Primitive as Prim

module _ {ℓ} where

 getArgs           : IO ℓ (List String)
 getProgName       : IO ℓ String
 getExecutablePath : IO ℓ FilePath
 lookupEnv         : String → IO ℓ (Maybe String)
 setEnv            : String → String → IO ℓ Unit
 unsetEnv          : String → IO ℓ Unit
 withArgs          : ∀ {a} {A : Set a} {{_ : a ≤ˡ ℓ}} → List String → IO ℓ A → IO ℓ A
 withProgName      : ∀ {a} {A : Set a} {{_ : a ≤ˡ ℓ}} → String → IO ℓ A → IO ℓ A
 getEnvironment    : IO ℓ (List (Pair String String))

 getArgs           = lift Prim.getArgs
 getProgName       = lift Prim.getProgName
 getExecutablePath = lift Prim.getExecutablePath
 lookupEnv         = λ var → lift (Prim.lookupEnv var)
 setEnv            = λ var str → lift (Prim.setEnv var str)
 unsetEnv          = λ var → lift (Prim.unsetEnv var)
 withArgs          = λ args io → lift (Prim.withArgs args (run io))
 withProgName      = λ nm io → lift (Prim.withProgName nm (run io))
 getEnvironment    = lift Prim.getEnvironment
