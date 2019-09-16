module System.Environment where

open import Level
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Foreign.Haskell.Coerce
open import System.FilePath.Posix

open import Data.Maybe.Base
open import Data.Product
open import Agda.Builtin.List
import System.Environment.Primitive as Prim

open import Codata.IO

private
  variable
    a ℓ : Level

getArgs           : IO ℓ (List String)
getProgName       : IO ℓ String
getExecutablePath : IO ℓ FilePath
lookupEnv         : String → IO ℓ (Maybe String)
setEnv            : String → String → IO ℓ ⊤
unsetEnv          : String → IO ℓ ⊤
withArgs          : {A : Set a} {{_ : a ≤ˡ ℓ}} → List String → IO ℓ A → IO ℓ A
withProgName      : {A : Set a} {{_ : a ≤ˡ ℓ}} → String → IO ℓ A → IO ℓ A
getEnvironment    : IO ℓ (List (String × String))

getArgs           = lift Prim.getArgs
getProgName       = lift Prim.getProgName
getExecutablePath = lift Prim.getExecutablePath
lookupEnv         = λ var → coerce <$> lift (Prim.lookupEnv var)
setEnv            = λ var str → lift (Prim.setEnv var str)
unsetEnv          = λ var → lift (Prim.unsetEnv var)
withArgs          = λ args io → lift (Prim.withArgs args (run io))
withProgName      = λ nm io → lift (Prim.withProgName nm (run io))
getEnvironment    = lift (coerce Prim.getEnvironment)
