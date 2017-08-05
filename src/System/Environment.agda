module System.Environment where

open import Agda.Builtin.String
open import Foreign.Haskell
open import Foreign.Haskell.Extras
open import Sized.IO
open import System.FilePath.Posix

open import Data.Maybe.Base
open import Agda.Builtin.List
import System.Environment.Primitive as Prim

getArgs           : IO (List String)
getProgName       : IO String
getExecutablePath : IO FilePath
lookupEnv         : String → IO (Maybe String)
setEnv            : String → String → IO Unit
unsetEnv          : String → IO Unit
withArgs          : ∀ {a} {A : Set a} → List String → IO A → IO A
withProgName      : ∀ {a} {A : Set a} → String → IO A → IO A
getEnvironment    : IO (List (Pair String String))

getArgs           = lift Prim.getArgs
getProgName       = lift Prim.getProgName
getExecutablePath = lift Prim.getExecutablePath
lookupEnv         = λ var → lift (Prim.lookupEnv var)
setEnv            = λ var str → lift (Prim.setEnv var str)
unsetEnv          = λ var → lift (Prim.unsetEnv var)
withArgs          = λ args io → lift (Prim.withArgs args (run io))
withProgName      = λ nm io → lift (Prim.withProgName nm (run io))
getEnvironment    = lift Prim.getEnvironment
