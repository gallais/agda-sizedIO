module System.Environment.Primitive where

open import IO.Primitive
open import Agda.Builtin.String
open import Data.Maybe.Base
open import Agda.Builtin.List
open import Foreign.Haskell
open import Foreign.Haskell.Extras
open import System.FilePath.Posix

postulate

  getArgs           : IO (List String)
  getProgName       : IO String
  getExecutablePath : IO FilePath
  lookupEnv         : String → IO (Maybe String)
  setEnv            : String → String → IO Unit
  unsetEnv          : String → IO Unit
  withArgs          : ∀ {a} {A : Set a} → List String → IO A → IO A
  withProgName      : ∀ {a} {A : Set a} → String → IO A → IO A
  getEnvironment    : IO (List (Pair String String))

{-# FOREIGN GHC import qualified System.Environment as SE                                        #-}
{-# FOREIGN GHC import Data.Text                                                                 #-}
{-# FOREIGN GHC import Data.Function                                                             #-}
{-# COMPILE GHC getArgs           = fmap (fmap pack) SE.getArgs                                  #-}
{-# COMPILE GHC getProgName       = fmap pack SE.getProgName                                     #-}
{-# COMPILE GHC getExecutablePath = SE.getExecutablePath                                         #-}
{-# COMPILE GHC lookupEnv         = fmap (fmap pack) . SE.lookupEnv . unpack                     #-}
{-# COMPILE GHC setEnv            = SE.setEnv `on` unpack                                        #-}
{-# COMPILE GHC unsetEnv          = SE.unsetEnv . unpack                                         #-}
{-# COMPILE GHC withArgs          = \ _ _ -> SE.withArgs . fmap unpack                           #-}
{-# COMPILE GHC withProgName      = \ _ _ -> SE.withProgName . unpack                            #-}
{-# COMPILE GHC getEnvironment    = fmap (fmap (\ (a, b) -> (pack a, pack b))) SE.getEnvironment #-}
