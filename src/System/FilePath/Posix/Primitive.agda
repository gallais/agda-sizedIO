module System.FilePath.Posix.Primitive where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Product
open import Data.Sum.Base
open import Foreign.Haskell as FFI
open import Foreign.Haskell.Coerce

-- A filepath has a nature: it can be either relative or absolute.
-- We postulate this nature rather than defining it as an inductive
-- type so that the user cannot inspect. The only way to cast an
-- arbitrary filepath nature @n@ to either @relative@ or @absolute@
-- is to use @observeNature@.

postulate
  Nature : Set
  relative absolute : Nature

-- In the Haskell backend these @natures@ are simply erased as the
-- libraries represent all filepaths in the same way.

{-# FOREIGN GHC {-# LANGUAGE DataKinds #-} #-}
{-# FOREIGN GHC import Data.Kind #-}
{-# COMPILE GHC Nature   = type Type #-}
{-# COMPILE GHC relative = type () #-}
{-# COMPILE GHC absolute = type () #-}

private
  variable
    m n : Nature

postulate

  FilePath     : Nature → Set
  getFilePath  : FilePath n → String

  Extension    : Set
  mkExtension  : String → Extension
  getExtension : Extension → String

{-# FOREIGN GHC import Data.Text                        #-}
{-# FOREIGN GHC import System.FilePath.Posix            #-}
{-# FOREIGN GHC type AgdaFilePath n = FilePath          #-}
{-# COMPILE GHC FilePath            = type AgdaFilePath #-}
{-# COMPILE GHC getFilePath         = const pack        #-}
{-# COMPILE GHC Extension           = type String       #-}
{-# COMPILE GHC mkExtension         = unpack            #-}
{-# COMPILE GHC getExtension        = pack              #-}

-- We provide convenient short names for the two types of filepaths

AbsolutePath = FilePath absolute
RelativePath = FilePath relative


-- As a @FilePath@ is represented internally as @String@ we can happily
-- coerce from one to the other. We do not add the symmetric @Coercible@
-- instance as this would entail the ability to pick a specific nature.

instance

  filePath-toString : Coercible (FilePath n) String
  filePath-toString = TrustMe

-- In order to prevent users from picking whether a string gets
-- converted to a @relative@ or an @absolute@ path we have:
-- * a postulated @defaultNature@
-- * a function @mkFilePath@ producing filepaths of this postulated nature

postulate
  defaultNature : Nature
  mkFilePath    : String → FilePath defaultNature

{-# COMPILE GHC defaultNature = type () #-}
{-# COMPILE GHC mkFilePath    = unpack  #-}

postulate

  splitExtension  : FilePath n → Pair (FilePath n) Extension
  splitExtensions : FilePath n → Pair (FilePath n) Extension

  takeExtension  : FilePath n → Extension
  takeExtensions : FilePath n → Extension

  replaceExtension  : FilePath n → Extension → FilePath n
  replaceExtensions : FilePath n → Extension → FilePath n

  dropExtension  : FilePath n → FilePath n
  dropExtensions : FilePath n → FilePath n

  addExtension : FilePath n → Extension → FilePath n
  hasExtension : FilePath n → Bool

  stripExtension : Extension → FilePath n → FFI.Maybe (FilePath n)

  splitFileName    : FilePath n → Pair (FilePath n) RelativePath
  takeFileName     : FilePath n → String
  replaceFileName  : FilePath n → String → FilePath n
  dropFileName     : FilePath n → FilePath n
  takeBaseName     : FilePath n → String
  replaceBaseName  : FilePath n → String → FilePath n
  takeDirectory    : FilePath n → FilePath n
  replaceDirectory : FilePath m → FilePath n → FilePath n
  combine          : FilePath n → RelativePath → FilePath n
  splitPath        : FilePath n → List RelativePath
  joinPath         : List RelativePath → RelativePath
  splitDirectories : FilePath n → List RelativePath

  -- File name manipulation

  normalise        : FilePath n → FilePath n
  isRelative       : FilePath n → Bool
  isAbsolute       : FilePath n → Bool

{-# COMPILE GHC splitExtension    = \ _ -> splitExtension                  #-}
{-# COMPILE GHC splitExtensions   = \ _ -> splitExtensions                 #-}
{-# COMPILE GHC takeExtension     = \ _ -> takeExtension                   #-}
{-# COMPILE GHC takeExtensions    = \ _ -> takeExtensions                  #-}
{-# COMPILE GHC replaceExtension  = \ _ -> replaceExtension                #-}
{-# COMPILE GHC replaceExtensions = \ _ -> replaceExtensions               #-}
{-# COMPILE GHC dropExtension     = \ _ -> dropExtension                   #-}
{-# COMPILE GHC dropExtensions    = \ _ -> dropExtensions                  #-}
{-# COMPILE GHC addExtension      = \ _ -> addExtension                    #-}
{-# COMPILE GHC hasExtension      = \ _ -> hasExtension                    #-}
{-# COMPILE GHC stripExtension    = \ _ -> stripExtension                  #-}
{-# COMPILE GHC splitFileName     = \ _ -> splitFileName                   #-}
{-# COMPILE GHC takeFileName      = \ _ -> pack . takeFileName             #-}
{-# COMPILE GHC replaceFileName   = \ _ -> fmap (. unpack) replaceFileName #-}
{-# COMPILE GHC dropFileName      = \ _ -> dropFileName                    #-}
{-# COMPILE GHC takeBaseName      = \ _ -> pack . takeBaseName             #-}
{-# COMPILE GHC replaceBaseName   = \ _ -> fmap (. unpack) replaceBaseName #-}
{-# COMPILE GHC takeDirectory     = \ _ -> takeDirectory                   #-}
{-# COMPILE GHC replaceDirectory  = \ _ _ -> replaceDirectory              #-}
{-# COMPILE GHC combine           = \ _ -> combine                         #-}
{-# COMPILE GHC splitPath         = \ _ -> splitPath                       #-}
{-# COMPILE GHC joinPath          = joinPath                               #-}
{-# COMPILE GHC splitDirectories  = \ _ -> splitDirectories                #-}
{-# COMPILE GHC normalise         = \ _ -> normalise                       #-}
{-# COMPILE GHC isRelative        = \ _ -> isRelative                      #-}
{-# COMPILE GHC isAbsolute        = \ _ -> isAbsolute                      #-}
