-----------------------------------------------------------------
-- A library to get the import structures of a program.

module Imports(getImportedInterfaces,moduleImports,readFlatCurryFileInLoadPath,
               InterfaceOrFlatProg(..),ifOrProg,progOfIFFP)
  where

import FlatCurry.Types
import FlatCurry.Files
import FlatCurry.Goodies
import FlatCurry.Read

import System.Directory (findFileWithSuffix, getFileSize)
import Data.Maybe
import Distribution     (getLoadPathForModule)

--- Get all interfaces (i.e., main and all indirectly imported modules)
--- of a program:
getImportedInterfaces :: String -> IO [(String,InterfaceOrFlatProg)]
getImportedInterfaces mod = do
  imps <- readFlatCurryIntWithImports mod
  return (map (\prog -> (progName prog, IF prog)) imps)

-- Extract a module and its imports
moduleImports :: Prog -> (String, [String])
moduleImports (Prog m is _ _ _) = (m, is)

-----------------------------------------------------------------------------
-- Unione type to distinguish between interface and FlatCurry program:
data InterfaceOrFlatProg = IF Prog | FP Prog

ifOrProg :: (Prog->a) -> (Prog->a) -> InterfaceOrFlatProg -> a
ifOrProg iffun _ (IF prog) = iffun prog
ifOrProg _ fpfun (FP prog) = fpfun prog

progOfIFFP :: InterfaceOrFlatProg -> Prog
progOfIFFP (IF prog) = prog
progOfIFFP (FP prog) = prog

--------------------------------------------------------------------------
-- Read an existing(!) FlatCurry file w.r.t. current load path:
readFlatCurryFileInLoadPath :: (String -> IO _) -> String -> [String] -> IO Prog
readFlatCurryFileInLoadPath prt mod loadpath = do
  mbfcyfile <- findFileWithSuffix (flatCurryFileName mod) [""] loadpath
  maybe (error $ "FlatCurry file of module "++mod++" not found!")
        (readFlatCurryFileAndReport prt mod)
        mbfcyfile

readFlatCurryFileAndReport :: (String -> IO _) -> String -> String -> IO Prog
readFlatCurryFileAndReport prt mod filename = do
  size <- getFileSize filename
  prt $ "Reading FlatCurry file of module '"++mod++"' ("++show size++" bytes)..."
  prog <- readFlatCurryFile filename
  seq (prog==prog) (return prog)

--------------------------------------------------------------------------
