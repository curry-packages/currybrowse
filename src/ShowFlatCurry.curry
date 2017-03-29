------------------------------------------------------------------------------
--- This module contains various operations to show a FlatCurry program
--- in human-readable forms, e.g., only the interface or also the
--- complete program translated back into pattern-based rules.
--- These operations are used in the Curry Browser and they are
--- also the basis to implement the `:interface` command
--- of PAKCS or KiCS2.
---
--- The interface description contains the type declarations
--- for all entities defined and exported by this module.
---
--- The human-readable presentation is (almost) Curry source code
--- generated from a FlatCurry program.
---
--- @author Michael Hanus
--- @version August 2016
------------------------------------------------------------------------------

module ShowFlatCurry
 ( main, showInterface, showCurryModule, showCurryFuncDecl
 , showFlatCurry, showFuncDeclAsCurry, showFuncDeclAsFlatCurry
 , funcModule, leqFunc
 ) where

import Char         (isAlpha)
import Directory    (doesFileExist, getModificationTime)
import Distribution (stripCurrySuffix, modNameToPath
                    ,lookupModuleSourceInLoadPath)
import FilePath     (takeFileName, (</>))
import List         (intercalate)
import Pretty             (pPrint)
import Sort         (sortBy, leqString)
import System       (getArgs, getEnviron, system)

import FlatCurry.Types
import FlatCurry.Files
import FlatCurry.Goodies (funcName)
import FlatCurry.Pretty  (Options (..), defaultOptions, ppProg, ppFuncDecl)
import FlatCurry.Show

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["-mod",mod] -> printCurryMod (stripCurrySuffix mod)
    ["-int",mod] -> printInterface (stripCurrySuffix mod)
    ["-mod",mod,target] -> writeCurryMod target (stripCurrySuffix mod)
    ["-int",mod,target] -> writeInterface target (stripCurrySuffix mod)
    _ -> putStrLn $ "ERROR: Illegal arguments for genint: " ++
                    intercalate " " args ++ "\n" ++
                    "Usage: [-mod|-int] module_name [targetfile]"

-- print interface on stdout:
printInterface :: String -> IO ()
printInterface progname =
  do intstring <- genInt False progname
     putStrLn ("Interface of module \""++progname++"\":\n")
     putStrLn intstring

-- write interface into target file:
writeInterface :: String -> String -> IO ()
writeInterface targetfile progname =
  do intstring <- genInt True progname
     writeFile targetfile
               ("--Interface of module \""++progname++"\":\n\n"++
                intstring)
     putStrLn ("Interface written into file \""++targetfile++"\"")


-----------------------------------------------------------------------
-- Get a FlatCurry program (parse only if necessary):
getFlatProg :: String -> IO Prog
getFlatProg modname = do
  mbdirfn <- lookupModuleSourceInLoadPath modname
  let progname = maybe modname snd mbdirfn
  let fcyprogname = flatCurryFileName
                        (maybe modname (\ (d,_) -> d </> takeFileName modname)
                                       mbdirfn)
  fcyexists <- doesFileExist fcyprogname
  if not fcyexists
    then readFlatCurry modname
    else do ctime <- getModificationTime progname
            ftime <- getModificationTime fcyprogname
            if ctime>ftime
             then readFlatCurry modname
             else readFlatCurryFile fcyprogname

-----------------------------------------------------------------------
-- Generate interface description for a program:
-- If first argument is True, generate stubs (...external) for
-- all functions so that the resulting interface is a valid Curry program.
genInt :: Bool -> String -> IO String
genInt genstub progname = getFlatInt progname >>= return . showInterface genstub

-- Shows an interface description for a program:
-- If first argument is True, generate stubs (...external) for
-- all functions so that the resulting interface is a valid Curry program.
showInterface :: Bool -> Prog -> String
showInterface genstub (Prog mod imports types funcs ops) = unlines $
  ["module " ++ mod ++ " where\n"] ++
  concatMap showInterfaceImport imports ++ [""] ++
  map showInterfaceOpDecl (sortBy leqOp ops) ++
  (if null ops then [] else [""]) ++
  concatMap (showInterfaceType (showQNameInModule mod))
            (sortBy leqType types) ++ [""] ++
  map (showInterfaceFunc (showQNameInModule mod) genstub)
      (sortBy leqFunc funcs)

-- Get a FlatCurry program (parse only if necessary):
getFlatInt :: String -> IO Prog
getFlatInt modname = do
  mbdirfn <- lookupModuleSourceInLoadPath modname
  let progname = maybe modname snd mbdirfn
  let fintprogname = flatCurryIntName
                        (maybe modname (\ (d,_) -> d </> takeFileName modname)
                                       mbdirfn)
  fintexists <- doesFileExist fintprogname
  if not fintexists
    then readFlatCurryInt modname
    else do ctime <- getModificationTime progname
            ftime <- getModificationTime fintprogname
            if ctime>ftime
             then readFlatCurryInt modname
             else readFlatCurryFile fintprogname

-- write import declaration
showInterfaceImport :: String -> [String]
showInterfaceImport impmod = if impmod=="Prelude"
                             then []
                             else ["import "++impmod]

-- show operator declaration
showInterfaceOpDecl :: OpDecl -> String
showInterfaceOpDecl (Op op InfixOp  prec) = "infix "++show prec++" "++showOp op
showInterfaceOpDecl (Op op InfixlOp prec) = "infixl "++show prec++" "++showOp op
showInterfaceOpDecl (Op op InfixrOp prec) = "infixr "++show prec++" "++showOp op

showOp :: (_,String) -> String
showOp (_,on) = if isAlpha (head on) then '`':on++"`"
                                     else on

-- show type declaration if it is not a dictionary
showInterfaceType :: (QName -> String) -> TypeDecl -> [String]
showInterfaceType tt (Type (_,tcons) vis tvars constrs) =
  if vis==Public && not (isDict tcons)
  then ["data " ++ tcons ++ concatMap (\i->[' ',chr (97+i)]) tvars ++
        (if null constxt then "" else " = " ++ constxt)]
  else []
 where
  isDict fn = take 6 fn == "_Dict#"
  
  constxt = intercalate " | "
              (map (showExportConsDecl tt)
                   (filter (\ (Cons _ _ cvis _)->cvis==Public) constrs))

showInterfaceType tt (TypeSyn (_,tcons) vis tvars texp) =
  if vis==Public
  then ["type " ++ tcons ++ concatMap (\i->[' ',chr (97+i)]) tvars ++
        " = " ++ showCurryType tt True texp]
  else []

showExportConsDecl :: (QName -> String) -> ConsDecl -> String
showExportConsDecl tt (Cons (_,cname) _ _ argtypes) =
  cname ++ concatMap (\t->" "++showCurryType tt True t) argtypes

-- show function type declaration if it is not an internal
-- operation to implement type classes
showInterfaceFunc :: (QName -> String) -> Bool -> FuncDecl -> String
showInterfaceFunc ttrans genstub (Func (_,fname) _ vis ftype _) =
  if vis==Public && not (classOperations fname)
  then showCurryId fname ++ " :: " ++
       showCurryType ttrans False ftype ++
       (if genstub then "\n" ++ showCurryId fname ++ " external\n" else "")
  else ""
 where
  classOperations fn = take 6 fn `elem` ["_impl#","_inst#"]
                    || take 5 fn == "_def#" || take 7 fn == "_super#"
  
---------------------------------------------------------------------------
-- generate a human-readable representation of a Curry module:

-- show representation on stdout:
printCurryMod :: String -> IO ()
printCurryMod progname =
  do modstring <- genCurryMod progname
     putStrLn ("-- Program file: "++progname)
     putStrLn modstring

-- write representation into file:
writeCurryMod :: String -> String -> IO ()
writeCurryMod targetfile progname =
  do modstring <- genCurryMod progname
     writeFile targetfile
               ("--Program file: "++progname++"\n\n"++
                modstring)
     putStrLn ("Module written into file \""++targetfile++"\"")

-- generate a human-readable representation of a Curry module:
genCurryMod :: String -> IO String
genCurryMod progname = do
  prog <- readFlatCurryFile (flatCurryFileName progname)
  return $ showCurryModule prog

showCurryModule :: Prog -> String
showCurryModule (Prog mod imports types funcs ops) = unlines $
  ["module "++mod++"("++showTypeExports types ++
   showFuncExports funcs++") where\n"] ++
  concatMap showInterfaceImport imports ++ [""] ++
  map showInterfaceOpDecl ops ++
  (if null ops then [] else [""]) ++
  map (showCurryDataDecl (showQNameInModule mod)) types
  ++ [""] ++
  map (showCurryFuncDecl (showQNameInModule mod)
                         (showQNameInModule mod)) funcs

showTypeExports :: [TypeDecl] -> String
showTypeExports types = concatMap (++",") (concatMap exptype types)
 where
   exptype (Type tcons vis _ cdecls) =
     if vis==Public
     then [snd tcons++let cs = expcons cdecls in (if cs=="()" then "" else cs)]
     else []
   exptype (TypeSyn tcons vis _ _) = if vis==Public then [snd tcons] else []

   expcons cds = "(" ++ intercalate "," (concatMap expc cds) ++ ")"
   expc (Cons cname _ vis _) = if vis==Public then [snd cname] else []

showFuncExports :: [FuncDecl] -> String
showFuncExports funcs = intercalate "," (concatMap expfun funcs)
 where
   expfun (Func fname _ vis _ _) = if vis==Public then [snd fname] else []

showCurryDataDecl :: (QName -> String) -> TypeDecl -> String
showCurryDataDecl tt (Type tcons _ tvars constrs) =
  "data " ++ snd tcons ++ concatMap (\i->[' ',chr (97+i)]) tvars ++
  (if null constxt then "" else " = " ++ constxt)
 where constxt = intercalate " | " (map (showCurryConsDecl tt) constrs)
showCurryDataDecl tt (TypeSyn tcons _ tvars texp) =
  "type " ++ snd tcons ++ concatMap (\i->[' ',chr (97+i)]) tvars ++
  " = " ++ showCurryType tt True texp

showCurryConsDecl :: (QName -> String) -> ConsDecl -> String
showCurryConsDecl tt (Cons cname _ _ argtypes) =
  snd cname ++ concatMap (\t->" "++showCurryType tt True t) argtypes


-- generate function definitions:
showCurryFuncDecl :: (QName -> String) -> (QName -> String) -> FuncDecl -> String
showCurryFuncDecl tt tf (Func fname _ _ ftype frule) =
  showCurryId (snd fname) ++" :: "++ showCurryType tt False ftype ++ "\n" ++
  showCurryRule tf fname frule

-- format rule as set of pattern matching rules:
showCurryRule :: (QName -> String) -> QName -> Rule -> String
showCurryRule _  fname (External   _) = showCurryId (snd fname) ++ " external\n"
showCurryRule tf fname (Rule lhs rhs) =
  concatMap (\ (l,r) -> showCurryPatternRule tf l r)
            (rule2equations (shallowPattern2Expr fname lhs) rhs)

splitFreeVars :: Expr -> ([Int],Expr)
splitFreeVars exp = case exp of
  Free vars e -> (vars,e)
  _ -> ([],exp)

showCurryPatternRule :: (QName -> String) -> Expr -> Expr -> String
showCurryPatternRule tf l r = let (vars,e) = splitFreeVars r in
   showCurryExpr tf False 0 l ++
   showCurryCRHS tf e ++
   (if vars==[] then "" else
    " where " ++ intercalate "," (map showCurryVar vars) ++ " free")
   ++ "\n"

showCurryCRHS :: (QName -> String) -> Expr -> String
showCurryCRHS tf r = case r of
  Comb _ ("Prelude","cond") [e1, e2] -> " | " ++ showCurryCondRule e1 e2
  _                                  -> " = " ++ showCurryExpr tf False 2 r
 where
   showCurryCondRule e1 e2 = showCurryExpr tf False 2 e1 ++
                             " = " ++ showCurryExpr tf False 4 e2

-- transform a rule consisting of a left- and a right-hand side
-- (represented as expressions) into a set of pattern matching rules:
rule2equations :: Expr -> Expr -> [(Expr,Expr)]
rule2equations lhs rhs = case rhs of
  Case Flex (Var i) bs -> caseIntoLhs lhs i bs
  Or e1 e2 -> rule2equations lhs e1 ++ rule2equations lhs e2
  _        -> [(lhs,rhs)]

caseIntoLhs :: Expr -> Int -> [BranchExpr] -> [(Expr,Expr)]
caseIntoLhs _ _ [] = []
caseIntoLhs lhs vi (Branch (Pattern c vs) e : bs) =
  rule2equations (substitute [vi] [shallowPattern2Expr c vs] lhs) e
  ++ caseIntoLhs lhs vi bs
caseIntoLhs lhs vi (Branch (LPattern lit) e : bs) =
  rule2equations (substitute [vi] [Lit lit] lhs) e
  ++ caseIntoLhs lhs vi bs

shallowPattern2Expr :: QName -> [Int] -> Expr
shallowPattern2Expr name vars =
               Comb ConsCall name (map (\i->Var i) vars)


-- (substitute vars exps expr) = expr[vars/exps]
-- i.e., replace all occurrences of vars by corresponding exps in the
-- expression expr
substitute :: [Int] -> [Expr] -> Expr -> Expr
substitute vars exps expr = substituteAll vars exps 0 expr

-- (substituteAll vars exps base expr):
-- substitute all occurrences of variables by corresonding expressions:
-- * substitute all occurrences of var_i by exp_i in expr
--   (if vars=[var_1,...,var_n] and exps=[exp_1,...,exp_n])
-- * substitute all other variables (Var j) by (Var (base+j))
--
-- here we assume that the new variables in guards and case patterns
-- do not occur in the list "vars" of replaced variables!

substituteAll :: [Int] -> [Expr] -> Int -> Expr -> Expr
substituteAll vars exps b (Var i) = replaceVar vars exps i
  where replaceVar []     _      var = Var (b + var)
        replaceVar (_:_)  []     var = Var (b + var)
        replaceVar (v:vs) (e:es) var = if v == var then e
                                                   else replaceVar vs es var
substituteAll _  _  _ (Lit l) = Lit l
substituteAll vs es b (Comb combtype c exps) =
                 Comb combtype c (map (substituteAll vs es b) exps)
substituteAll vs es b (Let bindings exp) =
                 Let (map (\(x,e)->(x+b,substituteAll vs es b e)) bindings)
                     (substituteAll vs es b exp)
substituteAll vs es b (Free vars e) =
                 Free (map (+b) vars) (substituteAll vs es b e)
substituteAll vs es b (Or e1 e2) =
                 Or (substituteAll vs es b e1) (substituteAll vs es b e2)
substituteAll vs es b (Case ctype e cases) =
   Case ctype (substituteAll vs es b e) (map (substituteAllCase vs es b) cases)
substituteAll vs es b (Typed e t) = Typed (substituteAll vs es b e) t

substituteAllCase :: [Int] -> [Expr] -> Int -> BranchExpr -> BranchExpr
substituteAllCase vs es b (Branch (Pattern l pvs) e) =
                 Branch (Pattern l (map (+b) pvs)) (substituteAll vs es b e)
substituteAllCase vs es b (Branch (LPattern l) e) =
                 Branch (LPattern l) (substituteAll vs es b e)


-------- Definition of some orderings:
leqOp :: OpDecl -> OpDecl -> Bool
leqOp (Op (_,op1) _ p1) (Op (_,op2) _ p2) = p1>p2 || p1==p2 && op1<=op2

leqType :: TypeDecl -> TypeDecl -> Bool
leqType t1 t2 = (tname t1) <= (tname t2)
 where tname (Type    (_,tn) _ _ _) = tn
       tname (TypeSyn (_,tn) _ _ _) = tn

leqFunc :: FuncDecl -> FuncDecl -> Bool
leqFunc (Func (_,f1) _ _ _ _) (Func (_,f2) _ _ _ _) = f1 <= f2

---------------------------------------------------------------------------
--- Show FlatCurry module in pretty-printed form
showFlatCurry :: Prog -> String
showFlatCurry = pPrint . ppProg defaultOptions

-- Show individual functions:
showFuncDeclAsCurry :: FuncDecl -> String
showFuncDeclAsCurry fd =
  showCurryFuncDecl (showQNameInModule (funcModule fd))
                    (showQNameInModule (funcModule fd)) fd

showFuncDeclAsFlatCurry :: FuncDecl -> String
showFuncDeclAsFlatCurry fd = pPrint (ppFuncDecl opts fd)
  where opts = defaultOptions { currentModule = funcModule fd }

funcModule :: FuncDecl -> String
funcModule fd = fst (funcName fd)

-----------------------------------------------------------------------------
