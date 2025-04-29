-----------------------------------------------------------------------------
--- A few base functions for analysing dependencies in FlatCurry programs:
---
--- @author Michael Hanus
--- @version April 2025
-----------------------------------------------------------------------------

module CurryBrowseAnalysis.Dependency
  ( analyseWithDependencies, indirectlyDependent
  , funcsInExpr, callsDirectly, externalDependent
  , dependencyGraphs, localDependencyGraphs
  ) where

import Prelude hiding  ( empty )
import Data.Maybe      ( fromJust )

import FlatCurry.Types
import Data.Set        ( Set, member, empty, insert, toList, union )

-- Generic global function analysis where the property of each function is a combination
-- of a property of the function and all its dependent functions.
-- 1. parameter: a function that associates a property to each function declaration
-- 2. parameter: an operation to combine the properties of function/dependent functions
analyseWithDependencies :: (FuncDecl->a) -> ([a]->a) -> [FuncDecl] -> [(QName,a)]
analyseWithDependencies funproperty combine funs = map anaFun alldeps
  where
    anaFun (name,depfuns) = (name, combine (map (lookupProp funprops) (name:depfuns)))

    funprops = map (\f->(funcName f, funproperty f)) funs

    alldeps = indirectlyDependent funs

    lookupProp :: [(QName,a)] -> QName -> a
    lookupProp fprops fun = fromJust (lookup fun fprops)

    funcName (Func fname _ _ _ _) = fname


-- external functions on which a function depends
externalDependent :: [FuncDecl] -> [(QName,[QName])]
externalDependent funcs =
  map (\ (f,fs)->(f,filter (`elem` externalFuncs) fs))
      (indirectlyDependent funcs)
 where
   externalFuncs = concatMap getExternal funcs

   getExternal (Func _ _ _ _ (Rule _ _)) = []
   getExternal (Func f _ _ _ (External _)) = [f]


-- Computes the list of indirect dependencies for all functions.
-- Argument: a list of function declarations
-- Result: a list of pairs of qualified functions names and the corresponding
--         called functions
indirectlyDependent :: [FuncDecl] -> [(QName,[QName])]
indirectlyDependent funs = map (\ (f,ds) -> (f,toList ds))
                               (depsClosure (map directlyDependent funs))

-- list of direct dependencies for a function
callsDirectly :: FuncDecl -> [QName]
callsDirectly fun = toList (snd (directlyDependent fun))

-- set of direct dependencies for a function
directlyDependent :: FuncDecl -> (QName,Set QName)
directlyDependent (Func f _ _ _ (Rule _ e))   = (f,funcSetOfExpr e)
directlyDependent (Func f _ _ _ (External _)) = (f,emptySet)

-- compute the transitive closure of all dependencies based on a list of
-- direct dependencies:
depsClosure :: [(QName,Set QName)] -> [(QName,Set QName)]
depsClosure directdeps = map (\(f,ds)->(f,closure ds (toList ds)))
                             directdeps
 where
  closure olddeps [] = olddeps
  closure olddeps (f:fs) =
     let newdeps = filter (\e->not (member e olddeps))
                          (toList (maybe emptySet id (lookup f directdeps)))
      in closure (foldr insert olddeps newdeps) (newdeps++fs)

-- Computes the list of all direct dependencies for all functions.
-- This is useful to represent the dependency graph for each function.
-- Argument: a list of function declarations
-- Result: a list of pairs of qualified functions names and the corresponding list of
--         direct dependencies for all functions on which this functions depend
dependencyGraphs :: [FuncDecl] -> [(QName,[(QName,[QName])])]
dependencyGraphs funs =
  let directdeps = map directlyDependent funs
   in map (\(f,ds) -> (f,map (\g->(g,toList (fromJust (lookup g directdeps))))
                             (toList (insert f ds))))
          (depsClosure directdeps)

-- Computes for all functions the list of all direct local dependencies, i.e.,
-- dependencies occurring in the module where the function is defined.
-- Thus, dependencies outside the module are not represented.
-- This is useful to represent the local dependency graph for each function.
-- Argument: a list of function declarations
-- Result: a list of pairs of qualified functions names and the corresponding list of
--         direct local dependencies for all functions on which this functions depend
localDependencyGraphs :: [FuncDecl] -> [(QName,[(QName,[QName])])]
localDependencyGraphs funs =
  let directdeps = map directlyDependent funs
   in map (\(f,ds) -> (f,map (\g->(g,if fst f == fst g
                                     then toList (fromJust (lookup g directdeps))
                                     else []))
                             (toList (insert f ds))))
          (localDepsClosure directdeps)

-- compute the transitive closure of all local dependencies based on a list of
-- direct dependencies:
localDepsClosure :: [(QName,Set QName)] -> [(QName,Set QName)]
localDepsClosure directdeps =
  map (\(f,ds)->(f,closure (fst f) ds (toList ds))) directdeps
 where
  closure _ olddeps [] = olddeps
  closure mod olddeps (f:fs)
   | mod == fst f  -- f is local in this module: add dependencies
    = let newdeps = filter (\e->not (member e olddeps))
                           (toList (maybe emptySet id (lookup f directdeps)))
       in closure mod (foldr insert olddeps newdeps) (newdeps++fs)
   | otherwise = closure mod olddeps fs

-- Gets a list of all functions (including partially applied functions)
-- called in an expression:
funcsInExpr :: Expr -> [QName]
funcsInExpr e = toList (funcSetOfExpr e)

-- Gets the set of all functions (including partially applied functions)
-- called in an expression:
funcSetOfExpr :: Expr -> Set QName
funcSetOfExpr (Var _) = emptySet
funcSetOfExpr (Lit _) = emptySet
funcSetOfExpr (Comb ct f es) =
  if isConstructorComb ct then unionMap funcSetOfExpr es
                          else insert f (unionMap funcSetOfExpr es)
funcSetOfExpr (Free _ e) = funcSetOfExpr e
funcSetOfExpr (Let bs e) = union (unionMap (funcSetOfExpr . snd) bs) (funcSetOfExpr e)
funcSetOfExpr (Or e1 e2) = union (funcSetOfExpr e1) (funcSetOfExpr e2)
funcSetOfExpr (Case _ e bs) = union (funcSetOfExpr e) (unionMap funcSetOfBranch bs)
                     where funcSetOfBranch (Branch _ be) = funcSetOfExpr be
funcSetOfExpr (Typed e _) = funcSetOfExpr e

isConstructorComb :: CombType -> Bool
isConstructorComb ct = case ct of
  ConsCall       -> True
  ConsPartCall _ -> True
  _              -> False

unionMap :: (a -> Set QName) -> [a] -> Set QName
unionMap f = foldr union emptySet . map f

emptySet :: Set QName
emptySet = empty

leqQName :: QName -> QName -> Bool
leqQName (m1,n1) (m2,n2) = m1 ++ ('.':n1) <= m2 ++ ('.':n2)

-- end of Dependency

