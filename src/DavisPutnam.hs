{-|
Module      : DavisPutnam
Description : Implementation of DP and DPLL algorithms
Copyright   : (c) Alex Nelson, 2015
License     : MIT
Maintainer  : pqnelson@gmail.com
Stability   : experimental
Portability : POSIX

A slightly optimized method for checking satisfiability.
-}

module DavisPutnam
       (
         dp
       , isTautology
       , isSatisfiable
       , isUnsatisfiable
       ) where
import qualified Data.List
import qualified Set
import Prelude hiding (negate)
import Formula hiding (isTautology, isSatisfiable, isUnsatisfiable)

isUnitClause :: [Formula] -> Bool
isUnitClause (_:t) = null t
isUnitClause _     = False

-- | The one literal rule for the Davis-Putnam algorithm.
oneLiteralRule :: [[Formula]] -> Maybe [[Formula]]
oneLiteralRule clauses = case Data.List.find isUnitClause clauses of
                          Nothing -> Nothing
                          Just [u] -> Just (Set.image (Set.\\ [u']) clauses')
                            where u' = negate u
                                  clauses' = filter (notElem u) clauses
                          _ -> error "oneLiteralRule reached impossible state"

affirmitiveNegativeRule :: [[Formula]] -> Maybe [[Formula]]
affirmitiveNegativeRule clauses =
  let (neg', pos) = Data.List.partition isNegative (Set.unions clauses)
      neg = map negate neg'
      posOnly = Set.difference pos neg
      negOnly = Set.difference neg pos
      pure = Set.union posOnly (map negate negOnly)
  in case pure of
      [] -> Nothing
      _ -> Just (filter (null . Set.intersect pure) clauses)

trivial :: [Formula] -> Bool
trivial literals =
  let (pos, neg) = Data.List.partition isPositive literals
  in Set.intersect pos (map negate neg) /= []

resolveOn :: Formula -> [[Formula]] -> [[Formula]]
resolveOn p clauses =
  let p' = negate p
      (pos, notPos) = Data.List.partition (elem p) clauses
      (neg, other) = Data.List.partition (elem p') notPos
      pos' = map (filter (/= p)) pos
      neg' = map (filter (/= p')) neg
      res0 = [ c `Set.union` d | c <- pos', d <- neg']
  in Set.union other (filter (not . trivial) res0)

-- | A crude heuristic to determine which literal to use.
findBlowup :: [[Formula]] -> Formula -> (Int, Formula)
findBlowup cls l = let m = length(filter (elem l) cls)
                       n = length(filter (elem (negate l)) cls)
                   in (m*n - m - n, l)

resolutionRule :: [[Formula]] -> [[Formula]]
resolutionRule clauses =
  let pvs = filter isPositive (Set.unions clauses)
      (_, p) = Data.List.minimum $ map (findBlowup clauses) pvs
  in resolveOn p clauses

dp :: [[Formula]] -> Bool
dp [] = True
dp clauses = if [] `elem` clauses
             then False
             else case oneLiteralRule clauses of
             Just clauses' -> dp clauses'
             Nothing -> case affirmitiveNegativeRule clauses of
                         Just clauses' -> dp clauses'
                         Nothing -> dp(resolutionRule clauses)

isSatisfiable :: Formula -> Bool
isSatisfiable = dp . defCNFClauses

isUnsatisfiable :: Formula -> Bool
isUnsatisfiable = not . isSatisfiable

isTautology :: Formula -> Bool
isTautology fm = not $ isSatisfiable (Not fm)
