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
       , dpll
       ) where
import qualified Data.List
import qualified Data.Map as Map
import qualified Set
import Data.Maybe
import Prelude hiding (negate)
import Formula hiding (isTautology, isSatisfiable, isUnsatisfiable)
import NormalForm

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

-- | Attempts to eliminate literals that show up as _only positive_ or
-- _only negative_. If this eliminates everything, it will return
-- 'Nothing'; otherwise, it returns 'Just' the transformed clauses.
affirmativeNegativeRule :: [[Formula]] -> Maybe [[Formula]]
affirmativeNegativeRule clauses =
  let (neg', pos) = Data.List.partition isNegative (Set.unions clauses)
      neg = map negate neg'
      posOnly = Set.difference pos neg
      negOnly = Set.difference neg pos
      pure = Set.union posOnly (map negate negOnly)
  in case pure of
      [] -> Nothing
      _ -> Just (filter (null . Set.intersect pure) clauses)

-- | Gets rid of a literal (first argument) from the clauses (second argument)
-- producing a new set of clauses without the literal showing up at all.
-- Warning: the result could be huge.
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

-- | A one-step resolution rule, which 'resolveOn' the literal
-- determined by minimizing 'findBlowup' on the clauses.
resolutionRule :: [[Formula]] -> [[Formula]]
resolutionRule clauses =
  let pvs = filter isPositive (Set.unions clauses)
      (_, p) = Data.List.minimum $ map (findBlowup clauses) pvs
  in resolveOn p clauses

-- | The basic structure of the Davis-Putnam and DPLL algorithms are the
-- same, they just differ with respect to the splitting rule. So,
-- refactor out the similar structure into a helper function, and have
-- each algorithm pass in its own splitting rule.
dpSkeleton :: [[Formula]] -> ([[Formula]] -> Bool) -> Bool
dpSkeleton [] _ = True
dpSkeleton clauses isSatisfiable =
  if [] `elem` clauses
  then False
  else case oneLiteralRule clauses of
        Just clauses' -> dpSkeleton clauses' isSatisfiable
        Nothing -> case affirmativeNegativeRule clauses of
                    Just clauses' -> dpSkeleton clauses' isSatisfiable
                    Nothing -> isSatisfiable clauses

-- | The original Davis-Putnam algorithm, in all its glory.
dp :: [[Formula]] -> Bool
dp clauses = dpSkeleton clauses (dp . resolutionRule)

-- | Given the clauses and a literal, return an ordered pair '(Int, Formula)'
-- which gives how many times the literal (or its negation) appears in
-- the clauses, and the literal being checked for.
frequencies :: [[Formula]] -> Formula -> (Int, Formula)
frequencies clauses p = let m = length $ filter (elem p) clauses
                            n = length $ filter (elem (Not p)) clauses
                        in (m+n, p)

-- | Return all literals that occur in the formula, negated literals are
-- transformed to be positive.
getLiterals :: [[Formula]] -> [Formula]
getLiterals clauses = let (pos,neg) = Data.List.partition isPositive
                                      $ Set.unions clauses
                      in Set.union pos (map negate neg)

-- | The unique component to the DPLL modifies the splitting rule.
splittingRule :: [[Formula]] -> Bool
splittingRule clauses = let pvs = getLiterals clauses
                            lcounts = map (frequencies clauses) pvs 
                            (_, p) = Data.List.maximum lcounts
                        in dpll (Set.insert [p] clauses)
                           || dpll (Set.insert [negate p] clauses)

-- | The 1962 Davis-Putnam rule, which is slightly slicker.
-- See Davis, Logemann, and Loveland's "A Machine Program for Theorem Proving"
-- Comm. of the ACM, vol 5, no 7 (1962) pp 394-397 for the original reference.
dpll :: [[Formula]] -> Bool
dpll clauses = dpSkeleton clauses splittingRule

{-
  The following code is idiosyncratic, and has to do with backtracking
  in the DPLL algorithm.
-}

-- | Keep track of each step in the trail when we 'Guessed' or 'Deduced'
-- a value in the valuation.
data TrailMix = Deduced | Guessed deriving (Eq, Ord)

-- | The Trail is just a step in the trail, keeping track of a 'Formula'
-- and a 'TrailMix' explanation.
type Trail = (Formula, TrailMix)
type Clauses = [[Formula]]

-- | Updates the clauses to remove negated literals which do not belong to
-- the trail, as specified by the map.
removeTrailedNegLits :: Map.Map Formula Formula -> Clauses -> Clauses
removeTrailedNegLits m = map (filter (not . (`Map.member` m) . negate))

-- | Given a 'Map.Map Formula Formula', and a list '[Formula]',
-- for each element in our list, check if it's a member of the map;
-- if so, map it to 'Just fm', otherwise map it to 'Nothing'.
maybeInclude :: Map.Map Formula Formula -> [Formula] -> [Maybe Formula]
maybeInclude m (c:cls) = if Map.member c m
                         then Nothing : maybeInclude m cls
                         else Just c : maybeInclude m cls
maybeInclude _ [] = []

-- | Get all the units from the clauses which are undefined according
-- to our dictionary.
undefinedUnits :: Map.Map Formula Formula -> Clauses -> [Formula]
undefinedUnits m = Set.unions . map (catMaybes . maybeInclude m)

-- | We keep track of the trail history in the @Map.Map Formula Formula@
-- parameter, the given clause is the first parameter, and the @[Trail]@
-- stars as itself.
unitSubpropagate :: (Clauses, Map.Map Formula Formula, [Trail])
                    -> (Clauses, Map.Map Formula Formula, [Trail])
unitSubpropagate (cls, m, trail) =
  let cls' = removeTrailedNegLits m cls
      newunits = undefinedUnits m cls'
  in if null newunits
     then (cls', m, trail)
     else let trail' = foldr (\l t -> (l, Deduced):t) trail newunits
              m' = foldr (\l mp -> Map.insert l l mp) m newunits
          in unitSubpropagate (cls', m', trail')

-- | Unit propagation using the newfangled 'Trail'. It amounts to making
-- 'unitSubpropagate' doing all the work, and 'btUnitPropagation'
-- getting all the glory.
btUnitPropagation :: (Clauses, [Trail]) -> (Clauses, [Trail])
btUnitPropagation (cls, trail) =
  let m = foldr (\(l,_) mp -> Map.insert l l mp) Map.empty trail
      (cls', _, trail') = unitSubpropagate (cls, m, trail)
  in (cls', trail')

-- | Backtrack the trail until we found the last guess which caused problems.
backtrack :: [Trail] -> [Trail]
backtrack ((_, Deduced):tt) = backtrack tt
backtrack tt = tt
--- backtrack [] = []

-- | All the literals in the clauses not yet assigned to the trail yet.
unassigned :: Clauses -> [Trail] -> [Formula]
unassigned cls trail = Set.difference
                       (Set.unions (Set.image (Set.image litAbs) cls))
                       (Set.image (litAbs . fst) trail)

-- | The iterative DPLL algorithm with backtracking.
dpli :: Clauses -> [Trail] -> Bool
dpli cls trail =
  let (cls', trail') = btUnitPropagation (cls, trail)
  in if [] `elem` cls'                            --- if we get the empty clause
     then case backtrack trail of                 --- backtrack until
           (p, Guessed):tt                        --- we guessed last
             -> dpli cls ((negate p, Deduced):tt) --- and guess again!
           _ -> False                             --- unless we can't
     else case unassigned cls trail' of           --- otherwise
           [] -> True   --- it's satisfiable if there are no unassigned literals
           ps -> let (_, p) = Data.List.maximum
                              $ map (frequencies cls') ps
                 in dpli cls ((p, Guessed):trail') --- recur with the next
                                                   --- best guess

-- | Test for satisfiability using 'dpli'
dplisat :: Formula -> Bool
dplisat fm = dpli (defCNFClauses fm) []

-- | Test for validity using 'dpli'
dplitaut :: Formula -> Bool
dplitaut = not . dplisat . Not

-- | Given a set of clauses, a literal, and a trail, go back through the
-- trail as far as possible while ensuring the most recent decision @p@
-- (the second argument) still leads to a conflict. It returns this
-- modified 'Trail' list.
backjump :: Clauses -> Formula -> [Trail] -> [Trail]
backjump cls p trail@((q, Guessed):tt) =
  let (cls', trail') = btUnitPropagation (cls, (p,Guessed):tt)
  in if [] `elem` cls'
     then backjump cls p tt
     else trail
backjump _ _ trail = trail

-- | Given a list of 'Trail' elements, filter out all the 'Guessed' nodes.
-- It will return a list of 'Trail', possibly empty if there were no 'Guessed'
-- elements.
guessedLiterals :: [Trail] -> [Trail]
guessedLiterals ((p, Guessed):tt) = (p, Guessed):guessedLiterals tt
guessedLiterals ((_, Deduced):tt) = guessedLiterals tt
guessedLiterals [] = []

-- | The DPLL with backjumping and conflict learning.
dplb :: Clauses -> [Trail] -> Bool
dplb cls trail =
  let (cls', trail') = btUnitPropagation (cls, trail)
  in if [] `elem` cls'
     then case backtrack trail of
           (p, Guessed):tt ->
             let trail'' = backjump cls p tt
                 declits = guessedLiterals trail''
                 conflict = Set.insert (negate p)
                            (Set.image (negate . fst) declits)
             in dplb (conflict:cls) (Set.insert (negate p, Deduced) trail'')
           _ -> False
     else case unassigned cls trail' of
           [] -> True
           ps -> let (_,p) = Data.List.maximum
                             $ map (frequencies cls') ps
                 in dplb cls (Set.insert (p, Guessed) trail')

-- | Uses our newfangled 'dplb' algorithm to test for satisfiability.
isSatisfiable :: Formula -> Bool
isSatisfiable fm = dplb (defCNFClauses fm) []

-- | Simply the complement of 'isSatisfiable'
isUnsatisfiable :: Formula -> Bool
isUnsatisfiable = not . isSatisfiable

-- | Checks if the negated input 'isUnsatisfiable'.
isTautology :: Formula -> Bool
isTautology = isUnsatisfiable . Not
