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

frequencies :: [[Formula]] -> Formula -> (Int, Formula)
frequencies clauses p = let m = length $ filter (elem p) clauses
                            n = length $ filter (elem (Not p)) clauses
                        in (m+n, p)

getLiterals :: [[Formula]] -> [Formula]
getLiterals clauses = let (pos,neg) = Data.List.partition isPositive
                                      $ Set.unions clauses
                      in Set.union pos (map negate neg)

dpll :: [[Formula]] -> Bool
dpll [] = True
dpll clauses = if [] `elem` clauses
               then False
               else case oneLiteralRule clauses of
                  Just clauses' -> dpll clauses'
                  Nothing -> case affirmitiveNegativeRule clauses of
                    Just clauses' -> dpll clauses'
                    Nothing -> let pvs = getLiterals clauses
                                   lcounts = map (frequencies clauses) pvs 
                                   (_, p) = Data.List.maximum lcounts
                               in dpll (Set.insert [p] clauses)
                                  || dpll (Set.insert [negate p] clauses)

{-
  The following code is idiosyncratic, and has to do with backtracking
  in the DPLL algorithm.
-}

data TrailMix = Deduced | Guessed deriving (Eq, Ord)

type Trail = (Formula, TrailMix)
type Clauses = [[Formula]]
type Clause = [Formula]

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

litAbs :: Formula -> Formula
litAbs (Not p) = p
litAbs fm = fm

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

-- | Unit propagation using the newfangled 'Trail'.
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

-- | The DPLL algorithm with backtracking.
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

-- | Test for satisfiability using 'dplii'
dplisat :: Formula -> Bool
dplisat fm = dpli (defCNFClauses fm) []

-- | Test for validity using 'dplii'
dplitaut :: Formula -> Bool
dplitaut = not . dplisat . Not

backjump :: Clauses -> Formula -> [Trail] -> [Trail]
backjump cls p trail@((q, Guessed):tt) =
  let (cls', trail') = btUnitPropagation (cls, (p,Guessed):tt)
  in if [] `elem` cls'
     then backjump cls p tt
     else trail
backjump _ _ trail = trail

guessedLiterals :: [Trail] -> [Trail]
guessedLiterals ((p, Guessed):tt) = (p, Guessed):guessedLiterals tt
guessedLiterals ((_, Deduced):tt) = guessedLiterals tt
guessedLiterals [] = []

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


isSatisfiable :: Formula -> Bool
isSatisfiable fm = dplb (defCNFClauses fm) []

isUnsatisfiable :: Formula -> Bool
isUnsatisfiable = not . isSatisfiable

isTautology :: Formula -> Bool
isTautology fm = not $ isSatisfiable (Not fm)
