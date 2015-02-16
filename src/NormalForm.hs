{-|
Module      : NormalForm
Description : Syntactic transformations to render formulas in normal form
Copyright   : (c) Alex Nelson, 2015
License     : MIT
Maintainer  : pqnelson@gmail.com
Stability   : experimental
Portability : POSIX

Whenever we want to convert a given formula to normal form, it's best to
separate this from the rest of the code.
-}
module NormalForm
       (
         toNNF
       , toNENF
       , toCNF
       , toDNF
       , foldlConj
       , foldrDisj
       , trivial
       , naiveToDNF
       , nnfToDNF
       , pureDNF
       , defCNFClauses
       , toDefCNF
       , maxVarIndex
       )
       where
import qualified Data.Map as Map
import qualified Data.List
import qualified Set
import Prelude hiding (negate)
import Data.Maybe
import Formula

toNNF' :: Formula -> Formula
toNNF' fm = case fm of
  And p q           -> And (toNNF' p) (toNNF' q)
  Or p q            -> Or (toNNF' p) (toNNF' q)
  Implies p q       -> Or (toNNF' (Not p)) (toNNF' q)
  Iff p q           -> Or (And (toNNF' p) (toNNF' q))
                          (And (toNNF' (Not p)) (toNNF' (Not q)))
  Not (Not p)       -> toNNF' p
  Not (And p q)     -> Or (toNNF' (Not p)) (toNNF' (Not q))
  Not (Or p q)      -> And (toNNF' (Not p)) (toNNF' (Not q))
  Not (Implies p q) -> And (toNNF' p) (toNNF' (Not q))
  Not (Iff p q)     -> Or (And (toNNF' (Not p)) (toNNF' q))
                          (And (toNNF' p) (toNNF' (Not q)))
  _                 -> fm

-- | Converts a formula to negation normal form.
toNNF :: Formula -> Formula
toNNF = toNNF' . simplifyProp

toNENF' :: Formula -> Formula
toNENF' fm = case fm of
  Not (Not p)       -> toNENF' p
  Not (And p q)     -> Or (toNENF' (Not p)) (toNENF' (Not q))
  Not (Implies p q) -> And (toNENF' p) (toNENF' (Not q))
  Not (Iff p q)     -> Iff (toNENF' p) (toNENF' (Not q))
  And p q           -> And (toNENF' p) (toNENF' q)
  Or p q            -> Or (toNENF' p) (toNENF' q)
  Implies p q       -> Or (toNENF' (Not p)) (toNENF' q)
  Iff p q           -> Iff (toNENF' p) (toNENF' q)
  _                 -> fm

-- | Converts a formula to pseudo-negation normal form...it does not
-- alter 'Iff' connectives.
--
-- >>> toNENF (Iff (Atom "a") (Atom "b"))
-- (Iff a b)
-- >>> toNENF (Implies (Iff (Atom "a") (Atom "b")) (Atom "c"))
-- Or (Iff a (Not b)) c
toNENF :: Formula -> Formula
toNENF = toNENF' . simplifyProp

-- | Given a list of formulas, apply `foldl And T` to them to get a single
-- formula.
--
-- >>> foldlConj [(Atom "a"), (Atom "b"), (Atom "c")]
-- And (And (And T (Atom "c")) (Atom "b")) (Atom "a")
foldlConj :: [Formula] -> Formula
foldlConj [] = T
foldlConj (f:fs) = And (foldlConj fs) f

-- | Given a list of formulas, apply `foldr Or F` to them to get a single
-- formula.
--
-- >>> foldrDisj [(Atom "a"), (Atom "b"), (Atom "c")]
-- Or (Atom "a") (Or (Atom "b") (Or (Atom "c") F))
foldrDisj :: [Formula] -> Formula
foldrDisj = foldr Or F

-- | Get all valuations which satisfy some property @prop@
allValuationsSatisfying :: (Valuation -> Bool) -> Valuation -> [PropVar] -> [Valuation]
allValuationsSatisfying p v [] = [v | p v]
allValuationsSatisfying p v (a:pvs) =
  allValuationsSatisfying p ((a |-> False) v) pvs
  ++ allValuationsSatisfying p ((a |-> True) v) pvs

-- | Given a list of propositional variables and a fixed valuation @v@, map
-- the propositional variables through
-- @if eval (Atom _) v then (toAtom _) else (Not (toAtom _))@
-- and then 'foldlConj' the resulting formulas all together 
makeLiterals :: [PropVar] -> Valuation -> Formula
makeLiterals ats v = foldlConj (map ((\p -> if eval p v then p else Not p)
                                     . Atom)
                                ats)

-- | Converts a formula to DNF by examining the truth table of the given
-- formula. As the name suggests, this is a naive approach, and shouldn't
-- be used in production.
naiveToDNF :: Formula -> Formula
naiveToDNF fm =
  let ats = atoms fm
      satVals = allValuationsSatisfying (eval fm) (const False) ats
  in foldrDisj (map (makeLiterals ats) satVals)

-- | Distributes 'And' over 'Or' in formulas
distrib :: Formula -> Formula
distrib (And p (Or q r)) = Or (distrib (And p q)) (distrib (And p r))
distrib (And (Or p q) r) = Or (distrib (And p r)) (distrib (And q r))
distrib fm = fm

-- | Converts an NNF to a DNF by iteratively applying 'Formula.distrib'.
nnfToDNF :: Formula -> Formula
nnfToDNF (And p q) = distrib (And (nnfToDNF p) (nnfToDNF q))
nnfToDNF (Or p q) = Or (nnfToDNF p) (nnfToDNF q)
nnfToDNF fm = fm

--- Helper function
allPairs :: Ord c => (a -> b -> c) -> [a] -> [b] -> [c]
allPairs f xs ys = Set.setify [f x y | x <- xs, y <- ys]

-- | Given a formula in NNF, convert it to a list of clauses, where each
-- clause is represented as a list of literals.
pureDNF :: Formula -> [[Formula]]
pureDNF fm = case fm of
  And p q -> Set.setify $ allPairs Set.union (pureDNF p) (pureDNF q)
  Or p q  -> pureDNF p `Set.union` pureDNF q
  _       -> [[fm]]

-- | A clause is trivial if it contains some literal and its negation.
trivial :: [Formula] -> Bool
trivial literals =
  let (pos, negs) = Data.List.partition isPositive literals
  in Set.intersect (map negate negs) pos /= []

--- Helper function, makes sure the clauses don't include proper subsets
--- of each other
subsume :: [[Formula]] -> [[Formula]]
subsume cls = filter (\cl -> not (any (`Set.isProperSubset` cl)
                                  cls)) cls

-- | Takes a given formula, then produces a list of clauses which are
-- nontrivial and no clause is subsumed in any other.
simpDNF :: Formula -> [[Formula]]
simpDNF F = []
simpDNF T = [[]]
simpDNF fm = (subsume . filter (not . trivial) . pureDNF . toNNF) fm

-- | Determines the DNF using sets, then collects the clauses by
-- iteratively joining them @Or@-d together.
toDNF :: Formula -> Formula
toDNF fm = foldrDisj (map foldlConj (simpDNF fm))

pureCNF :: Formula -> [[Formula]]
pureCNF = map (map negate) . pureDNF . toNNF . negate

simpCNF :: Formula -> [[Formula]]
simpCNF F = []
simpCNF T = [[]]
simpCNF fm = let cjs = filter (not . trivial) (pureCNF $ toNNF fm)
             in filter (\c -> not $ any (`Set.isProperSubset` c) cjs) cjs

-- | Converts a formula to conjunctive normal form.
toCNF :: Formula -> Formula
toCNF fm = foldlConj (map foldrDisj (simpCNF fm))

-- | Helper functions for toDefCNF
maybeRead :: Read a => String -> Maybe a
maybeRead = fmap fst . listToMaybe . reads

-- | Given a prefix, a string, and a possible candidate for the index
-- counter value, check if the string looks like 'prefix ++ (number)'.
-- If so, return the maximum of the parsed number and the candidate
-- value parameter; otherwise, just return the candidate value.
maxVarIndex :: String -> String -> Int -> Int
maxVarIndex pfx s n =
  let m = length pfx
      l = length s
  in if l <= m || take m s /= pfx
     then n
     else let s' = take (l-m) (drop m s)
          in case maybeRead s'
             of Nothing -> n
                Just n' -> max n n'

makeProp :: Int -> (Formula, Int)
makeProp n = (Atom ("p_" ++ show n), n+1)

-- | A triple tracking the formula to be transformed,
-- definitions made so far (as a dictionary, well 'Data.Map'),
-- and the current variable index counter.
type Trip = (Formula, Map.Map Formula (Formula, Formula), Int)

-- | Iteratively transform a formula, represented as a 'Trip', into
-- set-based definitional conjunctive normal form.
mainCNF :: Trip -> Trip
mainCNF (trip@(fm, _, _)) = case fm of
  And p q -> defstep And (p, q) trip
  Or p q  -> defstep Or (p, q) trip
  Iff p q -> defstep Iff (p, q) trip
  _       -> trip

-- | Takes a binary connective, an ordered pair of formulas, and a 'Trip'
-- then transforms this into another 'Trip'
defstep :: (Formula -> Formula -> Formula) -> (Formula, Formula) -> Trip -> Trip
defstep op (p, q) (_, defs, n) =
  let (fm1, defs1, n1) = mainCNF (p, defs, n)
      (fm2, defs2, n2) = mainCNF (q, defs1, n1)
      fm' = op fm1 fm2
  in case Map.lookup fm' defs2 of
      Just (v, _) -> (v, defs, n2)
      Nothing -> (v, Map.insert fm' (v, Iff v fm') defs2, n3)
        where (v, n3) = makeProp n2


-- | Transform the clauses to definitional CNF, and return the set-based
-- representation of the given formula.
mkDefCNF :: (Trip -> Trip) -> Formula -> [[Formula]]
mkDefCNF fn fm =
  let fm' = toNENF fm
      n = 1 + foldr (maxVarIndex "p_" . show) 0 (atoms fm')
      (fm'', defs, _) = fn (fm', Map.empty, n)
      deflist = map (snd . snd) (Map.toList defs)
  in Set.unions $ simpCNF fm'' : map simpCNF deflist

-- | Converts a formula to definitional conjunctive normal form.
--
-- | In general, fails to produce a formula logically equivalent to the input
--
-- prop> not $ isTautology (Iff fm (naiveToDefCNF fm))
naiveToDefCNF :: Formula -> Formula
naiveToDefCNF fm = foldlConj $ map foldrDisj $ mkDefCNF mainCNF fm

-- | A generalized version of defstep
subCNF :: (Trip -> Trip) -> (Formula -> Formula -> Formula)
          -> (Formula, Formula) -> Trip -> Trip
subCNF subfn op (p, q) (_, defs, n) =
  let (fm1, defs1, n1) = subfn (p, defs, n)
      (fm2, defs2, n2) = subfn (q, defs1, n1)
  in (op fm1 fm2, defs2, n2)

orCNF :: Trip -> Trip
orCNF trip@(fm, _, _) = case fm of
  Or p q -> subCNF orCNF Or (p, q) trip
  _      -> mainCNF trip

andCNF :: Trip -> Trip
andCNF trip@(fm, _, _) = case fm of
  And p q -> subCNF andCNF And (p, q) trip
  _       -> orCNF trip

-- | Given a formula, return the set-based representation of it in
-- definition conjunctive normal form.
defCNFClauses :: Formula -> [[Formula]]
defCNFClauses = mkDefCNF andCNF

-- | A slightly optimized way to convert a formula to definitional CNF.
toDefCNF :: Formula -> Formula
toDefCNF = foldlConj . map foldrDisj . defCNFClauses
