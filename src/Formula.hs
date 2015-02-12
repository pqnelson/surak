{-|
Module      : Formula
Description : Logical formula related code
Copyright   : (c) Alex Nelson, 2015
License     : MIT
Maintainer  : pqnelson@gmail.com
Stability   : experimental
Portability : POSIX

This code is related to all the formula manipulation. So far, it is just
propositional calculus, but eventually it will be extended to first-order
logic.
-}
module Formula
       (
         PropVar
       , Formula(..)
       , Valuation
       , atoms
       , eval
       , onAllValuations
       , isTautology
       , isSatisfiable
       , isUnsatisfiable
       , isLiteral
       , isNegative
       , isPositive
       , dual
       , simplifyProp
       , propSubstitute
       , toNNF
       , toNENF
       , foldlConj
       , foldrDisj
       , naiveToDNF
       , nnfToDNF
       , pureDNF
       , toDNF
       , toCNF
       ) where
import Prelude hiding (negate)
import qualified Set
import qualified Data.List

-- | We're working with propositional calculus in this version, so we
-- need to keep track of propositional variables. 
type PropVar = String

{-|
  A formula is a simple tree, whose leaves are 'T', 'F', and 'Atom'
  (true, false, and atomic propositions), and nodes are the binary
  connectives & negation.
-}
data Formula = F
             | T
             | Atom PropVar
             | Not Formula
             | And Formula Formula
             | Or Formula Formula
             | Implies Formula Formula
             | Iff Formula Formula
               deriving (Eq, Ord)

instance Show Formula where
  show F = "F"
  show T = "T"
  show (Atom x) = x
  show (Not p) = "(Not "++ show p ++ ")"
  show (And p q) = "(And "++show p++" "++show q++")"
  show (Or p q) = "(Or "++show p++" "++show q++")"
  show (Implies p q) = "(Implies "++show p++" "++show q++")"
  show (Iff p q) = "(Iff "++show p++" "++show q++")"

-- | A 'Formula' is-a tree, but we care about the 'Atom' leaves. This
-- just maps the atoms, while respecting the tree-structure.
mapAtoms :: (PropVar -> Formula) -> Formula -> Formula
mapAtoms _ F             = F
mapAtoms _ T             = T
mapAtoms f (Atom x)      = f x
mapAtoms f (Not p)       = Not (mapAtoms f p)
mapAtoms f (And p q)     = And (mapAtoms f p) (mapAtoms f q)
mapAtoms f (Or p q)      = Or (mapAtoms f p) (mapAtoms f q)
mapAtoms f (Implies p q) = Implies (mapAtoms f p) (mapAtoms f q)
mapAtoms f (Iff p q)     = Iff (mapAtoms f p) (mapAtoms f q)

-- | Get all the propositional variables in a formula, with duplicates;
-- a helper function for 'atoms' 
rawAtoms :: Formula -> [PropVar]
rawAtoms f = case f of
  F           -> []
  T           -> []
  Atom x      -> [x]
  Not p       -> rawAtoms p
  And p q     -> rawAtoms p ++ rawAtoms q
  Or p q      -> rawAtoms p ++ rawAtoms q
  Implies p q -> rawAtoms p ++ rawAtoms q
  Iff p q     -> rawAtoms p ++ rawAtoms q

-- | Get all the propositional variables in a formula, without duplicates
atoms :: Formula -> [PropVar]
atoms = Set.setify . rawAtoms

-- | Valuations simply evaluate any given propositional variable as
-- either 'True' or 'False'
type Valuation = PropVar -> Bool

-- | Given a 'Valuation', determine whether a 'Formula' evaluates to 'True'
-- or 'False'. 
eval :: Formula -> Valuation -> Bool
eval f v = case f of
  F           -> False
  T           -> True
  Atom x      -> v x
  Not p       -> not (eval p v)
  And p q     -> eval p v && eval q v
  Or p q      -> eval p v || eval q v
  Implies p q -> not (eval p v) || eval q v
  Iff p q     -> eval p v == eval q v

-- | This acts like a "hook", extending a function 'f' to '(p |-> y) f'
-- which will map 'p' to 'y', and any other propositional variable 'q' to
-- 'f q'.
(|->) :: PropVar -> a -> (PropVar -> a) -> PropVar -> a
(|->) p y f p' = if p' == p then y else f p'

-- | Recursively constructs all possible valuations on a given list of
-- atoms, then calls 'subfn' on each resulting valuation, "folds" them
-- together with '&&'. Used for checking validity and satisfiability.
onAllValuations :: (Valuation -> Bool) -> Valuation -> [PropVar] -> Bool
onAllValuations subfn v ats = case ats of
  []   -> subfn v
  p:ps -> onAllValuations subfn ((p |-> False) v) ps &&
          onAllValuations subfn ((p |-> True) v) ps

-- | Check if a given formula is a tautology or not
isTautology :: Formula -> Bool
isTautology fm = onAllValuations (eval fm) (const False) (atoms fm)

-- | Check if a given formula is unsatisfiable or not
isUnsatisfiable :: Formula -> Bool
isUnsatisfiable fm = isTautology $ Not fm

-- | Check if a given formula is satisfiable or not
isSatisfiable :: Formula -> Bool
isSatisfiable = not . isUnsatisfiable


{- utility functions -}
isLiteral :: Formula -> Bool
isLiteral (Atom _) = True
isLiteral (Not (Atom _)) = True
isLiteral _ = False

isNegative :: Formula -> Bool
isNegative (Not _) = True
isNegative _ = False

isPositive :: Formula -> Bool
isPositive = not . isNegative

-- | Take the dual of a formula. Assumes the formula is in negation
-- normal form. Throws an error if it enounters an 'Implies' or 'Iff'.
dual :: Formula -> Formula
dual fm = case fm of
  F       -> T
  T       -> F
  Atom _  -> fm
  Not p   -> Not (dual p)
  And p q -> Or (dual p) (dual q)
  Or p q  -> And (dual p) (dual q)
  _       -> error "dual called on formula involving 'Implies' or 'Iff'"

propSubstitute :: PropVar -> Formula -> Formula -> Formula
propSubstitute x y = mapAtoms (\a -> if a == x then y else Atom a)

{- simplification -}
simplifyProp' :: Formula -> Formula
simplifyProp' fm = case fm of
  Not F       -> T
  Not T       -> F
  Not (Not p) -> p
  And _ F     -> F
  And F _     -> F
  And p T     -> p
  And T q     -> q
  Or _ T      -> T
  Or T _      -> T
  Or F p      -> p
  Or p F      -> p
  Implies F _ -> T
  Implies _ T -> T
  Implies p F -> Not p
  Iff p T     -> p
  Iff T p     -> p
  Iff F F     -> T
  Iff p F     -> Not p
  Iff F p     -> Not p
  _           -> fm

-- | Simplifies various logical structures, avoids double negatives, etc.
-- Necessary as a first step to get a formula in NNF.
simplifyProp :: Formula -> Formula
simplifyProp fm = case fm of
  Not p       -> simplifyProp' (Not (simplifyProp p))
  And p q     -> simplifyProp' (And (simplifyProp p) (simplifyProp q))
  Or p q      -> simplifyProp' (Or (simplifyProp p) (simplifyProp q))
  Implies p q -> simplifyProp' (Implies (simplifyProp p) (simplifyProp q))
  Iff p q     -> simplifyProp' (Iff (simplifyProp p) (simplifyProp q))
  _           -> fm

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

toNNF :: Formula -> Formula
toNNF = toNNF' . simplifyProp

toNENF' :: Formula -> Formula
toNENF' fm = case fm of
  Not (Not p)       -> toNENF' p
  Not (And p q)     -> Or (toNENF' p) (toNENF' q)
  Not (Implies p q) -> And (toNENF' p) (toNENF' (Not q))
  Not (Iff p q)     -> Iff (toNENF' p) (toNENF' (Not q))
  And p q           -> And (toNENF' p) (toNENF' q)
  Or p q            -> Or (toNENF' p) (toNENF' q)
  Implies p q       -> Or (toNENF' (Not p)) (toNENF' q)
  Iff p q           -> Iff (toNENF' p) (toNENF' q)
  _                 -> fm

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

-- | Get all valuations which satisfy some property 'prop'
allValuationsSatisfying :: (Valuation -> Bool) -> Valuation -> [PropVar] -> [Valuation]
allValuationsSatisfying p v [] = [v | p v]
allValuationsSatisfying p v (a:pvs) =
  allValuationsSatisfying p ((a |-> False) v) pvs
  ++ allValuationsSatisfying p ((a |-> True) v) pvs

-- | Given a list of propositional variables and a fixed valuation 'v', map
-- the propositional variables through 'if eval (Atom _) v then (toAtom
-- _) else (Not (toAtom _))', the 'foldlConj' the resulting formulas all
-- together 
makeLiterals :: [PropVar] -> Valuation -> Formula
makeLiterals ats v = foldlConj (map ((\p -> if eval p v then p else Not p)
                                     . Atom)
                                ats)

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

-- | Converts an NNF to a DNF by iteratively applying 'distrib'.
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

negate :: Formula -> Formula
negate (Not fm) = fm
negate fm = Not fm

isDnfClauseTrivial :: [Formula] -> Bool
isDnfClauseTrivial literals =
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
simpDNF fm = (subsume . filter (not . isDnfClauseTrivial) . pureDNF . toNNF) fm

-- | Determines the DNF using sets, then collects the clauses by
-- iteratively joining them 'Or'-d together.
toDNF :: Formula -> Formula
toDNF fm = foldrDisj (map foldlConj (simpDNF fm))

pureCNF :: Formula -> [[Formula]]
pureCNF = map (map negate) . pureDNF . toNNF . negate

simpCNF :: Formula -> [[Formula]]
simpCNF F = []
simpCNF T = [[]]
simpCNF fm = let cjs = filter (not . isDnfClauseTrivial) (pureCNF $ toNNF fm)
             in filter (\c -> not $ any (`Set.isProperSubset` c) cjs) cjs

toCNF :: Formula -> Formula
toCNF fm = foldlConj (map foldrDisj (simpCNF fm))
