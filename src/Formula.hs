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
module Formula (PropVar,
                Formula(F,T,Atom,Not,And,Or,Implies,Iff),
                Valuation,
                atoms,
                eval,
                onAllValuations,
                isTautology,
                isSatisfiable,
                isUnsatisfiable,
                isNegative,
                isPositive,
                dual,
                propSimplify,
                propSubstitute) where
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
               deriving (Eq)

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
mapAtoms f F             = F
mapAtoms f T             = T
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
atoms = Data.List.nub . rawAtoms

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
  Implies p q -> not $ eval p v || eval q v
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
isNegative :: Formula -> Bool
isNegative (Not fm) = True
isNegative _ = False

isPositive :: Formula -> Bool
isPositive = not . isNegative

-- | Take the dual of a formula. Assumes the formula is in negation
-- normal form. Throws an error if it enounters an 'Implies' or 'Iff'.
dual :: Formula -> Formula
dual fm = case fm of
  F       -> T
  T       -> F
  Atom x  -> fm
  Not p   -> Not (dual p)
  And p q -> Or (dual p) (dual q)
  Or p q  -> And (dual p) (dual q)
  _       -> error "dual called on formula involving 'Implies' or 'Iff'"

(|=>) :: PropVar -> Formula -> PropVar -> Formula
(|=>) x f y = if x==y then f else undefined

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
