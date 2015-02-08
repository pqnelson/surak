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
                isUnsatisfiable) where
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


