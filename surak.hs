{-
 (c) 2015 by Alex Nelson

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
-}
import qualified Data.List as Data.List

type PropVar = String

data Formula = F
             | T
             | Atom PropVar
             | Not Formula
             | And Formula Formula
             | Or Formula Formula
             | Implies Formula Formula
             | Iff Formula Formula
               deriving (Show, Eq)

-- instance Show Formula where
  
{- valuation related code -}
rawAtoms :: Formula -> [PropVar]
rawAtoms f = case f of
  F           -> []
  T           -> []
  Atom x      -> [x]
  Not p       -> rawAtoms p
  And p q     -> (rawAtoms p) ++ (rawAtoms q)
  Or p q      -> (rawAtoms p) ++ (rawAtoms q)
  Implies p q -> (rawAtoms p) ++ (rawAtoms q)
  Iff p q     -> (rawAtoms p) ++ (rawAtoms q)

atoms :: Formula -> [PropVar]
atoms = Data.List.nub . rawAtoms

type Valuation = PropVar -> Bool

{- evaluator -}
eval :: Formula -> Valuation -> Bool
eval f v = case f of
  F           -> False
  T           -> True
  Atom x      -> v x
  Not p       -> not (eval p v)
  And p q     -> (eval p v) && (eval q v)
  Or p q      -> (eval p v) || (eval q v)
  Implies p q -> not (eval p v) || (eval q v)
  Iff p q     -> (eval p v) == (eval q v)

{- helper functions -}
--- used to determine tautologies, etc.
onAllValuations :: (Valuation -> Bool) -> Valuation -> [PropVar] -> Bool
onAllValuations subfn v ats = case ats of
  []   -> subfn v
  p:ps -> let v' t q = if q == p then t else v q in
          (onAllValuations subfn (v' False) ps)
          && (onAllValuations subfn (v' True) ps)

isTautology :: Formula -> Bool
isTautology fm = onAllValuations (eval fm) (Const False) (atoms fm)

isUnsatisfiable :: Formula -> Bool
isUnsatisfiable fm = isTautology (Not fm)

isSatisfiable :: Formula -> Bool
isSatisfiable fm = not (isUnsatisfiable fm)

main = let a = Atom "A"
           notA = Not a
       in putStrLn ("isTautology (Or A (Not A)) = " ++ (show (isTautology
                                                              (Or a notA))))
