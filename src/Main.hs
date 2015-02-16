{-|
Module      : Main
Copyright   : (c) Alex Nelson, 2015
License     : MIT
Maintainer  : pqnelson@gmail.com
Stability   : experimental
Portability : POSIX

This just runs 16 tests from the literature.
-}
module Main where
import Formula
import NormalForm
import qualified DavisPutnam as DP

testToStr :: Formula -> String
testToStr fm = let result = DP.isTautology fm
               in if not result
                  then show fm ++ " is " ++ show result ++ "\n"
                  else "...True\n"

-- | A number of tests taken from Francis Pelletier's "Seventy-Five
-- Problems for Testing Automatic Theorem Provers"
-- /Journal of Automated Reasoning/ __2__ (1986) 191-216
pelletierTest :: [Formula]
pelletierTest = [(Iff (Implies p q) (Implies (Not q) (Not p))),
                 (Iff (Not (Not p)) p),
                 (Implies (Not (Implies p q)) (Implies q p)),
                 (Iff (Implies (Not p) q) (Implies (Not q) p)),
                 (Implies (Implies (Or p q) (Or p r)) (Or p (Implies q r))),
                 (Or p (Not p)),
                 (Or p (Not $ Not $ Not p)),
                 (Implies (Implies (Implies p q) p) p), --- Pierce's Law
                 (Implies (And (Or p q)
                               (And (Or (Not p) q)
                                    (Or p (Not q))))
                          (Not (Or (Not p) (Not q)))), --- Problem 9
                 (Implies (And (Implies q r)
                               (And (Implies r (And p q))
                                    (Implies p (Or q r))))
                          (Iff p q)), --- Modified version of Problem 10
                 (Iff p p), --- Problem 11
                 (Iff (Iff (Iff p q) r) (Iff p (Iff q r))),
                 (Iff (Or p (And q r))
                      (And (Or p q) (Or p r))),
                 (Iff (Iff p q)
                      (And (Or q (Not p))
                           (Or (Not q) p))),
                 (Iff (Implies p q) (Or (Not p) q)), --- problem 15
                 (Or (Implies p q) (Implies q p)),
                 (Iff (Implies (And p (Implies q r)) s)
                      (And (Or (Not p) (Or q s))
                           (Or (Not p) (Or (Not r) s))))]
                where p = Atom "p"
                      q = Atom "q"
                      r = Atom "r"
                      s = Atom "s"

tautologyTests :: () -> String
tautologyTests _ =
  foldr (++) ""
  $ map testToStr pelletierTest

toNnfTests :: () -> String
toNnfTests _ =
  foldr (++) ""
  $ map (\fm -> (testToStr (Iff fm (toNNF fm)))) pelletierTest

toCnfTests :: () -> String
toCnfTests _ =
  foldr (++) ""
  $ map (\fm -> (testToStr (Iff fm (toCNF fm)))) pelletierTest

textbookDefCNFTest :: () -> String
textbookDefCNFTest _ =
  testToStr (Iff (And (Or p (And q (Not r))) s)
                 (And (Iff p1 (And q (Not r)))
                      (And (Iff p2 (Or p p1))
                           (And (Iff p3 (And p2 s))
                                p3))))
  where p = Atom "p"
        q = Atom "q"
        r = Atom "r"
        s = Atom "s"
        p1 = Atom "p1"
        p2 = Atom "p2"
        p3 = Atom "p3"
             
main :: IO ()
main = putStrLn ("Tautology tests...\n"
                 ++ (tautologyTests ())
                 ++ "\nConverting to CNF tests...\n"
                 ++ (toCnfTests ())
                 ++ "\nConverting to NNF tests...\n"
                 ++ (toNnfTests ()))

