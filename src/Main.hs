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
pierceLawTest :: Formula
pierceLawTest = let p = Atom "p8"
                    q = Atom "q8"
                in Implies (Implies (Implies p q) p) p

pelletierTestNine :: Formula
pelletierTestNine = let p = Atom "p9"
                        q = Atom "q9"
                    in (Implies (And (Or p q)
                                     (And (Or (Not p) q)
                                          (Or p (Not q))))
                                (Not (Or (Not p)
                                         (Not q))))

--- Modified version of Problem 10
pelletierTestTen :: Formula
pelletierTestTen = let p = Atom "p10"
                       q = Atom "q10"
                       r = Atom "r10"
                   in (Implies (And (Implies q r)
                                    (And (Implies r (And p q))
                                         (Implies p (Or q r))))
                               (Iff p q))

pelletierTest' :: [Formula]
pelletierTest' = [(Iff (Implies (Atom "p1") (Atom "q1"))
                       (Implies (Not (Atom "q1")) (Not (Atom "p1")))),
                  (Iff (Not (Not (Atom "p2")))
                       (Atom "p2")),
                  (Implies (Not (Implies (Atom "p3") (Atom "q3")))
                           (Implies (Atom "q3") (Atom "p3"))),
                  (Iff (Implies (Not (Atom "p4")) (Atom "q4"))
                       (Implies (Not (Atom "q4")) (Atom "p4"))),
                  (Implies (Implies (Or p q) (Or p r))
                           (Or p (Implies q r))),
                  (Or (Atom "p6")
                      (Not (Atom "p6"))),
                  (Or (Atom "p7") (Not $ Not $ Not (Atom "p7"))),
                  pierceLawTest,
                  pelletierTestNine,
                  pelletierTestTen,
                  (Iff (Atom "p11") (Atom "p11")), --- Problem 11
                  (Iff (Iff (Iff (Atom "p12") (Atom "q12"))
                            (Atom "r12"))
                       (Iff (Atom "p12")
                            (Iff (Atom "q12") (Atom "r12")))),
                  (Iff (Or (Atom "p13")
                           (And (Atom "q13")
                                (Atom "r13")))
                       (And (Or (Atom "p13")
                                (Atom "q13"))
                            (Or (Atom "p13")
                                (Atom "r13")))),
                  (Iff (Iff (Atom "p14") (Atom "q14"))
                       (And (Or (Atom "q14")
                                (Not (Atom "p14")))
                            (Or (Not (Atom "q14"))
                                (Atom "p14")))),
                  (Iff (Implies (Atom "p15") (Atom "q15"))
                       (Or (Not (Atom "p15")) (Atom "q15"))), --- problem 15
                  (Or (Implies (Atom "p16") (Atom "q16"))
                      (Implies (Atom "q16") (Atom "p16"))),
                  (Iff (Implies (And (Atom "p17")
                                     (Implies (Atom "q17")
                                              (Atom "r17")))
                                (Atom "s17"))
                       (And (Or (Not (Atom "p17"))
                                (Or (Atom "q17")
                                    (Atom "s17")))
                            (Or (Not (Atom "p17"))
                                (Or (Not (Atom "r17"))
                                    (Atom "s17")))))]
                where p = Atom "p"
                      q = Atom "q"
                      r = Atom "r"

-- | The Pelletier test, plus a stress test checking the the first 5
-- are all logically equivalent to 'Formula.T'. You can really feel how
-- slow the naive CNF and DNF algorithms are on this stress test, even
-- on a modern computer with 8 processors and 12 Gigs of RAM.
pelletierTest :: [Formula]
pelletierTest = pelletierTest' ++ [foldr Iff T (take 5 pelletierTest')]

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

