module defCNF
       where

import qualified Data.Map as Map

makeProp :: Int -> (Formula, Int)
makeProp n = (Atom ("p_" ++ (show n)), n+1)

-- | A triple tracking the formula to be transformed,
-- definitions made so far (as a dictionary, well 'Data.Map'),
-- and the current variable index counter.
type Trip = (Formula, Map Formula (Formula, Formula), Int)


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

-- | Helper function
maybeRead :: Read a => String -> Maybe a
maybeRead = fmap fst . listToMaybe . reads

maxVarIndex :: String -> String -> Int -> Int
maxVarIndex pfx s n =
  let m = length pfx
      l = length s
  in if l <= m || take m s /= pfx
     then n
     else let s' = take (l-m) (drop m s)
          in case MaybeRead s'
             of Nothing -> n
                Just n' -> max n n'
