{-|
Module      : Set
Description : Using Lists for Sets
Copyright   : (c) Alex Nelson, 2015
License     : MIT
Maintainer  : pqnelson@gmail.com
Stability   : experimental
Portability : POSIX

This is all just helper functions, treating lists as sets of distinct
elements. Sets are ordered for efficiency.
-}
module Set
       (
         setify
       , insert
       , union
       , unions
       , intersect
       , isSubset
       , isProperSubset
       , powerSet
       , difference
       , (\\)
       , remove
       , image
       ) where
import qualified Data.List as List
import qualified Data.Set as Set

-- | Create a sorted list with unique elements, it should be O(N log N).
setify :: Ord a => [a] -> [a]
setify = Set.toList . Set.fromList

union' :: Ord a => [a] -> [a] -> [a]
union' [] s2 = s2
union' s1 [] = s1
union' s1@(h1:t1) s2@(h2:t2) = case compare h1 h2 of
                                EQ -> h1 : union' t1 t2
                                LT -> h1 : union' t1 s2
                                GT -> h2 : union' s1 t2

-- | The union of two sets.
union :: Ord a => [a] -> [a] -> [a]
union l1 l2 = union' (setify l1) (setify l2)

-- | The union of an arbitrary number of lists
unions :: Ord a => [[a]] -> [a]
unions = setify . List.concat

intersect' :: Ord a => [a] -> [a] -> [a]
intersect' [] _ = []
intersect' _ [] = []
intersect' l1@(h1:t1) l2@(h2:t2) = case compare h1 h2 of
                                    EQ -> h1 : intersect' t1 t2
                                    LT -> intersect' t1 l2
                                    GT -> intersect' l1 t2

-- | The intersection of two sets
intersect :: Ord a => [a] -> [a] -> [a]
intersect l1 l2 = intersect' (setify l1) (setify l2)

-- | Inserting an element into a set
insert :: Ord a => a -> [a] -> [a]
insert x = union [x]

-- | Checks if first argument is a subset (proper or not) of the second argument
isSubset :: Ord a => [a] -> [a] -> Bool
isSubset [] _ = True
isSubset _ [] = False
isSubset l1@(h1:t1) (h2:t2) | h1 == h2 = isSubset t1 t2
                            | h1 < h2 = False
                            | otherwise = isSubset l1 t2

-- | Checks if the first argument is a proper subset of the second
isProperSubset :: Ord a => [a] -> [a] -> Bool
isProperSubset _ [] = False
isProperSubset [] _ = True
isProperSubset s1 s2 = (s1 /= s2) && isSubset s1 s2

-- | Returns the set of all subsets of the argument
powerSet :: [a] -> [[a]]
powerSet [] = [[]]
powerSet (a:t) = let acc = powerSet t
                 in map (a:) acc ++ acc

-- | The set difference of the first list minus the second list.
difference :: Ord a => [a] -> [a] -> [a]
difference [] _ = []
difference s1 [] = s1
difference s1@(h1:t1) s2@(h2:t2) = case compare h1 h2 of
                                    EQ -> difference t1 t2
                                    LT -> h1 : difference t1 s2
                                    GT -> difference s1 t2

-- | The 'difference' function as an infix operator. (Syntactic Sugar) 
(\\) :: Ord a => [a] -> [a] -> [a]
s1 \\ s2 = difference (setify s1) (setify s2)

-- | Removes a single element from a set
remove :: Ord a => [a] -> a -> [a]
remove s1 elt = s1 \\ [elt]

-- | Setify the results of a map
image :: Ord b => (a -> b) -> [a] -> [b]
image f = setify . map f
