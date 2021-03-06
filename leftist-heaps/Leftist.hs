-- G54AAD Advanced Algorithms and Data Structures
-- Leftist Heaps
--  Venanzio Capretta, Fall 2019

module Leftist where

import Heaps

{-
A leftist heap is a binary tree such that
 1) Heap property:
      every node element is smaller or equal to the elements in its children
 2) Leftist property:
      the rank of the left child is larger or equal to
         the rank of the right child, and
      both children are themselves leftist heaps.
The rank of a tree is the length of its rightmost branch,
  also called its right spine.
-}

data LeftistHeap a = E | T Int a (LeftistHeap a) (LeftistHeap a)
  deriving (Show,Eq)

{-
The constructor E denotes the empty heap.
A tree of the form (T r x t1 t2) represent a leftist heap with
  rank r, minimum element x, left child t1 and right child t2.
-}

rank :: LeftistHeap a -> Int
rank E = 0
rank (T r _ _ _) = r

-- Computed rank
compRank :: LeftistHeap a -> Int
compRank E = 0
compRank (T _ _ _ right) = compRank right + 1

-- Checking that the ranks is correct
rankOK :: LeftistHeap a -> Bool
rankOK E = True
rankOK (T r _ _ right) = r == rank right + 1 && rankOK right

{- Checking the leftist rank property -}
rankProp :: LeftistHeap a -> Bool
rankProp E = True
rankProp (T _ _ left right) =
  rank left >= rank right && rankProp left && rankProp right


-- Extracting the root (if not empty)
root :: LeftistHeap a -> Maybe a
root E = Nothing
root (T _ x _ _) = Just x

-- Comparing with a Maybe value
infix 5 <~

(<~) :: Ord a => a -> Maybe a -> Bool
x <~ Nothing = True
x <~ (Just y) = x <= y

{-
Checking the heap property:
Every node must be smaller or equal to its descendants
-}

heapOrd :: Ord a => LeftistHeap a -> Bool
heapOrd E = True
heapOrd (T _ x left right) =
  x <~ root left  && heapOrd left  &&
  x <~ root right && heapOrd right

-- Check if it is a correct Leftist Heap
lhCheck :: Ord a => LeftistHeap a -> Bool
lhCheck t = rankOK t && rankProp t && heapOrd t


{-
Suppose we have two heaps a and b and a value x.
If we know that x is smaller than all the values contained in a and b,
  then we can easily make a new heap with x at the root:
  the left child is the one between a and b with the larger rank,
  the right child is the other.
-}

makeT :: a -> LeftistHeap a -> LeftistHeap a -> LeftistHeap a
makeT x a b = if rank a >= rank b
                 then T (rank b + 1) x a b
                 else T (rank a + 1) x b a

instance Heap LeftistHeap where
  emptyH = E

  isEmptyH E = True
  isEmptyH _ = False

  insertH x = unionH (T 1 x E E)

  minimumH E = error "empty heap"
  minimumH (T _ x _ _) = x
  
  extractH E = error "empty heap"
  extractH (T _ x t1 t2) = (x, unionH t1 t2)

  unionH h E = h
  unionH E h = h
  unionH h1@(T _ x a1 b1) h2@(T _ y a2 b2)
    = if x<=y then makeT x a1 (unionH b1 h2)
              else makeT y a2 (unionH h1 b2)

-- Sorting with Leftist Heaps

sortLH :: Ord a => [a] -> [a]
sortLH = heapList . (listHeap :: Ord a => [a] -> LeftistHeap a)
