-- G54AAD Advanced Algorithms and Data Structures
-- Heap Class, Binary Heaps
--  Venanzio Capretta, Fall 2019

module Heaps where

-- Priority Queues or Heaps

class Heap h where
  emptyH :: h a
  isEmptyH :: h a -> Bool
  insertH :: Ord a => a -> h a -> h a
  minimumH :: Ord a => h a -> a
  extractH :: Ord a => h a -> (a,h a)

  -- Default implementation of union
  -- Specific instances will have a more efficient implementation
  unionH :: Ord a => h a -> h a -> h a
  unionH h1 h2 | isEmptyH h1 = h2
               | otherwise = let (x,h1') = extractH h1
                             in unionH h1' (insertH x h2)

  -- default implementations of conversion with lists
  -- specific instances may have their own efficient version

  listHeap :: Ord a => [a] -> h a
  listHeap = foldr insertH emptyH

  heapList :: Ord a => h a -> [a]
  heapList h = if isEmptyH h then []
                 else let (x,h') = extractH h
                      in x:heapList h'


-- we can use listHeap and heapList to implement a sorting algorithm
--    sort :: Ord a => [a] -> [a]
--    sort heapList . listHeap
-- This has to be defined specifically for every instance
--  Because the data constructor doesn't appear in the type

deleteH :: (Heap h, Ord a) => h a -> h a
deleteH = snd . extractH

-----------------------------------------------------------------------------

-- Implementation as SORTED LISTS

instance Heap [] where
  emptyH = []
  isEmptyH = null
  insertH x h = let (h1,h2) = span (<= x) h in h1++x:h2
  minimumH = head
  extractH h = (head h, tail h)
  heapList h = h
  unionH [] h2 = h2
  unionH h1 [] = h1
  unionH (x:xs) (y:ys) = if x<=y then x : unionH xs (y:ys)
                                 else y : unionH (x:xs) ys

-- Heap Sort
-- Since the heap instance is not present in the type of the sort function
--  we have to do a type cast.
-- We must redefine the sorting function for every heap instance

sortHL :: Ord a => [a] -> [a]
sortHL = heapList . (listHeap :: Ord a => [a] -> [a])

----------------------------------------------------------------------------

-- Implementation as BINARY HEAPS
--   1. Complete Binary Trees
--   2. The root is smaller or equal to the children
-- We use a Boolean value to keep track of balance
--  True = balanced, False = unbalanced to the left

data BinHeap a = EmptyBH | NodeBH Bool a (BinHeap a) (BinHeap a)
  deriving (Show,Eq)

keyBH :: BinHeap a -> a
keyBH (NodeBH _ x _ _) = x

leftBH :: BinHeap a -> BinHeap a
leftBH (NodeBH _ _ h1 _) = h1

rightBH :: BinHeap a -> BinHeap a
rightBH (NodeBH _ _ _ h2) = h2

sizeBH :: BinHeap a -> Int
sizeBH EmptyBH = 0
sizeBH (NodeBH _ _ h1 h2) = sizeBH h1 + sizeBH h2 + 1

balancedBH :: BinHeap a -> Bool
balancedBH EmptyBH = True
balancedBH (NodeBH b _ h1 h2) =
  balancedBH h1 && balancedBH h2 &&
  if b then sizeBH h1 == sizeBH h2
       else sizeBH h1 == sizeBH h2 + 1

-- moving the last leaft up to the right place
siftUp :: Ord a => a -> BinHeap a -> (a, BinHeap a)
siftUp x h@(NodeBH b y h1 h2) =
  if x > y then if b then let (z,h1') = siftUp x h1
                          in (y, NodeBH b z h1' h2)
                     else let (z,h2') = siftUp x h2
                          in (y, NodeBH b z h1 h2')
           else (x,h)
siftUp x h = (x,h)

-- Tree with the minimun root
minRoot :: Ord a => BinHeap a -> BinHeap a -> Bool
minRoot (NodeBH _ x _ _) (NodeBH _ y _ _) = x<=y
minRoot _ EmptyBH = True
minRoot _ _ = False

-- moving the root down to the right place
siftDown :: Ord a => a -> BinHeap a -> (a, BinHeap a)
siftDown x h@(NodeBH b y h1 h2) =
  if x>y then (y, downHeap (NodeBH b x h1 h2))
         else (x, h)
siftDown x h = (x,h)

-- swapping the root down to the right place
downHeap :: Ord a => BinHeap a -> BinHeap a
downHeap (NodeBH b x h1 h2) =
  if minRoot h1 h2
  then let (x',h1') = siftDown x h1
       in (NodeBH b x' h1' h2)
  else let (x',h2') = siftDown x h2
       in (NodeBH b x' h1 h2')
downHeap h = h

-- Extracting a leaf (without spoiling balance)
extractLeafBH :: BinHeap a -> (a, BinHeap a)
extractLeafBH (NodeBH _ x EmptyBH EmptyBH) = (x, EmptyBH)
extractLeafBH (NodeBH True x h1 h2) =
  let (y,h2') = extractLeafBH h2
  in (y, NodeBH False x h1 h2')
extractLeafBH (NodeBH False x h1 h2) =
  let (y,h1') = extractLeafBH h1
  in (y, NodeBH True x h1' h2)

replaceRoot :: a -> BinHeap a -> (a,BinHeap a)
replaceRoot x (NodeBH b y h1 h2) = (y,NodeBH b x h1 h2)
replaceRoot x EmptyBH = undefined

instance Heap BinHeap where
  emptyH = EmptyBH
  
  isEmptyH EmptyBH = True
  isEmptyH _ = False

  insertH x EmptyBH = NodeBH True x EmptyBH EmptyBH
  insertH x (NodeBH True y h1 h2) =
    NodeBH False (min x y) (insertH (max x y) h1) h2
  insertH x (NodeBH False y h1 h2) =
    NodeBH True (min x y) h1 (insertH (max x y) h2)

{- Alternative: insert as a leaf and sift up:

  insertH x EmptyBH = NodeBH True x EmptyBH EmptyBH
  insertH x (NodeBH True y h1 h2) =
    let (z,h1') = siftUp y (insertH x h1)
    in NodeBH False z h1' h2
  insertH x (NodeBH False y h1 h2) =
    let (z,h2') = siftUp y (insertH x h2)
    in NodeBH True z h1 h2'
-}

  minimumH (NodeBH _ x _ _) = x

  extractH EmptyBH = undefined
  extractH (NodeBH _ x EmptyBH EmptyBH) = (x,EmptyBH)
  extractH (NodeBH True x h1 h2) =
    let (y,h2') = extractH h2
        (z,h1') = siftDown y h1
    in (x, NodeBH False z h1' h2')
  extractH (NodeBH False x h1 h2) =
    let (y,h1') = extractH h1
        (z,h2') = siftDown y h2
    in (x, NodeBH True z h1' h2')
  
{- Alternative: put the last element in the root and sift down:

  extractH EmptyBH = undefined
  extractH (NodeBH _ x EmptyBH EmptyBH) = (x,EmptyBH)
  extractH h =
    let (y,h') = extractLeafBH h
        (x,h'') = replaceRoot y h'
    in (x, downHeap h'')
-}

-- Heap Sort

sortBH :: Ord a => [a] -> [a]
sortBH = heapList . (listHeap :: Ord a => [a] -> BinHeap a)


