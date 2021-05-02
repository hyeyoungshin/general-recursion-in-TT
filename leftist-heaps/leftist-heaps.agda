module leftist-heaps where

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Data.List
open import Data.Nat hiding (compare)
open import Data.Product
open import Function
open import Induction.Nat
open import Induction.WellFounded

data LTree : Set
rank : LTree → ℕ

data LTree where
 ltnil : LTree
 ltnode : (left right : LTree) → (rank right ≤  rank left) → LTree

rank ltnil = 0
rank (ltnode left right h) = (rank right) + 1

empty : LTree
empty = ltnil

test-tree : LTree
test-tree = ltnode empty empty γ
 where
 γ : rank empty ≤ rank empty
 γ = z≤n

test1-tree : LTree
test1-tree = (ltnode test-tree test-tree) γ
  where
  γ : rank test-tree ≤ rank test-tree
  γ = s≤s z≤n

test2-tree : LTree
test2-tree = ltnode test1-tree test-tree (s≤s z≤n)

