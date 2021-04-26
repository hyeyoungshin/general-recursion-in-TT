----------------------------------------------------------
-- to make mergesort generic

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module mergesort
  {l a} {A : Set a}
  {_<_ : Rel A l}
  (strictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open IsStrictTotalOrder strictTotalOrder
----------------------------------------------------------

module mergesort where

open import Agda.Builtin.Nat
open import Data.List
open import Data.Nat hiding (compare)
open import Data.Product
open import Function
open import Induction.Nat
open import Induction.WellFounded


-- data Compare : Nat -> Nat -> Set where
--   LT : {m : Nat} {n : Nat} -> Compare m (suc (m + n))
--   EQ : {m : Nat} -> Compare m m
--   GT : {m : Nat} {n : Nat} -> Compare (suc (m + n)) m


-- data Tri (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where
--   tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
--   tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
--   tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C


merge : (xs : List A) → (ys : List A) → List A
merge [] ys = ys
merge (x ∷ xs) [] = x ∷ xs
merge (x ∷ xs) (y ∷ ys) with compare x y
...                        | tri< _ _ _  = x ∷ merge xs (y ∷ ys)
...                        | tri≈ _ _ _ = x ∷ merge xs (y ∷ ys)
...                        | tri> _ _ _ = y ∷ merge (x ∷ xs) ys


split : List A → List A × List A
split [] = [] , []
split (x ∷ xs) with split xs
...               | l , r = x ∷ r , l


_<ₗ_ : Rel (List ℕ) _
_<ₗ_ = Data.Nat._<_ on length

-- mergesort : (List ℕ -> List ℕ)
-- mergesort [] = []
-- mergesort (x ∷ xs) = merge(left, right)
--  where
--  left : List ℕ
--  left = []
--  right : List ℕ
--  right = []

--   f : ℕ → List ℕ → List ℕ → List ℕ
--   f x left right = if(x < length(x::xs)) {x::left} else {x::right}

--   left = mergesort(f(x))
--   right = mergesort(f(x))

--   merge : List ℕ → List ℕ → List ℕ
--   merge = ?
