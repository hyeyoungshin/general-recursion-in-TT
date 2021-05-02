-- mergesort implementation as described by Bove and Capretta

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module mergesort-bv
  {l a} {A : Set a}
  {_<_ : Rel A l}
  (strictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open IsStrictTotalOrder strictTotalOrder

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Data.List
open import Data.Nat hiding (compare)
open import Data.Product
open import Function
open import Induction.Nat
open import Induction.WellFounded

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
...               | first , second = x ∷ second , first

first-half : (List A → (List A × List A)) → List A → List A
first-half f l = fst (f l)

second-half : (List A → List A × List A) → List A → List A
second-half f l = snd (f l)


data merge-Dom : List A → Set where
 mD-nil : merge-Dom []
 mD-single : (x : A) → merge-Dom (x ∷ [])
 mD-split : (l : List A) → merge-Dom (first-half split l) → merge-Dom (second-half split l) → merge-Dom l

mergeD-sort : (l : List A) → (merge-Dom l) → List A
mergeD-sort .[] mD-nil = []
mergeD-sort .(x ∷ []) (mD-single x) = x ∷ []
mergeD-sort l (mD-split .l md₁ md₂) = merge (mergeD-sort (first-half split l) md₁) (mergeD-sort (second-half split l) md₂)

