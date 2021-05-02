-- mergesort implementation by Vitus (https://stackoverflow.com/questions/22265402/merge-sort-in-agda)


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

first_half : (List A → (List A × List A)) → List A → List A
first_half f l = fst (f l)

second_half : (List A → List A × List A) → List A → List A
second_half f l = snd (f l)


data merge_Dom : List A → Set where
 mD_nil : merge_Dom []
 mD_single : (x : A) → merge_Dom (x ∷ [])
 mD_split : (l : List A) → merge_Dom (first_half split l) → merge_Dom (second_half split l) → merge_Dom l

mergeD_sort : (l : List A) → (merge_Dom l) → List A
mergeD .[] sort mD_nil = []
mergeD .(x ∷ []) sort mD x single = x ∷ []
mergeD l sort (mD .l split md md₁) = {!merge (mergeD_sort (first_half l) md) (mergeD_sort (second_half l) md₁)!}

