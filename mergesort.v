Module Merge_Sort.

Section Merge_Sort. 

Variable A: Set.

Variable split_list : list A -> (list A) * (list A).

Definition first_half : list A -> list A := fun l => fst (split_list l).

Definition second_half : list A -> list A := fun l => snd (split_list l).

Inductive merge_Dom: list A -> Set :=
  mD_nil: merge_Dom nil
| mD_single: forall x:A, merge_Dom (cons x nil)
| mD_split: forall l, merge_Dom (first_half l) -> merge_Dom (second_half l) 
                      -> merge_Dom l.

Variable merge: list A -> list A -> list A.

Fixpoint mergeD_sort (l:list A)(h: merge_Dom l): list A :=
match h with
  mD_nil => nil
| mD_single x => cons x nil
| mD_split l h1 h2 => merge (mergeD_sort (first_half l) h1)
                            (mergeD_sort (second_half l) h2)
end.

End Merge_Sort.

Definition l : list nat := cons 3 nil.

Lemma lD: merge_Dom  l.


