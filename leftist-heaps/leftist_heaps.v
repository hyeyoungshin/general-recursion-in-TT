(* Formalization of Leftist Heaps (Okasaki Ch.3) *)

Require Export Nat.
Require Export Arith.
Require Export PeanoNat.

(* The rank of a tree is the length of its rightmost path.
   In a leftist tree the rank of the left child must be
   larger or equal to the rank of the right child.

   This can be done with simultaneous induction-recursion
   by defining the type of leftist trees simultaneously
   with the rank function.
  
   We also simultaneously check the heap property.

   data LTree: Set
      ltnil: LTree
      ltnode: (x:nat)(left right: LTree), 
                rank left >= rank right -> 
                x <~ root left -> x <~ root right -> LTree
   with rank: LTree -> nat
        rank ltnil = 0
        rank (ltnode left right h) = (rank right) + 1
   with root: LTree -> option nat
        root ltnil = None
        root (ltnode x _ _ _ _ _) = Some x

   (<~): nat -> option nat -> Prop   defined separately

   We don't have induction-recursion in Coq,
   so we use Conor McBride's indexing trick.
*)

Definition Rank := nat.
Definition Data := nat.

(* Leftist Heaps indexed both on rank and root element
      Empty heap not allowed for now *)

Inductive Leftist: Rank -> Data -> Set :=
  lsingle : forall (x:Data), Leftist 1 x
| lnode : forall (x:Data)
                 (lrank: Rank)(y:Data)(ltree: Leftist lrank y)
                 (rrank: Rank)(z:Data)(rtree: Leftist rrank z),
          lrank >= rrank -> x <= y -> x <= z -> Leftist (S rrank) x.

Definition ge_ge_dec: forall x y: nat, {x >= y} + {y >= x}.
intros x y; case (le_ge_dec x y).
intro hxy; right.
auto.
auto.
Defined.

Lemma ge_max_l: forall x y: nat, x >= y -> max x y = x.
intros x y hxy.
apply max_l.
auto.
Qed.

Lemma ge_min_r: forall x y: nat, x >= y -> min x y = y.
intros x y hxy.
apply min_r.
auto.
Qed.

Lemma ge_max_r: forall x y: nat, y >= x -> max x y = y.
intros x y hyx.
apply max_r.
auto.
Qed.

Lemma ge_min_l: forall x y: nat, y >= x -> min x y = x.
intros x y hyx.
apply min_l.
auto.
Qed.


(* The same as lnode, but we check the ranks on the fly *)
Definition lmake:
  forall (x:Data)
         (lrank: Rank)(y:Data)(ltree: Leftist lrank y)
         (rrank: Rank)(z:Data)(rtree: Leftist rrank z),
         x <= y -> x <= z -> Leftist (S (min lrank rrank)) x.
intros x lrank y ltree rrank z rtree hxy hxz.
case (ge_ge_dec lrank rrank).

intro hrank; rewrite ge_min_r.
exact (lnode x lrank y ltree rrank z rtree hrank hxy hxz).
exact hrank.

intro hrank; rewrite ge_min_l.
exact (lnode x rrank z rtree lrank y ltree hrank hxz hxy).
exact hrank.
Defined.

(* We put all heaps in a single type *)

Record LTree: Set := ltree
  { ltr_rank: Rank;
    ltr_root: Data;
    ltr_tree: Leftist ltr_rank ltr_root
  }.


Definition lt_single (x: Data): LTree := ltree 1 x (lsingle x).

Definition lt_node (left right: LTree): 
  forall (x:Data), 
    ltr_rank left >= ltr_rank right -> 
    x <= ltr_root left -> x <= ltr_root right -> LTree :=
  fun x h pl pr => ltree (S (ltr_rank right)) x
                     (lnode x (ltr_rank left)  (ltr_root left)  (ltr_tree left)
                              (ltr_rank right) (ltr_root right) (ltr_tree right)
                            h pl pr).









(* We add the empty heap to the structure *) 


Definition LHeap: Set := option LTree.

Definition lh_rank (t:LHeap): Rank :=
  match t with
    None => 0
  | Some t => ltr_rank t
  end.

(* The derived constructors. *)

Definition lh_empty: LHeap := None.
