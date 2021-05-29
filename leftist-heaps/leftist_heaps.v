(* Formalization of Leftist Heaps (Okasaki Ch.3) *)

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
  lnil : forall (x:Data), Leftist 1 x
| lnode : forall (x:Data)
                 (lrank: Rank)(y:Data)(ltree: Leftist lrank y)
                 (rrank: Rank)(z:Data)(rtree: Leftist rrank z),
          lrank >= rrank -> x <= y -> x <= z -> Leftist (S rrank) x.

(* We put all heaps in a single type *)

Record LTreeRec: Set := ltree
  { ltr_rank: Rank;
    ltr_root: Data;
    ltr_tree: Leftist ltr_rank ltr_root
  }.

Definition LTree: Set := option LTreeRec.

Definition lt_rank (t:LTree): Rank :=
  match t with
    None => 0
  | Some t => ltr_rank t
  end.

(* The derived constructors. *)

Definition ltnil: LTree := None.

Definition ltrNode (left right: LTreeRec): 
  forall (x:Data), 
    ltr_rank left >= ltr_rank right -> 
    x <= ltr_root left -> x <= ltr_root right -> LTreeRec :=
  fun x h pl pr => ltree (S (ltr_rank right)) x
                     (lnode x (ltr_rank left)  (ltr_root left)  (ltr_tree left)
                              (ltr_rank right) (ltr_root right) (ltr_tree right)
                            h pl pr).

(* Equational characterization of rank. *)

Lemma rank_nil: lt_rank ltnil = 0.
Proof.
auto.
Qed.

(*
Lemma rank_node: 
  forall left right h, lt_rank (ltnode left right h) = S (lt_rank right).
Proof.
auto.
Qed.
*)
