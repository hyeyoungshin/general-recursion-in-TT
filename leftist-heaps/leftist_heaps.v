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


(* First, we indexed trees on their rank. *)

Inductive Leftist: nat -> Set :=
  lnil : Leftist 0
| lnode : forall (lrank: nat)(ltree: Leftist lrank)
                 (rrank: nat)(rtree: Leftist rrank),
          lrank >= rrank -> Leftist (S rrank).

(* Then we hide the rank. *)

Record LTree: Set := ltree
  { lt_rank: nat;
    lt_tree: Leftist lt_rank
  }.

(* The derived constructors. *)

Definition ltnil: LTree := ltree 0 lnil.

Definition ltnode (left right: LTree): lt_rank left >= lt_rank right -> LTree :=
  fun h => ltree (S (lt_rank right))
                 (lnode (lt_rank left)  (lt_tree left) 
                        (lt_rank right) (lt_tree right)
                        h).

(* Equational characterization of rank. *)

Lemma rank_nil: lt_rank ltnil = 0.
Proof.
auto.
Qed.

Lemma rank_node: 
  forall left right h, lt_rank (ltnode left right h) = S (lt_rank right).
Proof.
auto.
Qed.
