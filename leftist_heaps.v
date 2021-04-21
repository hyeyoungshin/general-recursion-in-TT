(* Formalization of Leftist Heaps (Okasaki Ch.3) *)

(* The rank of a tree is the length of its rightmost path.
   In a leftist tree the rank of the left child must be
   larger or equal to the rank of the right child.

   This can be done with simultaneous induction-recursion
   by defining the type of leftist trees simultaneously
   with the rank function.

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
