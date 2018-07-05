(* We load a small arithmetic library *)
(* essentially for properties of the order on nat *)
Require Import Arith.

(* look how natural numbers are defined *)
Print nat.

Search (0 <= _).

Search (0 < _).

(* we want to compare natural numbers *)
Fixpoint comp x y :=
  match x, y with
  | 0,_ => true
  | S _, 0 => false
  | S x, S y => comp x y
  end.



(* This formulation will be handy when using comp *)
Lemma comp_corr : forall x y,
    (comp x y = true /\ x<=y)
    \/(comp x y = false /\ y<x).
Proof.  
  induction x as [|x]; destruct y as [|y].
  - left; auto.
  - left. split.
    simpl.
    reflexivity.
    apply le_0_n.
  - right.
    split.
    simpl.
    reflexivity.
    apply lt_0_Sn.
  - simpl.
    assert (comp x y = true /\ x <= y \/ comp x y = false /\ y < x).
    apply IHx.
    intuition.
Qed.


Inductive list :=
  nil | cons : nat -> list -> list.

(* Check the induction principle *)
Check list_ind.

Fixpoint app (l m : list) :=
  match l with
  | nil => m
  | cons x l' => cons x (app l' m)
  end.


(* easy *)
Lemma app_ass : forall l m n,
    app l (app m n) = app (app l m) n.

Proof.
  induction l.

  - simpl.
    reflexivity.

  - simpl.
    intros.
    f_equal.
    apply IHl.
Qed.
    
    
Fixpoint length (l : list) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S(length l')
  end.

Lemma app_length :
  forall l m, length (app l m) = length l + length m.

Proof.  
  induction l.

  -  simpl.
     reflexivity.

  -  simpl.
     intro.
     f_equal.
     apply IHl.
Qed.

(* permut states that two lists are a permutation *)
(* of one another *)
(* WE WILL SEE NEXT WEEK HOW TO DEFINE IT  *)
(* Currently we just axiomatise it *)
Parameter permut : list -> list -> Prop.

Axiom permut_refl : forall l, permut l l.
Axiom permut_trans :
  forall l1 l2 l3,
    permut l1 l2 -> permut l2 l3 ->
    permut l1 l3.
Axiom permut_step : forall l1 l2 x,
    permut (cons x (app l1 l2)) (app l1 (cons x l2)).
Axiom permut_congr : forall x l1 l2,
    permut l1 l2 -> permut (cons x l1) (cons x l2).

(* The apply ... with tactic *)
Lemma ex : permut (cons 3 (cons 2 (cons 1 nil)))
                  (cons 1 (cons 2 (cons 3 nil))).

Proof.  
  apply permut_trans with (cons 3 (cons 1 (cons 2 nil))).
  apply permut_congr.
  apply (permut_step (cons 1 nil) nil).
  apply (permut_step (cons 1 (cons 2 nil)) nil).
Qed.

(* What it means for a list to be sorted *)
Definition lower x l :=
  match l with
  | nil => True
  | cons y _ => x <= y
  end.

Fixpoint sorted (l : list) :=
  match l with
  | nil => True
  | cons x l => lower x l /\ sorted l
  end.

Lemma lower_trans : forall l x y,
    lower x l -> y <= x -> lower y l.
Proof.
  intros.
  destruct l.

  -simpl.
   assumption.

  -simpl.
   simpl in H.
   now apply le_trans with x.
Qed.


(* Define the function which inserts x in a list l *)
(* preserving the sorted property *)
(* (for now we do not prove anything) *)
(* you should use comp *)
Fixpoint ins (l : list)(x : nat) :=
  match l with
  | nil => cons x nil
  | cons y l' as l => if comp x y
                      then cons x l
                      else cons y (ins l' x)
  end.

(* use ins to define insertion sort *)
Fixpoint tri (l : list) : list :=
  match l with
  | nil => nil
  | cons x l' => ins (tri l') x
  end.


Eval compute in (tri (cons 4 (cons 2 (cons 1 (cons 5 nil))))).

(* Let us prove properties wrt permutation *)

Lemma ins_ex : forall l x, exists l1 l2,
      ins l x = app l1 (cons x l2)
      /\ l = (app l1 l2).

Proof.  
  induction l.

  - exists nil, nil.
    simpl.
    intuition.

  - intro.
    assert (exists l1 l2 : list, ins l x = app l1 (cons x l2) /\ l = app l1 l2).
    apply IHl.
    destruct H.
    destruct H.
    destruct (comp x n) eqn:?.
    unfold ins.
    rewrite Heqb.
    exists nil, (cons n l).
    simpl.
    intuition.
    exists (cons n x0), x1.
    simpl.
    rewrite Heqb.
    destruct H.
    rewrite H.
    rewrite H0.
    intuition.
Qed.

Lemma ins_permut : forall x l, permut (cons x l)(ins l x).

Proof.  
  induction l.

  - simpl.
    apply permut_refl.

  -  assert ( exists l1 l2 : list, ins (cons n l) x = app l1 (cons x l2)
      /\ (cons n l) = (app l1 l2)).
     apply ins_ex.
     destruct H.
     destruct H.
     destruct H.
     rewrite H.
     rewrite H0.
     apply permut_step.
Qed.
     
Lemma tri_permut : forall l, permut l (tri l).

Proof.  
  induction l.

  - simpl.
    apply permut_refl.

  - simpl.
    destruct (ins_ex (tri l) n).
    destruct H.
    destruct H.
    rewrite H.
    apply permut_trans with (cons n (tri l)).
    apply permut_congr.
    assumption.
    rewrite H0.
    apply permut_step.
Qed.


(* Now we want to prove that the sort function *)
(* preserves sorted *)

(* We want to prove the following property *)
(* But may need to provide a stronger induction hypothesis *)
(* Can you see which one ?? *)
Lemma ins_sorted : forall x l, sorted l -> sorted (ins l x).

Proof.  
  induction l.

  - simpl.
    intuition.

  - intro.
    destruct (comp_corr x n).
    simpl.
    destruct H0.
    rewrite H0.
    simpl.
    intuition.
    simpl in H.
    intuition.
    simpl in H.
    intuition.
    destruct H0.
    simpl.
    rewrite H0.
    simpl.
    split.
    destruct l.
    simpl.
    apply lt_le_weak.
    assumption.
    simpl.
    destruct (comp x n0).
    simpl.
    apply lt_le_weak.
    assumption.
    simpl.
    simpl in H.
    intuition.
    apply IHl.
    destruct H.
    assumption.
Qed.    

Lemma tri_sorted : forall l, sorted (tri l).

Proof.
  induction l.
  
  - simpl.
    reflexivity.

  - simpl.
    apply ins_sorted.
    assumption.
Qed.
    
    (* Functional heapsort *)

(* insertion sort is of complexity n^2  *)
(* You can try to define and prove correct a similar but
efficient sorting algorithm using binary trees *)

Inductive tree :=
  | Leaf : tree
  | Node : nat -> tree -> tree -> tree.

Check tree_ind.

Fixpoint tinsert t x :=
  match t with
  | Leaf => (Node x Leaf Leaf)
  | Node y t1 t2 =>
    if comp x y
    then Node x (tinsert y t2) t1
    else Node y (tinsert x t2) t2
  end.

  (* The rest of the construction is similar to what you have done above *)
