Require Import List.

Import ListNotations.
  
Lemma concat_nil_l:
  forall (A : Type) (l : list A), []++ l = l.

Proof.
  intros.
  simpl.
  reflexivity.
  Qed.

Lemma concat_nil_r:
  forall (A : Type) (l : list A), l ++ [] = l.


  

Definition g (A : Type) (l : list A)  := l ++ [] = l.
Proof.
  intros.
  apply (list_ind (g A)).
  unfold g.
  simpl.
  reflexivity.
  intros.
  unfold g.
  simpl.
  rewrite H.
  reflexivity.
Qed.


Lemma concat_assoc:
  forall (A : Type) (l1 l2 l3 : list A), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).

Definition h (A : Type) (l2 l3 : list A) (l1 : list A) := (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).

Proof.  
  intros.
  apply (list_ind (h A l2 l3)).
  unfold h.
  rewrite (concat_nil_l A l2).
  rewrite (concat_nil_l A (l2 ++ l3)).
  reflexivity.
  intros.
  unfold h.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Fixpoint length {A : Type} (l : list A) := 
  match l with 
    | [] => 0
    | a :: l => 1 + length l
  end.

Lemma adding_length:
  forall (A : Type) (l1 l2 : list A), 
    length (l1 ++ l2) = length l1 + length l2.

Definition k (A : Type) (l2 : list A) (l1 : list A) := 
    length (l1 ++ l2) = length l1 + length l2.


Require Import Arith.
Proof.
  intros.
  apply (list_ind (k A l2)).
  unfold k.
  simpl.
  reflexivity.
  intros.
  unfold k.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Fixpoint rev_append {A : Type} (l1 l2 : list A) : list A := 
  match l1 with
    | [] => l2
    | a :: l => rev_append l (a :: l2)
  end.

Definition rev {A : Type} (l : list A) : list A :=
  rev_append l [].

Lemma len_rev:
  forall (A : Type) (l : list A), 
    length (rev l) = length l.

Lemma len_rev_append:
  forall (A : Type) (l1 l2 : list A), 
    length (rev_append l1 l2) = length l1 + length l2.

Definition ll {A : Type} (l1 : list A):= 
  forall (l2 : list A), length (rev_append l1 l2) = length l1 + length l2.

Proof.
  intros.  
  apply (list_ind ll).
  unfold ll.
  unfold rev_append.
  simpl.
  reflexivity.
  intros.
  unfold ll.
  intros.
  simpl.
  rewrite H.
  simpl.
  ring.
Qed.

Proof.
intros.
unfold rev.
rewrite len_rev_append.
simpl.
ring.
Qed.
Lemma rev_concat:
  forall (A : Type) (l1 l2 : list A), 
    rev (l1 ++ l2) = (rev l2) ++ (rev l1).

Lemma revappend:
  forall (A : Type) (l1 l2 l3 : list A), 
    rev_append l1 (l2 ++ l3) = (rev_append l1 l2) ++ l3.

Definition m (A : Type) (l3 : list A) (l1 : list A) := 
  forall l2 : list A, rev_append l1 (l2 ++ l3) = (rev_append l1 l2) ++ l3.

Lemma unsimpl_concat:
  forall (A : Type) (a : A) (l1 l2 : list A),
    (a :: l1) ++ l2 = a :: (l1 ++ l2).

Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Proof.
  intros.
  apply (list_ind (m A l3)).
  unfold m.
  simpl.
  reflexivity.
  intros.
  unfold m.
  intros.
  simpl.
  rewrite <- unsimpl_concat.
  rewrite H.
  reflexivity.
Qed.

Definition nn (A : Type) (l1 : list A) := 
  forall l2 : list A, rev_append (l1 ++ l2) [] = (rev_append l2 []) ++ (rev_append l1 []).

Proof.
  intros.
  apply (list_ind (nn A)).  
  unfold nn.
  intros.
  simpl.
  rewrite concat_nil_r.
  reflexivity.
  intros.
  unfold nn.
  intros.
  simpl.
  assert (rev_append (l ++ l0) ([] ++ [a]) = rev_append l0 [] ++ rev_append l [a]).
  rewrite (revappend A (l ++ l0) [] [a]).
  rewrite H.
  rewrite concat_assoc.
  rewrite <- (revappend A l [] [a]).
  simpl.
  reflexivity.
  rewrite <- H0.
  simpl.
  reflexivity.
Qed.


