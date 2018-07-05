Definition Leibniz (T:Type)(x : T) :=
  fun y=>
    forall P : T->Prop, (P y) -> (P x).

Lemma Lte : forall T x y, Leibniz T x y -> x = y.

Proof.
  intros.
  apply (H (fun t => t = y)).
  reflexivity.
Qed. 
  
Lemma etL : forall T x y, x = y -> Leibniz T x y.

Proof.
  intros.
  intro.
  intro.
  rewrite H.
  assumption.  
Qed.

(* Do the following ones without using the two previous lemmas *)

Lemma L_sym : forall T x y, Leibniz T x y -> Leibniz T y x.

Proof.
  intros.
  apply H.
  intro.
  intuition.
Qed.


Lemma L_trans : forall T x y z,
        Leibniz  T x y -> Leibniz T y z ->  Leibniz T x z.

Proof.
  intros.
  apply H.
  assumption.
Qed.
    
(* Redefine conjunction and/or disjunction and do the same *)
Definition imp_and (A:Prop)(B:Prop) :=
  forall P, (A -> B -> P) -> P.

Lemma imp_and_and A B:
  imp_and A B -> A /\B.

Proof.
  intro.
  apply X.
  intuition.
Qed.

Lemma and_imp_and A B:
  A /\ B -> imp_and A B.

Proof.
  intro.
  intro.
  intro.
  destruct H.
  apply X; assumption.
Qed.  

Definition imp_or (A B : Prop) :=
  forall P : Prop,  (A -> P) -> (B -> P) -> P.

Lemma imp_or_or A B:
  imp_or A B -> A \/ B.

Proof.
  intro.
  apply H; intuition.
Qed.


Lemma or_imp_or (A : Prop) (B : Prop) :
  A \/ B ->  imp_or A B.

Proof.
  intro.
  intro.
  intuition.
Qed.

(* We redefine less-or-equal *)

Inductive leq (n : nat) : nat -> Prop :=
|  leq_n : leq n n
|  leq_S : forall m, leq n m -> leq n (S m).

Lemma leq_trans : forall n m p, leq n m -> leq m p -> leq n p.

Proof.
  intros n m p.
  induction 2.
  intuition.
  apply leq_S.
  assumption.
Qed.

(* here you have to chose between induction 1 and induction 2 *)

(* Well-foundedness - here impredicative version *)

Definition Acc (T:Type) (R : T->T->Prop) :=
  fun x => forall P : T->Prop,
      (forall z, (forall y, R z y -> P y) -> P z) -> P x.


Lemma eqnwf : forall n, ~(Acc nat eq n).

Proof.
  intros.
  unfold Acc.
  intro.
  Definition P (n : nat) := False.
  assert (False = P n).
  reflexivity.
  rewrite H0.
  apply H.
  intros.
  apply H1.
  reflexivity.
Qed.


