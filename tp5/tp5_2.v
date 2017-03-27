Parameter T:Type.

Require Import Arith.

Inductive clos1 (R : T -> T -> Prop) : T -> T -> Prop :=
| cl1_base : forall x y, R x y -> clos1 R x y
| cl1_refl : forall x, clos1 R x x
| cl1_trans : forall x y z, clos1 R x y -> clos1 R y z -> clos1 R x z.


Lemma cl1_ind :
  forall R P : T -> T -> Prop,
    (forall x y : T, R x y -> P x y) ->
    (forall x : T, P x x) ->
    (forall x y z : T, P x y -> P y z -> P x z) ->
    forall t t0 : T, clos1 R t t0 -> P t t0.

Proof.
intros.
induction H2.
apply H.
assumption.
apply H0.
apply (H1 x y z).
assumption.
assumption.
Qed.

Definition sym (R : T -> T -> Prop) : Prop :=
  forall x y : T, R x y -> R y x.

Lemma clos1_sym :
  forall R : T -> T -> Prop,
    sym R -> sym (clos1 R).

Proof.
  unfold sym.
  intros.
  induction H0.
  apply cl1_base.
  apply H.
  assumption.
  apply cl1_refl.
  apply (cl1_trans R z y x).
  assumption.
  assumption.
Qed.


Lemma cl1_on_refl :
  forall R : T -> T -> Prop,
    (forall x : T, R x x) ->
    (forall x y z : T, R x y -> R y z -> R x z) ->
    forall x y : T, clos1 R x y <-> R x y.

Proof.

intros.
split.
intro.
induction H1.
assumption.
apply H.
apply (H0 x y z).
assumption.
assumption.
intro.
apply cl1_base.
assumption.

Qed.



Lemma indempotente :
  forall x y : T, forall R : T -> T -> Prop,   
      clos1 (clos1 R) x y -> clos1 R x y.

Proof.
  intros.
  apply (cl1_on_refl (clos1 R)).
  intro.
  apply cl1_refl.
  apply cl1_trans.
  assumption.
Qed.


Inductive clos2 (R : T -> T -> Prop) : T -> T -> Prop :=
| cl2_refl : forall x, clos2 R x x
| cl2_next : forall x y z, clos2 R x y -> R y z -> clos2 R x z.

Lemma clos2_in_clos1 :
  forall x y : T,
    forall R : T -> T -> Prop,
      clos2 R x y -> clos1 R x y.

Proof.
  intros.
  induction H.
  apply cl1_refl.
  apply (cl1_trans R x y z).
  assumption.
  apply cl1_base.
  assumption.
Qed.

Lemma cl2_base :
  forall R : T -> T -> Prop,
  forall x y : T,
    R x y -> clos2 R x y.

Proof.
  intros.
  apply (cl2_next R x x y).
  apply cl2_refl.
  assumption.
Qed.

Lemma cl2_trans : 
  forall R : T -> T -> Prop,
    forall x y z : T,
      clos2 R x y -> clos2 R y z -> clos2 R x z.

Proof.
  intros.
  induction H0.
  assumption.
  apply (cl2_next R x y z).
  apply IHclos2.
  assumption.
  assumption.
Qed.

Lemma clos1_in_clos2 :
  forall x y : T,
    forall R : T -> T -> Prop,
      clos1 R x y -> clos2 R x y.

Proof.
  intros.
  induction H.
  apply cl2_base.
  assumption.
  apply cl2_refl.
  apply (cl2_trans R x y z).
  assumption.
  assumption.
Qed.

Definition id (x y : T) : Prop :=
  x = y.

Definition comp (R1 R2 : T -> T -> Prop) (x z : T) : Prop :=
  exists y : T,
    R1 x y /\ R2 y z.

Inductive puiss (R : T -> T -> Prop) : nat -> T -> T -> Prop :=
| exp0 : forall x y : T, id x y -> puiss R 0 x y
| exp_ind : forall n : nat, forall x y : T, comp R (puiss R n) x y -> puiss R (S n) x y.


Definition clos3 (R : T -> T -> Prop) (x y : T) := exists n, puiss R n x y.


Lemma clos3_in_clos1:
  forall R : T->T->Prop,
    forall x y : T,
      clos3 R x y -> clos1 R x y.

Proof.
  intros.
  destruct H.
  induction x0.
  


  
Lemma adding_puiss :
  forall R : T -> T -> Prop,
      forall n1 n2 : nat,
        forall x y z : T,
          puiss R n1 x y -> puiss R n2 y z -> puiss R (n1 + n2) x z.

Proof.
  intro.
  induction n1.
  intros.
  rewrite plus_0_l.
  induction H0.
  rewrite <- H0.
  assumption.
  

  

Lemma puiss0 :
  forall R : T->T->Prop,
    forall x y : T, puiss R 0 x y -> id x y.

Proof.
  intros.
  
  