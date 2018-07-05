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

Fixpoint puiss (n : nat) (R : T -> T -> Prop) : T -> T -> Prop :=
  match n with 
    | 0 => id 
    | S p => comp R (puiss p R)
  end.  


Definition clos3 (R : T -> T -> Prop) (x y : T) := exists n, puiss n R x y.  


Lemma clos3_base :
  forall R : T -> T -> Prop,
  forall x y : T,
    R x y -> clos3 R x y.

Proof.                                       
  intros.
  exists 1.
  unfold puiss.
  unfold comp.
  exists y.
  split.
  assumption.
  reflexivity.
Qed.

Lemma clos3_refl :
  forall R : T -> T -> Prop,
  forall x : T, clos3 R x x.

Proof.
  intros.
  exists 0.
  reflexivity.
Qed.


Lemma adding_puiss :
  forall R : T -> T -> Prop,
      forall n1 n2 : nat,
      forall x y z : T,
        puiss n1 R x y -> puiss n2 R y z -> puiss (n1 + n2) R x z.

Proof.  
  intro.
  induction n1.
  intros.
  rewrite plus_0_l.
  rewrite H.
  assumption.
  intros.
  destruct H.
  destruct H.
  rewrite plus_Sn_m.
  unfold puiss.
  unfold comp.
  exists x0.
  split.
  assumption.
  apply (IHn1 n2 x0 y z).
  assumption.
  assumption.
Qed.


Lemma clos3_trans : 
  forall R : T -> T -> Prop,
    forall x y z : T,
      clos3 R x y -> clos3 R y z -> clos3 R x z.



Proof.
  intros.
  destruct H, H0.
  exists (x0 + x1).
  apply (adding_puiss R x0 x1 x y z).
  assumption.
  assumption.
Qed.



Lemma clos1_in_clos3 :
  forall x y : T,
    forall R : T -> T -> Prop,
      clos1 R x y -> clos3 R x y.

Proof.
  intros.
  induction H.
  apply clos3_base.
  assumption.
  apply clos3_refl.
  apply (clos3_trans R x y z).
  assumption.
  assumption.
Qed.


Lemma puiss_in_clos1:
  forall R : T -> T -> Prop,
    forall n : nat,
      forall x y : T,
        puiss n R x y -> clos1 R x y.

Proof.
  intro.
  induction n.
- 
intros.
rewrite H.
apply cl1_refl.
-
intros.
destruct H.
destruct H.
apply (cl1_trans R x x0 y).
apply cl1_base.
assumption.
apply IHn.
assumption.
Qed.

Lemma clos3_in_clos1 :
  forall x y : T,
    forall R : T -> T -> Prop,
      clos3 R x y -> clos1 R x y.

Proof.
  intros.
  destruct H.
  apply (puiss_in_clos1 R x0 x y).
  assumption.
Qed.


Lemma clos3_eq_clos2:
  forall x y : T,
    forall R : T -> T -> Prop,
      clos3 R x y <-> clos2 R x y.

Proof.
  intros.
  split; intros.
  apply clos1_in_clos2.
  apply clos3_in_clos1.
  assumption.
  apply clos1_in_clos3.
  apply clos2_in_clos1.
  assumption.
Qed.
