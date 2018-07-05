Parameter E: Set.

Definition subset (AppX AppY : E -> Prop) := 
  forall e : E, AppX e -> AppY e.

Lemma sub_refl:
  forall AppX : E -> Prop, subset AppX AppX.

Proof.
intros.
unfold subset.
intros.
assumption.
Qed.

Lemma sub_trans:
  forall AppX AppY AppZ: E -> Prop, subset AppX AppY -> subset AppY AppZ -> subset AppX AppZ.

Proof.
intros.
unfold subset.
intros.
apply H0.
apply H.
assumption.
Qed.


Definition eq (AppX AppY : E -> Prop) := 
  forall e : E, AppX e <-> AppY e.

Lemma eq_refl:
  forall AppX : E -> Prop, eq AppX AppX.

Proof.
intros.
unfold eq.
intro.
split; intro; assumption.
Qed.

Lemma eq_trans:
  forall AppX AppY AppZ : E -> Prop, eq AppX AppY -> eq AppY AppZ -> eq AppX AppZ.

Proof.
intros.
unfold eq.
intro.
split.
intro.
apply H0.
apply H.
assumption.
intro.
apply H.
apply H0.
assumption.
Qed.

Lemma eq_sym : 
  forall AppX AppY : E -> Prop, eq AppX AppY -> eq AppY AppX.

Proof.
intros.
unfold eq.
intro.
split; intro; apply H; assumption.
Qed.

Definition union (AppX : E -> Prop) (AppY : E -> Prop) (e : E) :=
  AppX e \/ AppY  e.

Definition intersection (AppX : E -> Prop) (AppY : E -> Prop) (e : E) :=
  AppX e /\ AppY  e.

Lemma union_comm:
  forall AppX AppY : E -> Prop, eq (union AppX AppY) (union AppY AppX).

Proof.

intros.
unfold eq.
intros.
split.
intro.
unfold union.
destruct H.
right.
assumption.
left.
assumption.

intro.
unfold union.
destruct H.
right.
assumption.
left.
assumption.
Qed.

Lemma intersection_com :
  forall AppX AppY : E -> Prop, eq (intersection AppX AppY) (intersection AppY AppX).

Proof.
intros.
unfold eq.
intros.
split.
intro.
unfold intersection.
destruct H.
split;assumption.

intro.
unfold intersection.
destruct H.
split; assumption.
Qed.

Lemma union_indem:
  forall AppX : E -> Prop, eq AppX (union AppX AppX).

Proof.
intros.
unfold eq.
intros.
split.
intro.
unfold union.
left.
assumption.

unfold union.
intro.
destruct H; assumption.
Qed.

Lemma intersection_indem:
  forall AppX : E -> Prop, eq AppX (intersection AppX AppX).

Proof.
intros.
unfold eq.
intro.
split.
intro.
unfold intersection.
split; assumption.
unfold intersection.
intro.
destruct H.
assumption.
Qed.

Lemma union_assoc:
  forall AppX AppY AppZ : E -> Prop,
    eq (union AppX (union AppY AppZ)) (union (union AppX AppY) AppZ).

Proof.
intros.
unfold eq.
intro.
split.
intro.
unfold union.
destruct H.
left.
left.
assumption.
destruct H.
left.
right.
assumption.
right.
assumption.
intro.
unfold union.
destruct H.
destruct H.
left.
assumption.
right.
left.
assumption.
right.
right.
assumption.
Qed.

Lemma intersection_comm:
  forall AppX AppY AppZ : E -> Prop,
    eq (intersection AppX (intersection AppY AppZ)) (intersection (intersection AppX AppY) AppZ).

Proof.

intros.
unfold eq.
intro.
split; unfold intersection; intro.
destruct H.
destruct H0.
split.
split;assumption.
assumption.

destruct H.

destruct H.
split. 
assumption.
split; assumption.
Qed.

Lemma distr:
  forall AppX AppY AppZ : E -> Prop,
    eq (intersection AppX (union AppY AppZ)) 
       (union (intersection AppX AppY) (intersection AppX AppZ)).
  
Proof.
intros.
unfold eq.
intro.
split; intro.
unfold union.
destruct H.
destruct H0.
left.
unfold intersection.
split; assumption.
right.
split; assumption.
unfold intersection.
destruct H.
destruct H.
split. assumption.
unfold union.
left.
assumption.
destruct H.
split.
assumption.
unfold union.
right.
assumption.
Qed.

Lemma sub_antisym:
  forall AppX AppY : E -> Prop,
    subset AppX AppY -> subset AppY AppX -> eq AppX AppY.

Proof.
intros.
unfold eq.
intro.
split; intro.
apply H.
assumption.
apply H0.
assumption.
Qed.