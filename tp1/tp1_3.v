Axiom not_not_elim : forall A : Prop, ~~A -> A.

Lemma using_TND:
forall A : Prop, ~~A -> A.

Proof.
intro.
intro.
apply not_not_elim.
assumption.
Qed. 

Lemma TND:
forall A : Prop, A \/ ~ A.

Proof.
intro A.
apply not_not_elim.
intro.
apply H.
right.
intro.
apply H.
left.
assumption.
Qed.

Lemma not_true:
~True <-> False.

Proof.
split.
intro.
apply H.
split.

intro.
destruct H.
Qed.

Lemma not_false:
~False <-> True.

Proof.
split.
intro.
split.

intro.
intro.
assumption.
Qed.


Lemma Pierce:
forall A B: Prop, ((A->B) ->A) -> A.

Proof.
intros.
apply not_not_elim.
intro.
apply H0.
apply H.
intro.
apply not_not_elim.
intro.
apply H0.
assumption.
Qed.

Lemma impl:
forall A B : Prop, (A->B) <-> (~A \/ B).

Proof.
intros.
split.

intro.
apply not_not_elim.
intro.
apply H0.
left.
intro.
apply H0.
right.
apply H.
assumption.

intros.
destruct H.
apply not_not_elim.
intro.
apply H.
assumption.

assumption.
Qed.

Lemma Morgan:
forall A B : Prop, ~(A/\B) <-> ~A \/ ~ B.

Proof.
intros.
split.
intro.
apply not_not_elim.
intro.
apply H.
split.
apply not_not_elim.
intro.
apply H0.
left.
assumption.
apply not_not_elim.
intro.
apply H0.
right.
assumption.

intro.
destruct H.
intro.
destruct H0.
apply H.
assumption.

intro.
destruct H0.
apply H.
assumption.
Qed.

Lemma Morgan2:
forall A B : Prop, ~(A\/B) <-> ~A /\ ~B.

Proof.
intros.
split.
intro.
split.
intro.
apply H.
left.
assumption.
intro.
apply H.
right.
assumption.

intro.
intro.
destruct H.
destruct H0.
apply H.
assumption.
apply H1.
assumption.
Qed.

Lemma neg_forall:
forall X : Set, forall A : X -> Prop, ~ (forall x : X, A x) <-> exists x : X, ~A x.

Proof.
intros.
split.
intro.
apply not_not_elim.
intro.
assert (forall x : X, A x).
intro.
apply not_not_elim.
intro.
apply H0.
exists x.
assumption.
apply H.
assumption.

intros.
intro.
destruct H.
apply H.
apply H0.
Qed.

Lemma neg_exists:
  forall X: Set, forall A : X-> Prop, ~(exists x : X, A x) <-> forall x :X, ~ A x.

Proof.
intros.
split.
intro.
intro.
intro.
apply H.
exists x.
assumption.

intros.
intro.
destruct H0.
assert (~(A x)).
apply H.
apply H1.
assumption.
Qed.

Lemma impland:
forall A B C : Prop, A -> (B /\ C) <->( A -> B) /\ (A -> C).

Proof.
intros.
split.
intro.
split.
intro.
assert (B /\C).
apply H.
assumption.
destruct H1.
assumption.

intro.
assert (B /\C).
apply H.
assumption.
destruct H1.
assumption.

intro.
intro.
destruct H.
assert B.
apply H.
assumption.
assert C.
apply H1.
assumption.
split;assumption.
Qed.


