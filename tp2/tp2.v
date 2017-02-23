Parameter E : Set.
Parameter R : E -> E -> Prop.

Axiom refl :
  forall x : E, R x x.

Axiom trans:
  forall x y z : E, R x y -> R y z -> R x z.

Axiom antisym:
  forall x y : E, R x y -> R y x -> x = y.

Definition smallest (x0 : E) := forall x : E, R x0 x.

Definition minimal (x0 : E) := forall x : E, R x x0 -> x = x0.

Lemma unicite_minimal:
  forall x y : E, smallest x -> smallest y -> x = y.

Proof.
intros.
unfold smallest.
apply antisym.
apply H.
apply H0.
Qed.
Lemma smallest_is_minimal:
  forall x : E, smallest x -> minimal x.

Proof.
intros.
unfold minimal.
intros.
apply antisym.
assumption.
apply H.
Qed.

Lemma smallest_is_only_minimal:
  forall x y : E, smallest x -> minimal y -> x = y.

Proof.
intros.
apply H0.
apply H.
Qed.

