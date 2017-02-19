Parameter X Y : Set.
Parameter A B : X -> Prop.
Parameter R : X -> Y -> Prop.

Theorem and_forall:
(forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x).

Proof.
split.
intro.
split.
intro.
apply H.
 
intro.
apply H.

intro.
intro.
destruct H.
split.
apply H.

apply H0.
Qed.

Theorem or_exists:
(exists x: X, A x \/ B x) <-> (exists x: X, A x) \/ (exists x:X, B x).

Proof.
split.

intro.
destruct H.
destruct H.
left.
exists x.
assumption.
right.
exists x.
assumption.

intro.
destruct H.
destruct H.
exists x.
left.
assumption.
destruct H.
exists x.
right.
assumption.
Qed.

Theorem one_wit:
(exists y, forall x, R x y) -> forall x, exists y, R x y.

Proof.
intro.
destruct H.
intro.
exists x.
apply H.
Qed.