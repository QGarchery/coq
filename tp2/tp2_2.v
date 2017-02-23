Axiom not_not_elim:
  forall A : Prop, ~~A -> A.

Parameter Piece : Set.
Parameter Hydrate : Piece -> Prop.
Parameter Exist : Piece -> Prop.

Lemma buveurs:
 (exists p : Piece, Exist p) -> (exists p1 : Piece, Hydrate p1 -> forall p2 : Piece, Hydrate p2).

Proof.
intros.
destruct H.
assert ((forall p : Piece, Hydrate p) \/ ~ (forall p: Piece, Hydrate p)).
apply not_not_elim.
intro.
apply H0.
right.
intro.
apply H0.
left.
assumption.
destruct H0.

exists x.
intro.
assumption.

assert (exists x : Piece, ~ Hydrate x).
apply not_not_elim.
intro.
apply H0.
intro.
apply not_not_elim.
intro.
apply H1.
exists p.
assumption.

destruct H1.
exists x0.
intro.
assert False.
apply H1.
assumption.
destruct H3.
Qed.
