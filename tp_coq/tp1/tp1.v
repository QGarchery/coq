Lemma and_commut :
forall A B : Prop, A /\ B <-> B /\ A.


Proof.
intros. split.

- intros. destruct H. split. assumption. assumption.
- intros. destruct H. split; assumption.
Qed.

Lemma toto :
forall A : Prop, A -> A.

Proof.
intro. intro.
assumption.
Qed.
Parameter A B C : Prop.

Lemma totoo : 
A->A.

Proof.
intro. assumption.
Qed.

Lemma trans : 
(A->B) -> (B->C) -> (A->C).

Proof.
intros. apply H0. apply H. assumption.
Qed.

Lemma and_comm:
A /\B <-> B /\A.
Proof.
split; intro; destruct H; split; assumption. 
Qed.

Lemma or_comm:
A\/B -> B \/A.

Proof.
intro.
destruct H.
right.
assumption.
left.
assumption.
Qed.

Lemma and_assoc:
(A /\ B) /\ C -> A /\ (B /\ C).

Proof.
intro.
destruct H.
destruct H.
split. assumption. split;assumption.
Qed.

Lemma or_assoc:
(A \/ B) \/ C <-> A \/ (B \/ C).

Proof.
split.
intro.
destruct H.
destruct H.
left. assumption.
right. left. assumption.
right. right. assumption.

intro.
destruct H.
left. left. assumption.
destruct H.
left. right. assumption.
right. assumption.
Qed.

Lemma add_tilt:
A -> ~~A.

Proof.
intro.
intro.
apply H0.
assumption.
Qed.

Theorem contraposition:
(A -> B) -> ~B -> ~ A.

Proof.
intros.
intro.
apply H0.
apply H.
assumption.
Qed.

Theorem almost_TND:
~~(A \/ ~A).

Proof.
intro.
apply H.
right.
intro.
apply H.
left.
assumption.
Qed.




