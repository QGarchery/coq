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

Parameter A B C : Prop.

Lemma totoo : 
A->A.
intro. assumption.

Lemma trans : 
(A->B) -> (B->C) -> (A->C).
intros. apply H0. apply H. assumption.

Lemma and_comm:
A /\B <-> B /\A.
Proof.
split; intro; destruct H; split; assumption. 

Lemma or_comm:
A\/B -> B \/A.
intro.
destruct H.
right.
assumption.
left.
assumption.

Lemma and_assoc:
(A /\ B) /\ C -> A /\ (B /\ C).
Proof.
intro.
destruct H.
destruct H.
split. assumption. split;assumption.


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

Lemma add_tilt:
A -> ~~A.
Proof.
intro.
