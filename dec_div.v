
Parameter x : nat.

Lemma calc : 200 + 200 = 400.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma add0n : forall n:nat, 0 + n = n.
Proof.
  intro.
  simpl.
  reflexivity.
Qed.

Lemma addn0 : forall n, n+0 = n.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.


Lemma addSnm : forall n m, S n + m = S(n + m).

Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma addnSm : forall n m, n + S m = S (n + m).
Proof.
  induction n.
  simpl.
  reflexivity.
  intro.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma add_com : forall n m, n + m = m + n.

Proof.
  induction n.
  simpl.
  intro.
  rewrite addn0.
  reflexivity.
  intro.
  simpl.
  rewrite IHn.
  rewrite addnSm.
  reflexivity.
Qed.

Lemma add_ass : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHn.
  reflexivity.
Qed.


Parameter foon : nat.



Lemma peano : forall n m, (S n)=(S m) -> n = m.

Proof.
  intros.
  assert (pred (S n) = n).
  simpl.
  reflexivity.
  rewrite <- H0.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Definition discr (n:nat) : Prop :=
  match n with
  | 0 => False
  | S _ => True
  end.


Lemma peano2 : forall n, 0<>S n.
Proof.
  intro.
  intro.
  replace False with (discr 0).
  rewrite H.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma eq_dec : forall n m : nat, n=m \/ ~n=m.

Proof.
  induction n.
  intro.
  destruct m.
  left.
  reflexivity.
  right.
  apply peano2.

  intro.
  destruct m.
  right.
  intro.
  assert (0 = S n).
  rewrite H.
  reflexivity.
  assert (0 <> S n).
  apply peano2.
  apply H1.
  assumption.

  assert (n = m \/ n <>m).
  apply IHn.
  destruct H.
  left.
  rewrite H.
  reflexivity.
  right.
  intro.
  apply H.
  apply peano.
  assumption.
Qed.


Lemma div2 : forall n, exists m, n=m+m \/ n = S(m+m).

Proof.
  induction n.

  exists 0.
  left.
  simpl.
  reflexivity.

  destruct IHn.
  destruct H.

  exists x0.
  right.
  rewrite H.
  reflexivity.

  exists (S x0).
  left.
  rewrite H.
  simpl.
  rewrite addnSm.
  reflexivity.
Qed.

