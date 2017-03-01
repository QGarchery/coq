Lemma plusO:
  forall m : nat, 0+m = m.

  Proof.
intro.
reflexivity.
Qed.

  Lemma plusdef:
    forall m n : nat, S m + n = S (m + n).
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Lemma add_0_r : forall n, n + 0 = n.
  Proof.
    intros.
    induction n.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma add_succ_r : forall n m, n + S m = S (n + m).
  Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma add_assoc : forall n m p, (n + m) + p = n + (m + p).
  Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
  Qed.
  
  Lemma add_comm : forall n m, n + m = m + n.
  Proof.
    intros.
    induction n.
    simpl.
    rewrite add_0_r.
    reflexivity.
    simpl.
    rewrite IHn.
    rewrite add_succ_r.
    reflexivity.
  Qed.


  Lemma mul_0_l : forall n, 0 * n = 0.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Lemma mul_succ_l : forall n m, S n * m = m + n * m.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Lemma mul_0_r : forall n, n * 0 = 0.
  Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    assumption.
  Qed.

  Lemma mul_succ_r : forall n m, n * S m = n + n * m.
  Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    f_equal.
    rewrite <- !add_assoc.
    replace (m+n) with (n+m).
    reflexivity.
    rewrite add_comm.
    reflexivity.
  Qed.

  Lemma mul_distr : forall n m p, (n + m) * p = n * p + m * p.
  Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    rewrite add_assoc.
    reflexivity.
  Qed.

  Lemma mul_assoc : forall n m p, (n * m) * p = n * (m * p).
  Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite mul_distr.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma mul_comm : forall n m, n * m = m * n.
  Proof.
    intros.
    induction n.
    simpl.
    rewrite mul_0_r.
    reflexivity.
    simpl.
    rewrite IHn.
    rewrite mul_succ_r.
    reflexivity.
  Qed.

  Definition le (n m : nat) := exists p, n + p = m.
Infix "<=" := le.

Lemma le_refl : forall n, n <= n.
Proof.
  intros.
  unfold le.
  exists 0.
  rewrite add_0_r.
  reflexivity.
Qed.

Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  intros.
  unfold le.
  destruct H.
  destruct H0.
  exists (x+x0).
  rewrite <- add_assoc.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.


Lemma addtoO:
  forall x y : nat, x+y=0 -> x = 0.
Proof.
  intros.
  induction x.
  reflexivity.
  assert (S (x+y) = 0).
  rewrite <- H.
  simpl.
  reflexivity.
  discriminate H0.
Qed.

Lemma simpl_l:
  forall m1 m2 n: nat, n + m1 = n + m2 -> m1 = m2.
Proof.
  intros.

  induction n.  
    assert (m2 = 0 + m1).
    rewrite H.
    simpl.
    reflexivity.
    rewrite H0.
    simpl.
    reflexivity.
    apply IHn.
    assert ( S (n+m1) = S (n +m2)).
    assert ( S n + m1 = S (n+m2)).
    rewrite H.
    simpl.
    reflexivity.
    rewrite <- H0.
    simpl.
    reflexivity.
    injection H0.
    intro.
    assumption.

Qed.


    Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.

  Proof.
    intros.
    destruct H.
    destruct H0.
    assert (m + (x0 + x) = m +0).
    rewrite add_0_r.
    rewrite <- add_assoc.
    rewrite H0.
    rewrite H.
    reflexivity.
    assert  (x0 + x = 0) .
    apply (simpl_l _ _ m) .
    assumption.
    assert (x0 = 0).
    apply (addtoO _ x).
    assumption.
    rewrite <- H0.
    rewrite H3.
    rewrite add_0_r.
    reflexivity.
  Qed.
  