Require Import Omega.

Inductive all_prec_true : nat -> Prop :=
| ini y : (forall x, x < y -> all_prec_true x) -> all_prec_true y.

Lemma all_true y : all_prec_true y.
Proof.
  induction y as [| y H].
  -apply ini.
   intros x xn. omega.
  -inversion H. apply ini. intros x px.
   apply le_lt_or_eq_iff in px. destruct px.
   +apply H0. omega.
   +injection H2; intro H3. now rewrite H3.
Qed.

Theorem strong_induction :
  forall P : nat -> Prop,
    (forall x, (forall y, y < x -> P y) -> P x) ->
    forall x, P x.
Proof.
  intros P reP x.
  apply all_prec_true_ind.
  intros y Qt Qr. now apply reP.
  apply all_true.
Qed.

Print strong_induction.


