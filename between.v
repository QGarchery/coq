Require Import Arith.
(* Print Between. *)
(* Print Between.between_le. *)

Inductive between (P : nat -> Prop) (k : nat) : nat -> Prop :=
| bet_emp : between P k k
| bet_S : forall l : nat, between P k l -> P l -> between P k (S l).

Lemma bet_eq :
  forall (P : nat -> Prop) (k l : nat), l = k -> between P k l.
Proof.
  intros P k l eqlk. rewrite eqlk. apply bet_emp.
Qed.

Lemma between_le :
  forall (P : nat -> Prop) (k l : nat), between P k l -> k <= l.
Proof.
  intros P k l bet. induction bet.
  -trivial.
  -apply le_trans with l. assumption. apply le_n_Sn.
Qed.

Lemma between_Sk_l :
  forall (P : nat -> Prop) (k l : nat),
    between P k l -> S k <= l -> between P (S k) l.
Proof.
  intros P k l bet skl. induction bet as [ | l p1 IHp1 p2].
  -exfalso. eapply le_Sn_n. apply skl.
  -destruct (le_lt_dec (S k) l) as [ le_sk_l | lt_l_sk ].
   +apply IHp1 in le_sk_l. now apply bet_S.
   +apply lt_le_S in lt_l_sk.
    assert (eq_sk_sl : S k = S l). now apply le_antisym.
    rewrite eq_sk_sl. now apply bet_emp.
Qed.

Lemma between_restr :
  forall (P : nat -> Prop) (k l m : nat),
    k <= l -> l <= m -> between P k m -> between P l m.
Proof.
  intros P k l m le_k_l le_l_m bet.
  induction le_k_l as [ | l le_n_l IH].
  -assumption.
  -apply between_Sk_l; trivial.
   apply IH. apply le_trans with (S l). apply le_n_Sn. assumption.
Qed.

Inductive exists_between (Q : nat -> Prop) (k : nat) : nat -> Prop :=
|  exists_S : forall l : nat,
    exists_between Q k l -> exists_between Q k (S l)
| exists_le : forall l : nat, k <= l -> Q l -> exists_between Q k (S l).

Lemma exists_le_S :
  forall (Q : nat -> Prop) (k l : nat), exists_between Q k l -> S k <= l.
Proof.
  induction 1. apply le_trans with l. assumption. now apply le_S.
  now apply le_n_S.
Qed.

Lemma exists_lt :
  forall (Q : nat -> Prop) (k l : nat), exists_between Q k l -> k < l.
Proof.
  now apply exists_le_S.
Qed.

Lemma exists_S_le :
  forall (Q : nat -> Prop) (k l : nat), exists_between Q k (S l) -> k <= l.
Proof.
  intros. apply le_S_n. now apply exists_le_S with Q.
Qed.

Definition in_int : nat -> nat -> nat -> Prop :=
  fun p q r : nat => p <= r < q.

Lemma in_int_intro :
    forall p q r : nat, p <= r -> r < q -> in_int p q r.
Proof.
  split; assumption.
Qed.

Lemma in_int_lt :
  forall p q r : nat, in_int p q r -> p < q.
Proof.
  intros p q r H. destruct H.
  now apply le_lt_trans with r.
Qed.

Lemma in_int_p_Sq :
  forall p q r : nat, in_int p (S q) r -> in_int p q r \/ r = q.
Proof.
  intros p q r H.
  destruct H as [ H1 H2 ]. apply le_S_n in H2.
  destruct (le_lt_eq_dec r q) as [ltrq | eqrq]. assumption.
  -left. split; assumption.
  -now right.
Qed.
  
Lemma in_int_S :
  forall p q r : nat, in_int p q r -> in_int p (S q) r.
Proof.
  intros p q r H.
  destruct H.
  split; trivial.
  apply lt_le_trans with q; trivial.
  now apply le_S.
Qed.

Lemma in_int_pred p q :
  p <= q -> in_int p (S q) q.
Proof.
  split; unfold "<" ; trivial.
Qed.
  
Lemma in_int_Sp_q :
  forall p q r : nat, in_int (S p) q r -> in_int p q r.
Proof.
  intros p q r H. destruct H. split; trivial.
  apply le_trans with (S p). now apply le_S. assumption.
Qed.
  
Lemma between_in_int :
  forall (P : nat -> Prop) (k l : nat),
    between P k l -> forall r : nat, in_int k l r -> P r.
Proof.
  intros P k l Hb r Hi. destruct Hi as [H1 H2].
  induction Hb as [|l H IH pl].
  -exfalso. apply (lt_irrefl k).
   now apply le_lt_trans with r.
  -destruct (le_lt_eq_dec _ _ H2) as [Hlt | Heq].
   +apply le_S_n in Hlt. now apply IH. 
   +injection Heq. intro Heq'. now rewrite Heq'.
Qed.
   
Lemma in_int_between :
  forall (P : nat -> Prop) (k l : nat),
    k <= l -> (forall r : nat, in_int k l r -> P r) -> between P k l.
Proof.
  intros P k l. induction 1; intros.
  -apply bet_emp.
  -apply bet_S.
   +apply IHle. intros r Hi. apply H0. now apply in_int_S.
   +apply H0. now apply in_int_pred.
Qed.

Lemma exists_in_int :
  forall (Q : nat -> Prop) (k l : nat),
    exists_between Q k l -> exists2 m : nat, in_int k l m & Q m.
Proof.
  intros Q k l H. induction H as [l H IH | l leq ql].
  -destruct IH as [ x H1 H2]. exists x.
   now apply in_int_S. assumption.
  -exists l. now apply in_int_pred. assumption.
Qed.

Lemma exists_right_le Q k l r :
  exists_between Q k l -> l <= r -> exists_between Q k r.
Proof.
  induction 2.
  -assumption.
  -now apply exists_S.
Qed.

Lemma in_int_exists :
  forall (Q : nat -> Prop) (k l r : nat),
    in_int k l r -> Q r -> exists_between Q k l.
Proof.
  intros Q k l r H qr. destruct H.
  apply exists_right_le with (S r).
  -now apply exists_le.
  -assumption.
Qed.  
  
Lemma between_or_exists :
  forall (P Q : nat -> Prop) (k l : nat),
    k <= l ->
    (forall n : nat, in_int k l n -> P n \/ Q n) ->
    between P k l \/ exists_between Q k l.
Proof.
  intros P Q k l. induction 1 as [| l H IH].
  -left. apply bet_emp.
  -intro f. destruct IH.
   intros. apply f. now apply in_int_S.
   destruct (f l). now apply in_int_pred.
   left. now apply bet_S.
   right. now apply exists_le.
   right. now apply exists_S.
Qed.
   
Lemma between_not_exists :
  forall (P Q : nat -> Prop) (k l : nat),
    between P k l ->
    (forall n : nat, in_int k l n -> P n -> ~ Q n) -> ~ exists_between Q k l.
Proof.
  intros P Q k l bet H ex.
  apply exists_in_int in ex. destruct ex as [x inx qx].
  apply H in inx. now apply inx.
  now apply between_in_int with k l.
Qed.
