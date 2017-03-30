Require Import List.
Import ListNotations.

Inductive alpha := M | I | U.

Check alpha_rec.
Definition word := list alpha.

Inductive lang : word -> Prop :=
| axiom : lang [M;I]
| rule1 x : lang (x ++ [I]) -> lang (x ++ [I;U])
| rule2 x : lang ([M] ++ x) -> lang ([M] ++ x ++ x)
| rule3 x y : lang (x ++ [I;I;I] ++ y) -> lang (x ++ [U] ++ y)
| rule4 x y : lang (x ++ [U;U] ++ y) -> lang (x ++ y).

Definition first_letter (w : word) : option alpha :=
  match w with
  | [] => None
  | x::w' => Some x
  end.
Lemma first_ext :
  forall w1 w2 : word,
    w1 <> [] -> first_letter w1 = first_letter (w1 ++ w2).

Proof.
  intros.
  destruct w1.
  destruct H.
  reflexivity.
  rewrite <- app_comm_cons.
  unfold first_letter.
  reflexivity.
Qed.  

Lemma start_with_M_2 :
  forall w : word, lang w -> first_letter w = Some M.
Proof.
  intros.
  induction H.
  unfold first_letter.
  reflexivity.
  -
    assert ([I; U] = [I] ++ [U]).
    simpl.
    reflexivity.
    rewrite H0.
    rewrite  app_assoc.
    rewrite <- first_ext.
    assumption.
    intro.
    assert (length x + length [I] = 0).
    Search (length _ + length _ ).
    rewrite <- app_length.
    rewrite H1.
    simpl.
    reflexivity.
    simpl in H2.
    Search (?X1 + _ = _ + ?X1).
    rewrite Plus.plus_comm in H2.
    rewrite plus_Sn_m in H2.
    discriminate.
  -
    rewrite app_assoc.
    rewrite <- first_ext.
    assumption.
    intro.
    rewrite H0 in IHlang.
    simpl in IHlang.
    discriminate.
  -
    destruct x.
    simpl in IHlang.
    discriminate.
    simpl in IHlang.
    simpl.
    assumption.
  -
    destruct x.
    simpl in IHlang.
    discriminate.
    rewrite <- first_ext.
    rewrite <- first_ext in IHlang.
    assumption.

    Search ( _ <> _).
    apply not_eq_sym.
    apply nil_cons.
    apply not_eq_sym.
    apply nil_cons.
Qed.

Lemma start_with_M_1 :
  forall w : word, lang w -> exists w' : word, w = M :: w'.

Proof.  
  intros.
  destruct w.
  assert (first_letter [] = Some M).
  apply start_with_M_2.
  assumption.
  simpl in H0.
  discriminate.
  exists w.
  assert (first_letter (a::w) = Some M).
  apply start_with_M_2.
  assumption.
  simpl in H0.
  assert (a = M).
  injection H0.
  intro.
  assumption.
  rewrite H1.
  reflexivity.
Qed.

Inductive Z3 := Z0 | Z1 | Z2.

Definition succ (z : Z3) : Z3 :=
  match z with
  | Z0 => Z1
  | Z1 => Z2
  | Z2 => Z0
  end.

Definition add (z1 z2 : Z3) : Z3 :=
  match z2 with
  | Z0 => z1
  | Z1 => succ z1
  | Z2 => succ (succ z1)
  end.

Infix "+" := add.


Lemma comm:
  forall z1 z2 : Z3, z1 + z2 = z2 + z1.

Proof.
  intros.
  destruct z2; destruct z1; simpl; reflexivity.
Qed.

Lemma assoc:
  forall z1 z2 z3 : Z3, (z1 + z2) + z3 = z1 + (z2 + z3).

Proof.
  intros.
  destruct z1; destruct z2; destruct z3; simpl; reflexivity.
Qed.

Lemma double_not_zero:
  forall z : Z3, z <> Z0 -> z+z <> Z0.

Proof.
  intros.
  destruct z; simpl.
  assumption.
  discriminate.
  discriminate.
Qed.

Lemma elt_neutre :
  forall z : Z3, z + Z0 = z.

Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Fixpoint occurI3 (w : word) : Z3 :=
  match w with
  | [] => Z0
  | h::t => match h with
            | M | U => occurI3 t
            | I => succ (occurI3 t)
            end
  end.

Lemma succ_Sn_m :
  forall a b : Z3,
    succ (a + b) = succ a + b.

Proof.
  intros.
  destruct a; destruct b; simpl; reflexivity.
Qed.



Lemma add_occur :
  forall v w : word,
    occurI3 (v ++ w) = (occurI3 v)+(occurI3 w).

Proof.
  intros.
  induction v.
  rewrite comm.
  simpl.
  reflexivity.
  destruct a.
  simpl.
  assumption.
  simpl.
  rewrite IHv.
  rewrite succ_Sn_m.
  reflexivity.
  simpl.
  assumption.
Qed.

Lemma not_Z0:
  forall w : word,
    lang w -> occurI3 w <> Z0.

Proof.
  intros.

  induction H.
  -
    simpl.
    discriminate.
  -
    rewrite add_occur.
    simpl.
    rewrite add_occur in IHlang.
    simpl in IHlang.
    assumption.
  -
    simpl.
    simpl in IHlang.
    rewrite add_occur.
    apply double_not_zero.
    assumption.
  -
    rewrite add_occur.
    rewrite add_occur.
    simpl.
    rewrite add_occur in IHlang.
    rewrite add_occur in IHlang.
    simpl in IHlang.
    assumption.
  -
    rewrite add_occur.
    rewrite add_occur in IHlang.
    rewrite add_occur in IHlang.
    simpl in IHlang.
    assert (Z0 + occurI3 y = occurI3 y).
    rewrite comm.
    simpl.
    reflexivity.
    rewrite H0 in IHlang.
    assumption.
Qed.

Lemma enigle_MU:
  ~ ( lang [M; U] ).

Proof.
  intro.
  assert (occurI3 [M; U] = Z0).
  simpl.
  reflexivity.
  assert (occurI3 [M; U] <> Z0).
  apply not_Z0.
  assumption.
  apply H1.
  assumption.
Qed.
