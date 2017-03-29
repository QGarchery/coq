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

Lemma start_with_M_1 :
  forall w : word, lang w -> exists w' : word, w = M :: w'.


Proof.  
 intros.
induction H.
-
exists [I].
reflexivity.
-
destruct IHlang.
exists (x0 ++ [U]).
Search ( _ :: _ ++ _).
rewrite app_comm_cons.
rewrite <- H0.
Search ( _ ++ _ ++ _).
rewrite <- app_assoc.
simpl.
reflexivity.
-
destruct IHlang.
exists (x0 ++ x).
rewrite app_assoc.
rewrite H0.
rewrite app_comm_cons.
reflexivity.
-
destruct IHlang.





Lemma start_with_M_2 :
  forall w : word, lang w ->  match w with
                                   | [] => False
                                   | x::r =>  x = M end.

Proof.
  intros.
induction H.
reflexivity.
  -
    destruct (x ++ [I; U]) eqn:?.
    assert (length (x++ [I;U]) = length x + length [I;U]).
    apply app_length.
    rewrite Heql in H0.
    simpl in H0.
    Search (_ + S _ = S _).
    rewrite PeanoNat.Nat.add_succ_r in H0.
    discriminate.



Definition first_letter (w : word) : option alpha :=
  match w with
    | [] => None
    | x::w' => Some x
  end.

Lemma start_with_M_3 :
  forall w : word, lang w -> first_letter w = Some M.

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
    Search ( _ + S _ = S _).
    rewrite PeanoNat.Nat.add_succ_r in H2.
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