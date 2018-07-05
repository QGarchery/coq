
Check 0.
Print nat.
Check nat_ind.

Check true.

Print true.

Check bool_ind.

Definition bneg b :=
  match b with
  | true => false
  | false => true
  end.

Lemma inv b :
  bneg (bneg b) = b.

Proof.
  destruct b; intuition.
Qed.

Lemma pair_ou_impair n:
  exists m, n = m + m \/ n = S( m + m).

Proof.
  induction n.
  exists 0.
  intuition.

  destruct IHn.
  destruct H; [exists x | exists (S x)].
  right.
  rewrite H.
  reflexivity.

  left.
  rewrite H.
  simpl.
  f_equal.
  clear H.
  assert (forall p q, p + S q = S (p + q)).
  induction p.
  now simpl.
  intro.
  simpl.
  f_equal.
  apply IHp.
  rewrite H.
  reflexivity.
Qed.

Fixpoint plus n m : nat :=
  match n with
  | O=> m
  | S n' => S (plus n' m)
  end.

Parameter foo : bool -> bool.
Axiom fx : forall b, foo b = negb (foo b).

Print list.

Fixpoint sorted (l : list nat) : Prop :=
  match l with
  | cons a1 r1 =>
    match r1 with
    | nil => True
    | cons a2 r2 => sorted r1 /\ a1 <= a2
    end
  | nil => True
  end.


Fixpoint comp x y :=
  match x,y with
  | 0, _ => true
  | S _, 0 => false
  | S x, S y => comp x y
  end.


Lemma comp_corr x y:
  ( comp x y = true /\ x <= y)
  \/ (comp x y = false /\y < x).

Admitted.

Fixpoint ins (e : nat) l :=
  match l with
  | nil => cons e nil
  | cons h t => if comp e h
                then cons e (cons h t)
                else cons h (ins e t)
  end.


Lemma before_ins a n l:
  a < n ->
  sorted (a :: l) ->
  a
Lemma ins_correct a l:
  sorted l ->
  sorted (ins a l).

Proof.
  intro.
  induction l.
  simpl.
  reflexivity.

  destruct (comp_corr a a0).
  destruct H0.
  simpl.
  rewrite H0.
  simpl.
  split.  
  assumption.
  assumption.

  destruct H0.
  simpl.
  rewrite H0.
  simpl.
  
  destruct (ins a l) eqn:?.
           reflexivity.
           split.

-           apply IHl.
            simpl in H.
            destruct l eqn:?.
                     simpl.
                     reflexivity.
                     intuition.

- 
  
  
  
           
Fixpoint tri l : list nat :=
  match l with
  | nil => nil
  | cons h t => ins h (tri t)
  end.

Lemma sorted_correct l:
  sorted (tri l).

Proof.
  induction l.
  
-  simpl.
   reflexivity.

-  simpl.
   destruct (tri l); trivial.
   destruct (comp_corr a n).
   destruct H.
   simpl.
   rewrite H.
   split.
   assumption.
   assumption.

   
   
   
  