Require Import Bool ROmega NDiv.
Open Scope N_scope.

Definition EM :=
  forall P : Prop, P \/ ~P.

Definition LPO :=
  forall P : N -> bool,
    (forall n, P n = false) \/ (exists n, P n = true).

Definition LLPO :=
  forall P : N -> bool,
    (forall m n, P m = true -> P n = true -> m = n) ->
    (forall n, P (2 * n) = false) \/ (forall n, P (2 * n + 1) = false).

Definition LPPO :=
  forall P : N -> Prop,
    (forall n, ~ P n) \/ (exists n, P n).

Lemma EM_to_LPO : 
  EM -> LPO.
Proof.
  intros em P.
  destruct (em (exists n, P n = true)) as [H|H].
  -now right.
  -left. intro n. apply not_true_is_false. intro Pn.
   apply H. now exists n.
Qed.  
  
Lemma LPO_to_LLPO:
  LPO -> LLPO.
Proof.
  intros lpo P Q.
  destruct (lpo (fun n => P (2*n))).
  -now left.
  -right. destruct H as [m H].
   intro n. apply not_true_is_false. intro nH.
   assert (G := Q _ _ H nH). clear P Q H nH.

   replace (2 * m) with (m * 2) in G; [ | apply N.mul_comm].
   change (m * 2) with (0 + m * 2) in G.
   replace (2 * n + 1) with (1 + 2 * n) in G; [| apply N.add_comm].
   replace (2 * n) with (n * 2) in G; [| apply N.mul_comm].

   assert (U : 2 <> 0). intro U; discriminate U.
   assert (H1 : (0 + m * 2) mod 2 = 0). now apply N.mod_add. 
   assert (H2 : (1 + n * 2) mod 2 = 1). now apply N.mod_add.

   rewrite G in H1. rewrite H1 in H2. discriminate H2.
Qed.

Lemma LPPO_to_EM:
  LPPO -> EM.
Proof.
  intros lppo P.
  destruct (lppo (fun n => P)).
  right. apply H. apply 0.
  destruct H. now left.
Qed.

Close Scope N_scope.
Inductive even : nat -> Prop :=
| E0 : even 0
| ESS : forall n, even n -> even (S (S n)).

About even_ind.
Print even_ind.

Lemma evenind (P: nat -> Prop) : P 0 -> (forall n : nat, even n -> P n -> P (S (S n))) -> forall n : nat, even n -> P n.
Proof.
  intros P0 PI.
  fix 2; intro n.
  intro H. destruct H.
  assumption.
  apply PI. assumption. now apply evenind.
Qed.

Definition evs (n : nat) : Prop :=
  exists x, n = x + x.

Lemma evn_evs n:
  even n -> evs n.
Proof.
  induction 1 as [| n H IH].
  now exists 0.
  destruct IH as [x Hx].
  exists (S x). rewrite Hx. romega with *.
Qed.

Lemma evs_evn n:
  evs n -> even n.
Proof.
  revert n.
  fix F 1; intros.
  destruct H as [x H].
  destruct x as [| x].
  rewrite H. now apply E0.
  destruct n. romega with *.
  destruct n. romega with *.
  apply ESS. apply F.
  exists x. romega with *.
Qed.

Inductive list : Type :=
| nil : list
| cons : nat -> list -> list.

Fixpoint triple (n : nat) : Prop :=
  match n with
    | 0 => True
    | S 0 => False
    | S (S 0) => False
    | S (S (S n)) => triple n
  end.

Inductive Triple : nat -> Prop :=
| T0 : Triple 0
| TSSS : forall n, Triple n -> Triple (S (S (S (n)))).

Lemma T_t n:
  Triple n -> triple n.
Proof.
  induction 1; now simpl.
Qed.

Lemma t_T:
  forall n,
  triple n -> Triple n.
Proof.
  fix 1.
  intros n tn.
  destruct n. apply T0.
  destruct n. destruct tn.
  destruct n. destruct tn.
  apply TSSS. now apply t_T. 
Qed.

Fixpoint all_triple (l : list) : Prop :=
  match l with
  | nil => True
  | cons n l' => triple n /\ all_triple l'
  end.

Inductive All_triple : list -> Prop :=
| Anil : All_triple nil
| Acons : forall n l', Triple n -> All_triple l' -> All_triple (cons n l').

Lemma A_a l:
  All_triple l -> all_triple l.
Proof.
  induction 1 as [|n l' Tn _ IH]; simpl; trivial.
  split; trivial. now apply T_t.
Qed.

Lemma a_A l:
  all_triple l -> All_triple l.
Proof.
  intro al. induction l.
  -apply Anil.
  -destruct al as [tn an].
   apply Acons. now apply t_T.
   now apply IHl.
Qed.

Fixpoint contains n l : Prop :=
  match l with
  | nil => False
  | cons h t => n = h \/ contains n t
  end.

Inductive Contains : nat -> list -> Prop :=
| Cexact n l: Contains n (cons n l)
| Ccons n h t : Contains n t -> Contains n (cons h t).

Lemma C_c n l:
  Contains n l -> contains n l.
Proof.
  induction 1.
  -now left.
  -now right.
Qed.   
  
Lemma c_C n l:
  contains n l -> Contains n l.
Proof.
  induction l; intro; destruct H.
  rewrite H. apply Cexact.
  apply Ccons. now apply IHl.
Qed.

Fixpoint addChain (l : list) : Prop :=
  match l with
  | nil => False
  | cons h nil => match h with 1 => True | _ => False end
  | cons m l' => exists x, exists y,
        contains x l' /\ contains y l' /\ m = x + y /\ addChain l'
  end.


Inductive AddChain : list -> Prop :=
| Addstart : AddChain (cons 1 nil)
| Add_next x y l: contains x l -> contains y l -> AddChain l ->
                  AddChain (cons (x+y) l).

Lemma in_single x a:
  contains x (cons a nil) -> x = a.
Proof.
  simpl. intuition.
Qed.  

Lemma Add_add l:
  AddChain l -> addChain l.
Proof.
  induction 1 as [|x y l cx cy H IH]. reflexivity.
  inversion H.
  rewrite <- H0 in *.
  assert (Gx := in_single x 1 cx).
  assert (Gy := in_single y 1 cy).
  rewrite Gx, Gy in *. exists 1, 1. intuition.
  exists x, y. rewrite H3 in *. intuition.
Qed.

Lemma add_Add l:
  addChain l -> AddChain l.
Proof.
  revert l. fix 1; intro.
  destruct l; intros.
  destruct H. 
  destruct_with_eqn l. simpl in H. destruct n; try destruct H.
  destruct n; try destruct H. apply Addstart.
  destruct H as [x [y [cx [cy [eqn IH]]]]].
  rewrite <- Heql0 in *. (* so that it accepts fix *)
  apply add_Add in IH. rewrite eqn. apply Add_next; trivial.
Qed.  
  
  
  

  
