(* -------------------------------------------------------------------- *)
Require Import Bool Arith List.

Local Notation "~~ b" := (negb b) (at level 2).
Local Notation "b1 == b2" := (eqb b1 b2) (at level 70).

(* -------------------------------------------------------------------- *)
(* On s'intéresse dans cet exercice à la logique propositionnelle.      *
 *                                                                      *
 * Nous allons démontrer 2 théorèmes :                                  *
 * - la correction de la déduction naturelle en logique                 *
 *   propositionnelle                                                   *
 * - la décidabilité de la validité universelle d'une assertion en      *
 *   logique propositionnelle via l'implémentation d'un algorithme      *
 *   de normalisation des assertions.                                   *)

(* ==================================================================== *)
(* Le type suivant décrit la syntaxe des assertions. Les constructeurs  *
 * pour le True, la négation et l'équivalence ne sont pas primitifs,    *
 * mais exprimés en fonction des autres constructeurs de la logique.    *)

Inductive assn : Type :=
| PVar (_ : nat)                (* Variable propositionnelle *)
| PFalse                        (* Faux *)
| PAnd (_ : assn) (_ : assn)    (* Conjonction *)
| POr  (_ : assn) (_ : assn)    (* Disjonction *)
| PImp (_ : assn) (_ : assn).   (* Implication *)

Notation PTrue    := (PImp PFalse PFalse).
Notation PNot p   := (PImp p PFalse).
Notation PIff p q := (PAnd (PImp p q) (PImp q p)).

(* -------------------------------------------------------------------- *)
(* Une valuation est simplement une fonction qui affecte à chaque       *
 * variable propositionnelle une valeur de vérité.                      *)

Notation valuation := (nat -> bool) (only parsing).

(* -------------------------------------------------------------------- *)
(* Définissez la fonction suivante qui, à partir d'une valuation,       *
 * calcule la sémantique (dans bool) d'une assertion.                   *)
Fixpoint sem (v : valuation) (p : assn) : bool :=
  match p with
  | PVar n => v n
  | PFalse => false
  | PAnd a b => andb (sem v a) (sem v b)
  | POr a b => orb (sem v a) (sem v b)
  | PImp a b => orb (negb (sem v a)) (sem v b)
  end.

(* -------------------------------------------------------------------- *)
(* Nous définissons les notions d'être satisfiable sous une valuation   *
 * et d'être universellement valide pour une assertion.                 *)
Definition sat (v : valuation) (p : assn) :=
  sem v p = true.

Definition valid (p : assn) :=
  forall v, sat v p.

(* -------------------------------------------------------------------- *)
(* Le prédicat inductif ci-dessous définit la notion de dérivabilité    *
 * en déduction naturelle. Ce prédicat prend deux arguments             *
 *                                                                      *
 * - une liste d'assertions qui représente le contexte de preuve,       *
 * - l'assertion que l'on veut prouver sous ce contexte.                *
 *)


Inductive dn : list assn -> assn -> Prop :=
(* Non-structural rules *)
| Ax env p :
    In p env -> dn env p

| Absurd env p :
    dn (PNot p :: env) PFalse -> dn env p

(* Introduction rules *)

| AndI   env p q : dn env p -> dn env q -> dn env (PAnd p q)
| OrIL   env p q : dn env p -> dn env (POr p q)
| OrIR   env p q : dn env q -> dn env (POr p q)
| ImpI   env p q : dn (p :: env) q -> dn env (PImp p q)

(* Elimination rules *)

| FalseE env p     : dn env PFalse -> dn env p
| AndEL  env p q   : dn env (PAnd p q) -> dn env p
| AndER  env p q   : dn env (PAnd p q) -> dn env q
| OrE    env p q r : dn env (POr p q) -> dn (p :: env) r -> dn (q :: env) r -> dn env r
| ImpE   env p q   : dn env p -> dn env (PImp p q) -> dn env q
.

(* -------------------------------------------------------------------- *)
(* On va commencer par prouver que le prédicat [dn] est invariant par   *
 * affaiblissement ou permutation du contexte de preuve. La définition  *
 * ci-dessous définit une relation d'ordre sur les contextes de preuve. *)
Definition subenv (e1 e2 : list assn) :=
  forall q, In q e1 -> In q e2.

(* -------------------------------------------------------------------- *)
(* Montrer que [dn] est un prédicat monotone pour [subenv].             *)
Lemma subenv_dn (e1 e2 : list assn) (p : assn) :
  subenv e1 e2 -> dn e1 p -> dn e2 p.
Proof.
  intros.
  revert H.
  revert e2.

  induction H0.

  - intros.
    apply Ax.
    apply H0.
    assumption.

  - intros.
    apply Absurd.
    apply IHdn.
    intro.
    intro.
    simpl.
    simpl in H1.
    intuition.

  - intros.
    apply AndI.
    apply IHdn1.
    assumption.
    apply IHdn2.
    assumption.

  - intros.
    apply OrIL.
    apply IHdn.
    assumption.

  - intros.
    apply OrIR.
    apply IHdn.
    assumption.

  - intros.
    apply ImpI.
    apply IHdn.
    intro.
    intros.
    simpl.
    simpl in H1.
    intuition.

  - intros.
    apply FalseE.
    now apply IHdn.

  - intros.
    apply AndEL with q.
    apply IHdn.
    assumption.

  - intros.
    apply AndER with p.
    apply IHdn.
    assumption.

  - intros.
    apply (OrE e2 p q r).
    apply IHdn1.
    assumption.
    apply IHdn2.
    intro.
    intro.
    simpl.
    simpl in H0.
    intuition.
    apply IHdn3.
    intro.
    intro.
    simpl.
    simpl in H0.
    intuition.

  - intros.
    apply ImpE with p.
    apply IHdn1.
    assumption.
    apply IHdn2.
    assumption.
Qed.

(* -------------------------------------------------------------------- *)
(* On s'intéresse maintenant à la correction de [dn]. Montrer le lemme  *
 * suivant, par induction sur [dn env p].                               *)
Lemma correctness (env : list assn) (p : assn) :
  dn env p -> forall v, (forall q, In q env -> sat v q) -> sat v p.

Proof.
  induction 1; intros; unfold sat; simpl.

  - now apply H0.

  - destruct (sem v p) eqn:?.
    reflexivity.
    assert (sat v PFalse).
    apply IHdn.
    intros.
    destruct H1.
    rewrite <- H1.
    unfold sat.
    simpl.
    replace (~~ (sem v p) || false) with (false || ~~(sem v p)).
    simpl.
    apply negb_true_iff.
    assumption.
    destruct (~~ (sem v p)); simpl; reflexivity.
    apply H0.
    assumption.
    unfold sat in H1.
    simpl in H1.
    discriminate H1.

  - rewrite IHdn1.
    rewrite IHdn2.
    simpl.
    reflexivity.
    assumption.
    assumption.

  - rewrite IHdn.
    simpl.
    reflexivity.
    intros.
    now apply H0.

  - rewrite IHdn.
    destruct (sem v p); simpl; reflexivity.
    assumption.

  - destruct (sem v p) eqn:?.
    simpl.
    apply IHdn.
    intros.
    destruct H1.
    rewrite <- H1.
    assumption.
    apply H0.
    assumption.
    simpl.
    reflexivity.

  - assert (sat v PFalse).
    apply IHdn.
    assumption.
    unfold sat in H1.
    simpl in H1.
    discriminate H1.

  - assert (sat v (PAnd p q)).
    apply IHdn.
    assumption.
    unfold sat in H1.
    simpl in H1.
    destruct (sem v p) eqn:?.
    reflexivity.
    simpl in H1.
    assumption.

  - assert (sat v (PAnd p q)).
    apply IHdn.
    assumption.
    unfold sat in H1.
    simpl in H1.
    destruct (sem v q) eqn:?.
    reflexivity.
    destruct (sem v p).
    simpl in H1.
    discriminate H1.
    simpl in H1.
    discriminate H1.

  - assert (sat v (POr p q)).
    apply IHdn1.
    assumption.
    unfold sat in H3.
    simpl in H3.
    destruct (sem v p) eqn:?.
    apply IHdn2.
    intros.
    destruct H4.
    rewrite <- H4.
    assumption.
    apply H2.
    assumption.
    destruct (sem v q) eqn:?.
    apply IHdn3.
    intros.
    destruct H4.
    rewrite <- H4.
    assumption.
    apply H2.
    assumption.
    simpl in H3.
    discriminate H3.

  - unfold sat in *.
    simpl in *.
    assert (~~ (sem v p) || sem v q = true).
    apply IHdn2.
    assumption.
    replace (sem v p) with true in H2.
    simpl in H2.
    assumption.
    symmetry.
    apply IHdn1.
    assumption.
Qed.

(* ==================================================================== *)
(* We are now interested in deciding if a given assertion is            *
 * universally valid or not. For that, we first normalize the           * 
 * assertions, obtaining an expression built from boolean constants,    *
 * propositionnal variables and if-then-else statements whose           *
 * condition is a propositional variables.                              *)

(* -------------------------------------------------------------------- *)
(* We start by defining an intermediate datatype that describe the      *
 * syntax of normalized assertions, except for the side conditions      *
 * of the if-then-else expressions that are still unconstrained.        *)

Inductive ifassn : Type :=
| PIVar   (_ : nat)                  (* variable propositionnelle *)
| PIConst (_ : bool)                 (* constante true / false *)
| PIIf    (_ : ifassn) (_ : ifassn) (_ : ifassn). (* if-then-else *)

(* -------------------------------------------------------------------- *)
(* Define the semantic of the assertions of type [ifassn].              *)

Fixpoint ifsem (v : valuation) (p : ifassn) : bool :=
  match p with
  | PIVar n => v n
  | PIConst b => b
  | PIIf cond a1 a2 => if ifsem v cond
                       then ifsem v a1
                       else ifsem v a2
  end.

(* -------------------------------------------------------------------- *)
(* Write the normalization functions from assertions of type [assn] to  *
 * assertions of type [ifassn].                                         *)

Fixpoint ifassn_of_assn (p : assn) :=
  match p with
  | PVar n => PIVar n
  | PFalse => PIConst false
  | PAnd a1 a2 => PIIf (ifassn_of_assn a1) (ifassn_of_assn a2) (PIConst false)
  | POr  a1 a2 => PIIf (ifassn_of_assn a1) (PIConst true) (ifassn_of_assn a2) 
  | PImp a1 a2 => PIIf (ifassn_of_assn a1) (ifassn_of_assn a2) (PIConst true)
  end.

(* -------------------------------------------------------------------- *)
(* Show that your normalization function is correct w.r.t. [ifsem].     *)

Lemma ifassn_correct (v : valuation) (p : assn) :
  sem v p = ifsem v (ifassn_of_assn p).

Proof.
  induction p; simpl; [reflexivity|reflexivity| | |];
    rewrite <- IHp1;
    rewrite <- IHp2;
    destruct (sem v p1);
    simpl;
    reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* We now define the syntax of normalized assertions. We see that the   *
 * conditions of the if-then-else expressions are now enforced to be    *
 * propositional variables.                                             *)

Inductive nifassn : Type :=
| PNIVar   (_ : nat)
| PNIConst (_ : bool)
| PNIIf    (_ : nat) (_ : nifassn) (_ : nifassn).

(* -------------------------------------------------------------------- *)
(* Define the semantic of the assertions of type [nifassn].             *)

Fixpoint nifsem (v : valuation) (p : nifassn) : bool :=
  match p with
  | PNIVar n => v n
  | PNIConst b => b
  | PNIIf n a1 a2 => if v n
                     then nifsem v a1
                     else nifsem v a2
  end.

(* -------------------------------------------------------------------- *)
(* We define below the normalization function for assertions of type    *
 * [ifassn], obtaining assertions of type [nifassn].                    *)

Fixpoint normif (c t f : nifassn) {struct c} :=
  match c with
  | PNIVar   x        => PNIIf x t f
  | PNIConst true     => t
  | PNIConst false    => f
  | PNIIf    c' t' f' => PNIIf c' (normif t' t f) (normif f' t f)
  end.

Fixpoint norm (p : ifassn) : nifassn :=
  match p with
  | PIVar   x     => PNIVar x
  | PIConst b     => PNIConst b
  | PIIf    c t f => normif (norm c) (norm t) (norm f)
  end.

(* -------------------------------------------------------------------- *)
(* Show that the normalization functions are correct w.r.t. [nifsem].   *)

Lemma normif_correct (v : valuation) (c t f : nifassn) :
  nifsem v (normif c t f) = if nifsem v c then nifsem v t else nifsem v f.

Proof.
  induction c; simpl.

  - reflexivity.

  - destruct b;
    reflexivity.

  - destruct (v n);
    assumption.
Qed.

(* -------------------------------------------------------------------- *)
Lemma norm_correct (v : valuation) (p : ifassn) : nifsem v (norm p) = ifsem v p.

Proof.
  induction p; simpl.

  - reflexivity.

  - reflexivity.

  - rewrite <- IHp1.
    rewrite <- IHp2.
    rewrite <- IHp3.
    apply normif_correct.
Qed.

(* -------------------------------------------------------------------- *)
(* Finally, we provide a procedure that decides if a normalized         *
 * assertion is universally valid w.r.t. [nifasm].                      *)

Definition xt (v : nat -> option bool) (x : nat) (b : bool) :=
  fun y => if beq_nat x y then Some b else v y.


Fixpoint nifassn_tauto_r (v : nat -> option bool) (p : nifassn) :=
  match p with
  | PNIVar   x => match v x with Some true => true | _ => false end
  | PNIConst b => b

  | PNIIf x t f =>
    match v x with
    | Some true  => nifassn_tauto_r v t
    | Some false => nifassn_tauto_r v f
    | None       =>
      nifassn_tauto_r (xt v x true) t
                      && nifassn_tauto_r (xt v x false) f
    end
  end.

Definition nifassn_tauto p := nifassn_tauto_r (fun _ => None) p.

(* -------------------------------------------------------------------- *)
(* Show the correctness of the procedure...                             *)

Lemma nifassn_tauto_r_correct (xv : nat -> option bool) (p : nifassn) :
  nifassn_tauto_r xv p = true
  -> forall v, (forall x b, xv x = Some b -> v x = b)
               -> nifsem v p = true.
Proof.
  revert xv.
  induction p; intros; simpl; simpl in H.

  - destruct (xv n) eqn:?.
    destruct b eqn:?.
    apply H0.
    assumption.
    discriminate H.
    discriminate H.

  - assumption.

  - destruct (xv n) eqn:?.

    {destruct b eqn:?.

     assert (v n = true).
     apply H0.
     assumption.
     rewrite H1.
     apply IHp1 with xv.
     assumption.
     assumption.

     assert (v n = false).
     apply H0.
     assumption.
     rewrite H1.
     apply IHp2 with xv.
     assumption.
     assumption.
     }

    {destruct (nifassn_tauto_r (xt xv n true) p1) eqn:?.
     simpl in H.
     destruct (v n) eqn:?.
     apply IHp1 with (xt xv n true).
     assumption.
     intros.
     unfold xt in H1.
     destruct (beq_nat n x) eqn:?.
     destruct b.
     apply beq_nat_true_iff in Heqb1.
     rewrite <- Heqb1.
     assumption.
     discriminate H1.
     apply H0.
     assumption.
     
     apply IHp2 with (xt xv n false).
     assumption.
     intros.
     unfold xt in H1.
     destruct (beq_nat n x) eqn:?.
     destruct b.
     discriminate H1.
     apply beq_nat_true_iff in Heqb1.
     rewrite <- Heqb1.
     assumption.
     apply H0.
     assumption.

     simpl in H.
     discriminate H.
     }
Qed.

(* -------------------------------------------------------------------- *)
Lemma nifassn_tauto_correct (p : nifassn) :
  nifassn_tauto p = true -> forall v, nifsem v p = true.

Proof.
  intros.
  unfold nifassn_tauto in *.
  apply nifassn_tauto_r_correct with (fun _ => None).
  assumption.
  intros.
  discriminate H0.
Qed.

(* -------------------------------------------------------------------- *)
(* ...and its completness.                                              *)

Definition extend (xv : nat -> option bool) (n : nat) :=
  match xv n with
  | Some true => true
  | Some false => false
  | None => false
  end.


Lemma extend_extends xv:
      forall (x : nat) (b0 : bool), xv x = Some b0 -> extend xv x = b0.

Proof.
  intros.
  unfold extend.

  destruct b0;
  destruct (xv x) eqn:?.
           destruct b.
           reflexivity.
           discriminate H.
           discriminate H.
           destruct b.
           discriminate H.
           reflexivity.
           reflexivity.
Qed.           

Lemma nifassn_tauto_r_complete (xv : nat -> option bool) (p : nifassn) :
  nifassn_tauto_r xv p = false
  -> exists v, (forall x b, xv x = Some b -> v x = b) /\ nifsem v p = false.

Proof.
  revert xv.
  induction p;
    intros;
    simpl;
    simpl in H.

  - exists (extend xv).
    split.
    apply extend_extends.
    assumption.

  - exists (extend xv).
    split.
    apply extend_extends.
    assumption.

  - destruct (xv n) eqn:?.
    destruct b eqn:?.
    destruct (IHp1 xv).
    assumption.
    exists x.
    destruct H0.
    split.
    assumption.
    assert (x n = true).
    apply H0.
    assumption.
    rewrite H2.
    assumption.

    destruct (IHp2 xv).
    assumption.
    destruct H0.
    exists x.
    split.
    assumption.
    assert (x n = false).
    apply H0.
    assumption.
    rewrite H2.
    assumption.

    destruct  (nifassn_tauto_r (xt xv n true) p1) eqn:?.
    simpl in H.
    destruct (IHp2 (xt xv n false)).
    assumption.
    destruct H0.
    exists x.
    split.
    intros.
    apply H0.
    destruct (beq_nat n x0) eqn:?.
    apply beq_nat_true_iff in Heqb0.
    rewrite <- Heqb0 in H2.
    rewrite Heqo in H2.
    discriminate H2.
    unfold xt.
    rewrite Heqb0.
    assumption.
    assert (x n = false).
    apply H0.
    assert (beq_nat n n = true).
    apply beq_nat_true_iff.
    reflexivity.
    unfold xt.
    rewrite H2.
    reflexivity.
    rewrite H2.
    assumption.

    destruct (IHp1 (xt xv n true)).
    assumption.
    destruct H0.
    exists x.
    split.
    intros.
    apply H0.
    destruct (beq_nat n x0) eqn:?.
    apply beq_nat_true_iff in Heqb0.
    rewrite Heqb0 in Heqo.
    rewrite Heqo in H2.
    discriminate H2.
    unfold xt.
    rewrite Heqb0.
    assumption.

    assert (x n = true).
    apply H0.
    assert (beq_nat n n = true).
    apply beq_nat_true_iff.
    reflexivity.
    unfold xt.
    rewrite H2.
    reflexivity.
    rewrite H2.
    assumption.
Qed.

(* -------------------------------------------------------------------- *)
Lemma nifassn_tauto_complete (p : nifassn) :
  nifassn_tauto p = false -> exists v, nifsem v p = false.

Proof.
  intros.
  destruct (nifassn_tauto_r_complete (fun _ => None) p).
  assumption.
  exists x.
  intuition.
Qed.

(* -------------------------------------------------------------------- *)
(* From this, define a decision procedure for the universal validity    *
 * and non-normalized assertions.                                       *)

Definition is_tautology (p : assn) : bool :=
  nifassn_tauto (norm (ifassn_of_assn p)).

(* -------------------------------------------------------------------- *)
(* Show the correctness of the procedure...                             *)

Lemma is_tautology_correct (p : assn) : is_tautology p = true -> valid p.
Proof.
  unfold valid.
  unfold sat.
  intros.
  rewrite ifassn_correct.
  unfold is_tautology in H.
  rewrite <- norm_correct.
  apply nifassn_tauto_correct.
  assumption.
Qed.

(* -------------------------------------------------------------------- *)
(* ...and its completness.                                              *)

Lemma is_tautology_complete (p : assn) :
  is_tautology p = false -> exists v, sem v p = false.


Proof.
  unfold valid.
  unfold sat.
  intros.
  destruct (nifassn_tauto_complete) with (norm (ifassn_of_assn p)).
  assumption.
  exists x.
  rewrite ifassn_correct.
  rewrite <- norm_correct.
  assumption.
Qed.
