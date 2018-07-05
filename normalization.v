(* -------------------------------------------------------------------- *)
Require Import Arith List.

(* -------------------------------------------------------------------- *)
(* We are going to formalize a proof of the strong normalization of the *
 * simply lambda calculus (STLC). The lambda terms will be represented  *
 * using De Bruijn indices. We will rely on the autosubst library to    *
 * handle these indices and to have for free basic results.             *)

(* Autosubst can be downloaded from:                                    *
 *    https://github.com/uds-psl/autosubst                              *
 *                                                                      *
 * If you are using Coq 8.6, you need to download this version:         *
 *    https://github.com/uds-psl/autosubst/tree/coq86-devel             *
 *                                                                      *
 * Once downloaded, running "make && make install" should do the trick. *)

(* -------------------------------------------------------------------- *)
From Autosubst Require Import Autosubst.

(* -------------------------------------------------------------------- *)
(* We define below the type of the pure lambda terms. The type [var] is *
 * an alias for [nat]. The notation {bind T} is an alias for [T].       *
 * These aliases tell autosubst with constructors represent variables   *
 * and which constructors bind variables.                               *)

Inductive term : Type :=
| Var (_ : var)
| App (_ : term) (_ : term)
| Lam (_ : {bind term}).

(* -------------------------------------------------------------------- *)
(* These magic commands bind the autosubst library to our term algebra. *
 * From there, you have the following notations                         *
 *                                                                      *
 * t.[xi]    : the result of applying the substitution [xi] to [t],     *
 *             where [xi : var -> term]                                 *
 * t.[v/]    : the result of substituting [0] by [v] in [t]             *
 * a .: xi   : the substitution that maps [0] to [a] and [S n]          *
 *             to [xi n]                                                *
 * (+n)      : the renaming that maps [p] to [p+n]                      *
 * ren rn    : the substitution obtained from the renaming [rn]         *
 * xi >>> sg : the substitution composition ( := sg o xi )              *
 * up xi     : the substitution [xi] lifted := Var 0 .: (xi >>> (+1))   *)
 
Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.



(* -------------------------------------------------------------------- *)
(* Autosubst comes with extra tactics:                                  *
 * - [asimpl], simplifies expressions containing substitutions          *
 * - [ainv], that performs inversion, on all hypothesis, where this     *
 *   produces no more than one subgoal.                                 *)

(* You can find more information in the autosubst documentation         *
 *     https://www.ps.uni-saarland.de/autosubst/doc/manual.pdf          *)

(* -------------------------------------------------------------------- *)
(* We define below the inductive type for the beta-reduction relation   *)
Inductive step : term -> term -> Prop :=
| Step_beta (s1 s2 t : term) :
    s1.[t/] = s2 -> step (App (Lam s1) t) s2

| Step_appL (s1 s2 t : term) :
    step s1 s2 -> step (App s1 t) (App s2 t)

| Step_appR (s t1 t2 : term) :
    step t1 t2 -> step (App s t1) (App s t2)

| Step_lam (s1 s2 : term) :
    step s1 s2 -> step (Lam s1) (Lam s2).

Notation red := (fun s t => step t s).

Hint Constructors step : rewr.
(* -------------------------------------------------------------------- *)
(* We start by proving that [beta] reduction is stable under            *
 * substitution.                                                        *)
Lemma step_subst t u xi : step t u -> step t.[xi] u.[xi].
Proof.
  intro.
  revert xi.
  induction H; 
    intro;[apply Step_beta; rewrite <- H | | |];
    asimpl;
    eauto with rewr.
Qed.
(* -------------------------------------------------------------------- *)
(* STLC only has two types : a basic type and the arrow type.           *)
Inductive type := Base | Arr (_ : type) (_ : type).

(* -------------------------------------------------------------------- *)
(* We define now the STLC typing relation.                              *)
Inductive ty (G : var -> type) : term -> type -> Prop :=
| Ty_Var x A :
    G x = A -> ty G (Var x) A

| Ty_Lam s A B :
    ty (A .: G) s B -> ty G (Lam s) (Arr A B)

| Ty_App s t A B :
    ty G s (Arr A B) -> ty G t A -> ty G (App s t) B.

Hint Constructors ty : ty.

(* -------------------------------------------------------------------- *)
(* We now prove one key property of STLC: its subject reduction.        *)
Lemma ty_ren G s A D xi : ty G s A -> G = xi >>> D -> ty D s.[ren xi] A.
Proof.
  intro.
  revert xi.
  revert D.
  induction H; intros.

  -asimpl.
   apply Ty_Var.
   rewrite <- H.
   rewrite H0.
   now simpl.

  -apply Ty_Lam.
   asimpl.
   apply IHty.
   rewrite H0.
   now asimpl.

  -apply Ty_App with A.
   apply IHty1.
   assumption.
   apply IHty2.
   assumption.
Qed.


Lemma ty_subst G s A subst D :
  ty G s A
  -> (forall x, ty D (subst x) (G x))
  -> ty D s.[subst] A.

Proof.
  intros.
  revert H0.
  revert D.
  revert subst.
  induction H; intros.


  -asimpl.
   rewrite <- H.
   apply H0.

  -apply Ty_Lam.
   apply IHty.
   intro.
   destruct x eqn:?.
   apply Ty_Var.
   now asimpl.
   asimpl.
   apply ty_ren with D.
   apply H0.
   now asimpl.

  -apply Ty_App with A.
   now apply IHty1.
   now apply IHty2.
Qed.

Lemma ty_pres G s A s' : ty G s A -> step s s' -> ty G s' A.

Proof. 
  intros.
  revert H.
  revert A.
  revert G.
  induction H0; intros; ainv.

  - apply ty_subst with (A0 .: G).
    assumption.
    intro.
    destruct x eqn:?.
    now asimpl.
    asimpl.
    now apply Ty_Var.

  - apply Ty_App with A0.
    now apply IHstep.
    assumption.

  - apply Ty_App with A0.
    assumption.
    now apply IHstep.

  - apply Ty_Lam.
    now apply IHstep.
Qed.    
    
(* -------------------------------------------------------------------- *)
(* We now define the notion to be SN using the accessibility predicate  *)
Notation SN := (Acc red).

Print Acc.
(* -------------------------------------------------------------------- *)
Definition allSN (ts : list term) :=
  forall t, In t ts -> SN t.

(* -------------------------------------------------------------------- *)
(* Variables are SN.                                                    *)
Lemma SN_var n : SN (Var n).

Proof. 
  apply Acc_intro.
  intros.
  ainv.
Qed.  

(* -------------------------------------------------------------------- *)
(* As a first result, we show that if a term has all its reduces SN,    *
 * then it is SN.                                                       *)
Lemma SN_stepI t : (forall u, step t u -> SN u) -> SN t.

Proof.
  intro.
  now apply Acc_intro.
Qed.  

(* -------------------------------------------------------------------- *)
(* Conversely, all the reduces of an SN term are SN.                    *)
Lemma SN_step t u : step t u -> SN t -> SN u.

Proof. 
  intros.
  now apply H0.
Qed.  
  
(* -------------------------------------------------------------------- *)
Inductive subterm : term -> term -> Prop :=
| SubTop t :
    subterm t t

| SubAppL t1 t2 u :
    subterm t1 u -> subterm (App t1 t2) u

| SubAppR t1 t2 u :
    subterm t2 u -> subterm (App t1 t2) u

| SubLam t u :
    subterm t u -> subterm (Lam t) u.


  
(* -------------------------------------------------------------------- *)
(* All subterms of a SN term are SN.                                    *)
Lemma step_subterm t u u' :
    subterm t u -> step u u' -> exists t', step t t' /\ subterm t' u'.

Proof.
  intros.
  induction H.
  
  exists u'.
  intuition.
  apply SubTop.
  
  destruct IHsubterm.
  assumption.
  exists (App x t2).
  destruct H1.
  split.
  now apply Step_appL.
  now apply SubAppL.

  destruct IHsubterm.
  assumption.
  destruct H1.
  exists (App t1 x).
  split.
  now apply Step_appR.
  now apply SubAppR.

  destruct IHsubterm.
  assumption.
  destruct H1.
  exists (Lam x).
  split.
  now apply Step_lam.
  now apply SubLam.
Qed.


Lemma SN_subterm t u : subterm t u -> SN t -> SN u.

Proof.
  intros.
  revert H.
  revert u.
  induction H0.

  intros.
  apply Acc_intro.
  intros.
  destruct (step_subterm x u y).
  assumption.
  assumption.
  apply H0 with x0;
  intuition.
Qed.  
  
Corollary SN_appIL t u : SN (App t u) -> SN t.

Proof.
  apply SN_subterm.
  apply SubAppL.
  apply SubTop.
Qed.  


Lemma SN_appIR t u : SN (App t u) -> SN u.

Proof. 
  apply SN_subterm.
  apply SubAppR.
  apply SubTop.
Qed.  

Lemma SN_lamI t : SN (Lam t) -> SN t.

Proof.
  apply SN_subterm.
  apply SubLam.
  apply SubTop.
Qed.  

(* -------------------------------------------------------------------- *)
(* We now prove the contraposite of the previous lemmas. Note that for  *
 * the [App] case, we need some extra conditions.                       *)

Definition neutral (t : term) :=
  match t with Lam _ => false | _ => true end.

Lemma SN_lam u : SN u -> SN (Lam u).

Proof.
  intro.
  induction H.

  apply Acc_intro.
  intros.
  inversion H1.
  apply H0.
  assumption.
Qed.  
  
Lemma SN_app t u : neutral t = true -> SN t -> SN u -> SN (App t u).

Proof. 
  intros.
  induction H0.
  
  apply Acc_intro.
  intros.
  inversion H3.
  rewrite <- H4 in H.
  simpl in H.
  discriminate H.

  rewrite <- H5 in H3.
  apply H2.
  assumption.
  

  
Lemma SN_apps t us :
  neutral t = true -> SN t -> allSN us -> SN (fold_left App us t).
Proof. (* ... *) Abort.

(* -------------------------------------------------------------------- *)
(* We now start the proof of strong normalization. We start by          *
 * an interpretation of [type] in terms of sets of terms.               *)

Fixpoint CR (ty : type) :=
  match ty with
  | Base => fun t => SN t
  | Arr ty1 ty2 => fun t => forall u, CR ty1 u -> CR ty2 (App t u)
  end.

(* -------------------------------------------------------------------- *)
(* We first show, by induction on [ty], that [CR] is included in [SN],  *
 * and that a term of the form [x u1 ... un], where the [ui] are SN, is *
 * in CR.                                                               *)

Lemma CR_SN_r ty :
  (forall t, CR ty t -> SN t)
  /\ (forall n ts, allSN ts -> CR ty (fold_left App ts (Var n))).
Proof. (* ... *) Abort.

Corollary CR_SN ty t : CR ty t -> SN t.
Proof. (* ... *) Abort.

Corollary CR_var ty n : CR ty (Var n).
Proof. (* ... *) Abort.

(* -------------------------------------------------------------------- *)
(* Second, we show two key properties of [CR] :                         *
 *   - its stability w.r.t. beta-reduction                              *
 *   - its inverse stability w.r.t beta-reduction (that is if a term    *
 *     has all its reduces in [CR A], then it is in [CR A].             *)
Lemma CR_step_r ty :
  (forall t u, step t u -> CR ty t -> CR ty u)
  /\ (forall t, neutral t = true -> (forall u, step t u -> CR ty u) -> CR ty t).
Proof. (* ... *) Abort.

Corollary CR_step ty t u : step t u -> CR ty t -> CR ty u.
Proof. (* ... *) Abort.


Corollary CR_stepI ty t :
  neutral t = true -> (forall u, step t u -> CR ty u) -> CR ty t.
Proof. (* ... *) Abort.

(* -------------------------------------------------------------------- *)
(* Finally, we prove that, for any well-formed subsitution [xi] under   *
 * [G], if [G |- t : A], then [t.[xi]] is in [CR A].                    *)
Lemma ty_CR G t A xi :
  (forall x, CR (G x) (xi x)) -> ty G t A -> CR A (t.[xi]).
Proof. (* .... *) Abort.

(* -------------------------------------------------------------------- *)
(* We can conclude that well-formed terms of STLC are SN.               *)
Theorem ty_SN G t A : ty G t A -> SN t.
  Proof. (* ... *) Abort.