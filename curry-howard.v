(* In Coq, propositions are of type Prop, which means they are types. *)
(* Data-types are of type Type or Set, which means they are also types  *)
(* The differences between Prop, Set and Type will be made clear later *)


(* ex 1 *)

Definition easy : forall P : Prop, P -> P :=
  fun P : Prop => fun u : P => u.

Print easy.

(* In Coq, -> is just a particular case of forall *)
Check forall n : nat, True.

(* Minimal logic *)
Parameter A B C : Prop.

(* Prove *)
Definition triv : A -> A :=
 fun u => u.

Definition trans : (A -> B) -> (B -> C) -> A -> C :=
  fun f : A -> B => fun g : B -> C => fun a : A => g (f a).

Definition K : A -> B -> A :=
  fun a b => a.

Definition S': (A -> B -> C) -> (A -> B) -> A -> C :=
  fun f g a => f a (g a).

(* Negation : remember ~A is an abrevation for A -> False *)
(* Prove the following, possibly using False_ind *)
Print False_ind.
Print False_rect.

Definition impl_neg_neg : A -> ~~A :=
  fun a nega => nega a.

Definition contra : (A -> B) -> (~B -> ~A) :=
  fun fab negb a => negb (fab a).

Definition presque_classic : ~~(~~A -> A) :=
  fun neg =>
    neg (fun nna => False_ind A (nna ( fun a => neg ( fun negnega => a)))).


(* forall quantification *)
Definition split_forall: forall P Q : Type -> Type,
    (forall x, P x -> Q x) -> (forall x, P x) -> (forall x, Q x) :=
  fun p q forpiq forp x => forpiq x (forp x).

Definition trans_forall : forall P Q R : Type -> Prop,
  (forall x, P x -> Q x) -> (forall x, Q x -> R x) -> (forall x, P x -> R x) :=
  fun P Q R forpiq forqir x Px => forqir x (forpiq x Px) .



Definition iter : forall (P : Type -> Prop) (f : Type -> Type),
    (forall x , P x -> P (f x)) -> (forall x, P x -> P (f(f x))) :=
      fun P f forpipf x Px => forpipf (f x) (forpipf x Px).

Definition contra_ex : forall (P Q : Type -> Prop) (c: Type),
    (forall x, P x -> Q x) -> ~Q c -> ~(forall x, P x) :=
  fun P Q c forpiq nqc forp => nqc ( forpiq c (forp c)) .

(* existantial quantification *)

Print ex_intro.

Check ex_intro.

Definition al_ex : forall A : Type, forall P : A -> Prop,
      A -> (forall x, P x) -> (exists x, P x) :=
  fun A P a forp => ex_intro P a (forp a).


Definition ex_al : forall A : Type, forall P : A -> Prop,
      ~(exists x, P x) -> forall x, ~(P x) :=
  fun A P nexp x Px => nexp ( ex_intro P x Px) .
  

(* Induction  / recursion *)

Definition half x y :=  x=y+y \/ x = S (y+y).


Definition d (x:nat) := exists y,half x y.

(* advanced : do the following without tactics ! *)
(* for now, just use it *)


Lemma dS : forall x, d x -> d(S x).

Proof.
  intros.
  unfold d in H.
  unfold d.
  Check ex_ind.
  apply ex_ind with nat (half x).
  intros.


  apply or_ind with (x = x0 + x0) (x = S (x0 + x0)).

  unfold half.
  intro.
  exists x0.
  right.
  rewrite H1.
  reflexivity.

  intro.
  exists (S x0).
  left.
  rewrite plus_n_Sm in H1.
  rewrite H1.
  reflexivity.
  assumption.

  assumption.
Qed.

Check eq_trans.
Check plus_n_Sm.
Check or_ind.
Check f_equal.
Check ex_ind.
Definition d_of_S : forall x, d x -> d (S x) :=
  fun x => @ex_ind nat (half x) _ 
                   (fun x0 h_x_x0 =>                      
                         or_ind 
                                (fun x_is_x0_plus_x0 =>
                                   ex_intro (half (S x)) x0
                                            (or_intror (f_equal S x_is_x0_plus_x0)))

                                (fun x_is_S_x0_plus_x0 =>
                                   ex_intro (half (S x)) (S x0)
                                            (or_introl
                                               (
                                                 (f_equal S (eq_trans x_is_S_x0_plus_x0 (plus_n_Sm x0 x0)))

                                               )))
                                h_x_x0
                      ).


Definition d0 : (d 0) :=
  ex_intro (half 0) 0 (or_introl (plus_O_n 0)).

  (* Use nat_ind for the following *)
Definition div2 (x:nat) : (d x) :=
  nat_ind d d0 dS x.


Eval compute in (div2 3).

Check I.

(* Try to understand the following *)
Check ex_ind.

Definition divide (x:nat) : exists y:nat, True :=
  @ex_ind nat (half x) (exists y:nat, True)
          (fun x Px => (ex_intro _ x I)) (div2 x).

Eval compute in (divide 251).




