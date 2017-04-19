Set Implicit Arguments.


Inductive color : Type :=
| Bl
| Wh.



Definition inv_color (c : color) : color :=
  match c with
  | Wh => Bl
  | Bl => Wh
  end.


Section Triple.

  Variable X : Type.

  Inductive pos : Type := | A | B | C.

  Definition triple : Type := (X * X * X)%type.

  Definition triple_x (x : X) : triple :=
    (x, x, x).

  Definition triple_map (f : X-> X) ( x : triple) : triple :=
    match x with
    | (a, b, c) => (f a, f b, f c)
    end.



  Definition triple_proj (p : pos) (x : triple) : X :=
    match x with
    | (a, b, c) => match p with
                   | A => a
                   | B => b
                   | C => c
                   end
    end.

  Definition triple_map_select (f : X -> X) (p : pos) (x : triple)
    : X :=
    f (triple_proj p x).

  Definition triple_map_on (f : X -> X) (p : pos) (x : triple)
    : triple :=
    match x with
    |(a, b, c) => match p with
                  | A => (f a, b, c)
                  | B => (a, f b, c)
                  | C => (a, b, f c)
                  end
    end.
End Triple.

Definition board : Type := (triple color * triple color * triple color
                           )%type.


Definition white_board : board :=
  ((Wh, Wh, Wh) ,
   (Wh, Wh, Wh) ,
   (Wh, Wh, Wh) ).

Definition start : board :=
  ((Wh, Wh, Bl),
   (Bl, Wh, Wh),
   (Bl, Bl, Bl)).

Definition target :board :=
  ((Bl, Bl, Bl),
   (Wh, Bl, Wh),
   (Bl, Bl, Wh)).

Check triple_proj.

Definition board_proj (b : board) (pi : pos) (pj : pos) : color :=
  triple_proj pj (triple_proj pi b).

Check pos.

Lemma test_proj_1 :
  board_proj start A B = Wh.

Proof.
  unfold board_proj.
  simpl.
  reflexivity.
Qed.

Lemma test_proj_2 :
  board_proj start B A = Bl.

Proof.
  unfold board_proj.
  simpl.
  reflexivity.
Qed.


Definition inv_row (b : board) (p : pos) : board :=
  triple_map_on (triple_map inv_color) p b.

Definition inv_col (b : board) (p : pos) : board :=
  triple_map (triple_map_on inv_color p) b.

Lemma test_inv_row :
  inv_row start A =   ((Bl, Bl, Wh),
                       (Bl, Wh, Wh),
                       (Bl, Bl, Bl)).


Proof.
  simpl.
  reflexivity.
Qed.

Lemma test_inv_col :
  inv_col start B =  ((Wh, Bl, Bl),
                      (Bl, Bl, Wh),
                      (Bl, Wh, Bl)).


Proof.
  simpl.
  reflexivity.
Qed.


Definition move (b1 b2 : board) : Prop :=
exists p : pos, b2 = inv_col b1 p \/ b2 = inv_row b1 p.

Lemma inv_color_idem c :
    inv_color (inv_color c) = c.

Proof.
  intros.
  destruct c; simpl; reflexivity.
Qed.

Lemma inv_row_idem b p :
  inv_row (inv_row b p) p = b.


Proof.
  intros.
  destruct b.
  destruct p0.
  destruct t0.
  destruct p0.
  destruct t1.
  destruct p0.
  destruct t.
  destruct p0.
  destruct p;
  simpl;
  now repeat rewrite inv_color_idem.
Qed.

Lemma inv_col_idem b p :
      inv_col (inv_col b p) p = b.

Proof.
  intros.
  destruct b.
  destruct p0.
  destruct t0.
  destruct p0.
  destruct t1.
  destruct p0.
  destruct t.
  destruct p0.
  destruct p;
  simpl;
  now repeat rewrite inv_color_idem.
Qed.

Lemma move_sym b1 b2 :
    move b1 b2 -> move b2 b1.

Proof.
  intro.
  destruct H.
  exists x.
  destruct H.
  left.
  rewrite H.
  rewrite inv_col_idem.
  reflexivity.
  right.
  rewrite H.
  rewrite inv_row_idem.
  reflexivity.
Qed.

Inductive moves : board -> board -> Prop :=
| move_ax b1 : moves b1 b1
| move_ind b1 b2 b3: moves b1 b2 -> move b2 b3 -> moves b1 b3.

Lemma mv_mvs b1 b2 b3 :
  move b1 b2 -> moves b2 b3 -> moves b1 b3.

Proof.
  intros.
  induction H0.
  apply move_ind with b1.
  apply move_ax.
  assumption.
  apply move_ind with b2.
  apply IHmoves.
  assumption.
  assumption.
Qed.

Lemma moves_sym b1 b2 :
  moves b1 b2 -> moves b2 b1.

Proof.
  intro.
  induction H.
  apply move_ax.
  apply move_sym in H0.
  apply mv_mvs with b2; assumption.
Qed.

Lemma moves_refl b1 :
  moves b1 b1.

Proof.
  apply move_ax.
Qed.

Lemma moves_trans b1 b2 b3 :
  moves b1 b2 -> moves b2 b3 -> moves b1 b3.

Proof.
  intros.
  induction H0.
  assumption.
  apply move_ind with b2.
  apply IHmoves.
  assumption.
  assumption.
Qed.

Lemma moves_start_target:
  moves start target.

Proof.
  Definition a2 := inv_col target C. 
  apply move_ind with a2.
  Definition a1 := inv_row a2 A.
  apply move_ind with a1.
  apply move_ind with start.
  apply move_ax.
  exists B.
  right.
  unfold a1.
  unfold a2.
  simpl.
  reflexivity.
  exists A.
  right.
  unfold a1.
  symmetry.
  apply inv_row_idem.
  exists C.
  left.
  unfold a2.
  symmetry.
  apply inv_col_idem.
Qed.

Inductive dir :=
| Row
| Col.

  
Definition may c rc p (b : board) :=
  match c with
    | Wh => b
    | Bl => match rc with
              | Row => inv_row b p
              | Col => inv_col b p
            end
  end.

Inductive mays : board -> board -> Prop :=
| mays_ax b: mays b b
| mays_i b b' c rc p: mays b b' -> mays b (may c rc p b').


Lemma mays_to_moves b b' :
  mays b b' -> moves b b'.

Proof.
  intro.
  induction H.
  apply move_ax.
  destruct c.
  destruct rc.
  simpl.
  apply move_ind with b'.
  assumption.
  exists p.
  right.
  reflexivity.
  simpl.
  apply move_ind with b'.
  assumption.
  exists p.
  left.
  reflexivity.
  simpl.
  assumption.
Qed.

Definition force_white ( b : board): board :=
  match b with
    | ((b11, b12, b13), (b21, b22, b23), (b31, b32, b33)) =>
      may b31 Row  C (
            may b21 Row B (
            may b13 Col C (
            may b12 Col B (
            may b11 Col A b ))))
  end.

Check (let f := fun x => (x * 3,x) in f 3).
Lemma moves_to_force b :
  moves b (force_white b).

Proof.
  destruct b.
  destruct p.
  destruct t0.
  destruct t1.
  destruct p0.
  destruct p.
  destruct t.
  destruct p.
  unfold force_white.
  apply mays_to_moves.
  repeat apply mays_i.
  apply mays_ax.
Qed.

Lemma may_comm c rc p c' rc' p' b :
  may c rc p (may c' rc' p' b) = may c' rc' p' (may c rc p b).

Proof.  
  destruct c; destruct c'.
  destruct b.
  destruct p0, t.
  destruct t0, t1, p0.
  destruct p1, p2.
  destruct rc; destruct rc'; destruct p; destruct p'; simpl; reflexivity.

  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma disj_col (x : color) y :
 {x= y}+{~(x=y)}.

Proof.
  




  
Lemma move_force b1 b2 :
  move b1 b2 -> force_white b1 = force_white b2.

Proof.
  destruct b1,b2.
  destruct p, p0.
  destruct t, t0, t1, t2, t3, t4.
  destruct p1, p2, p, p3, p4, p0.
  intro.
  destruct H.
  destruct H.
  destruct x.
  simpl in H.
  
  apply f_equal5 in H.
  Check f_equal.
  Definition f 