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

Lemma inv_color_idem :
  forall c : color,
    inv_color (inv_color c) = c.

Proof.
  intros.
  destruct c; simpl; reflexivity.
Qed.

Lemma inv_row_idem:
  forall b : board, forall p : pos,
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
  rewrite inv_color_idem;
  rewrite inv_color_idem;
  rewrite inv_color_idem;
  reflexivity.
Qed.

Lemma inv_col_idem:
  forall b : board, forall p : pos,
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
  rewrite inv_color_idem;
  rewrite inv_color_idem;
  rewrite inv_color_idem;
  reflexivity.
Qed.

Lemma move_comm :
  forall b1 b2 : board, 
    move b1 b2 -> move b2 b1.

Proof.
  intros.
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
| move_ind b1 b3: (exists b2 : board, moves b1 b2 /\ move b2 b3) -> moves b1 b3.



Lemma trying :
  forall b1 : board,
    moves b1 b1.





Lemma moves_comm:
  forall b1 b2 : board,
    moves b1 b2 -> moves b2 b1.

Proof.
  intros.

  induction H eqn:?.
  apply move_ax.
  
  


Lemma movable :
  moves start target.

Proof.
  assert (moves start start).
  apply move_ax.
  assert (moves start (inv_col start C)).
  apply (move_ind (inv_col start C)).