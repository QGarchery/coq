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

Inductive movable_from (b1 : board) : board -> Prop :=
| startb : movable_from b1 b1
| column b2 : (exists p : pos, inv_col b1 p = b2) ->
              movable_from b1 b2
| row b2 : (exists p : pos, inv_row b1 p = b2) ->
           movable_from b1 b2.

Lemma movable :
  movable_from start target.

Proof.
  apply row.