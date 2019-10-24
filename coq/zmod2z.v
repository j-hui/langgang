Inductive Z2Z : Type :=
    | O : Z2Z
    | I : Z2Z.

Definition succZ2Z (x : Z2Z) : Z2Z :=
  match x with
  | O => I
  | I => O
  end.

Definition plusZ2Z (x : Z2Z) (y : Z2Z) : Z2Z :=
  match x with
  | O => y
  | I => succZ2Z y
  end.

Lemma id_com : forall x : Z2Z, plusZ2Z O x = plusZ2Z x O.
Proof. intros x.
       simpl.
       destruct x.
       - simpl.
         reflexivity.
       - simpl.
         reflexivity.
Qed.

Theorem id : forall x : Z2Z, plusZ2Z O x = x.
Proof. intros x.
       simpl.
       reflexivity.
Qed.

(* Proved existence of additive identity that commutes *)

Theorem assoc : forall x y z : Z2Z, plusZ2Z (plusZ2Z x y) z 
        = plusZ2Z x (plusZ2Z  y z).                                              
 Proof. intros x y z.
        destruct x.
        - simpl.
          reflexivity.
        - destruct y.
          + destruct z.
            simpl.
            reflexivity.
            simpl.
            reflexivity.
          + destruct z.
            simpl.
            reflexivity.
            simpl.
            reflexivity.
 Qed.

 Theorem inv : forall x : Z2Z, exists y : Z2Z, plusZ2Z x y = O.
 Proof. intros x.
        destruct x.
        - now exists O.
        - now exists I.               
   Qed.

