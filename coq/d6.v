Load naturals.
Load zmod2z.

(* 
 * D6 = {1, r, r^2, s, sr, sr^2}
 * A dihedral group of symmetries on a three sided regular polygon.
 * r elements represent rotations.
 * s elements represent reflection.
 * 1 is the identity.
 * Other elements of the group comprise composition of rotations/reflections 
 *)

Inductive Rot3 : Type :=
   | rot0 : Rot3
   | rot1 : Rot3
   | rot2 : Rot3.

Inductive Ref : Type :=
   | ref0 : Ref
   | ref1 : Ref.

(* Definition D6 : Type := Ref * Rot 3. *)
Definition D6 : Type := Z2Z * Rot3.

Definition succRot3 (x : Rot3) : Rot3 :=
  match x with
  | rot0 => rot1
  | rot1 => rot2
  | rot2 => rot0
  end.

Definition opRot3 (x : Rot3) (y : Rot3) : Rot3 :=
  match x with
  | rot0 => y
  | rot1 => succRot3 y
  | rot2 => succRot3 (succRot3 y)
  end.
