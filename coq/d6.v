Load naturals.

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

Definition D6 : Type := Ref * Rot3.
