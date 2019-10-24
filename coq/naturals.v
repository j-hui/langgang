Inductive N : Type :=
    | Z: N
    | S (n : N) : N.

Fixpoint plusN (x : N) (y : N) : N :=
    match x with
    | Z => y
    | S x => S (plusN x y)
    end.

Lemma succ (a b : N): plusN a (S b) = S (plusN a b).
Proof.
  - induction a.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHa.
      reflexivity.
Qed.

Theorem commute_plusN : forall x y : N, plusN x y = plusN y x.
Proof.
  intros x y.
  induction x.
  - simpl.
    induction y.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHy.
      reflexivity.
  - simpl.
    rewrite IHx.
    rewrite succ.
    reflexivity.
Qed.

Theorem assoc_plusN : forall x y z : N, plusN (plusN x y) z = plusN x (plusN y z).
Proof.
  intros x y z.
  induction x.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHx.
    reflexivity.
  Qed.

(*Theorem commute_broken : forall x y : N, plusN x y = plusN y x.
Proof.
  intros x y.
  induction x.
  - simpl.
    induction y.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHy.
      reflexivity.
  - simpl.
    induction y.
    + simpl.
      rewrite IHx.
      simpl.
      reflexivity.
    + simpl.
      apply IHx in IHy.
Qed.*)
