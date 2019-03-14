Set Implicit Arguments.
Unset Strict Implicit.

Definition nat_rec :=
  fun p a f => fix g n := match n with
                       | 0 => a
                       | S n' => f n' (g n')
                       end : p n.

Check nat_rec.

Lemma nat_ind (p: nat -> Prop) :
  p 0 -> (forall n, p n -> p (S n)) -> forall n, p n.
Proof.
  exact (nat_rec (p:=p)).
Qed.

Goal forall n,
    S n <> n.
Proof.
  apply nat_ind.
  - discriminate.
  - intros n IH. contradict IH. congruence.
Qed.

Goal forall x y,
    x + y = y + x.
Proof.
  intros x y. pattern x. revert x.
  apply nat_ind.
  - cbn. revert y. apply nat_ind.
    + trivial.
    + intros n IH. cbn. f_equal. exact IH.
  - intros x IH. cbn. rewrite IH. clear IH.    
    revert y. apply nat_ind.
    + trivial.
    + intros y IH. cbn. f_equal. exact IH.
Qed.

Definition add := fun x y => nat_rec y (fun _ => S) x.

Goal forall x y,
    add 0 y = y /\ add (S x) y = S(add x y).
Proof.
  split; trivial.
Qed.

Goal forall x y,
    x + y = add x y.
Proof.
  intros x y. revert x. apply nat_ind.
  - trivial.
  - intros x IH. cbn. f_equal. trivial.
Qed.

Fixpoint eqb (x y: nat) : bool :=
  match x, y with
  | 0, 0 => true
  | 0, S _ => false
  | S x, S y => eqb x y
  | S _, 0 => false
  end.

Fact eqb_eq x y :
  eqb x y = true <-> x = y.
Proof.
  revert y. pattern x. revert x. apply nat_ind.
  - intros [|y]; cbn.
    + tauto.
    + split; congruence.
  - intros x IH [|y]; cbn.
    + split; congruence.
    + split.
      * intros [] % IH. trivial.
      * intros H. apply IH. congruence.
Qed.

Goal forall x y: nat,
    x = y \/ x <> y.
Proof.
  intros x y.
  destruct (eqb x y) eqn:H.
  - left. apply eqb_eq, H.
  - right. intros H1 % eqb_eq. congruence.
Qed.
  


