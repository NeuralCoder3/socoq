Goal forall x, x + 0 = x.
Proof.
  Check nat_ind.
  Check (nat_ind (fun x => x + 0 = x)).
  apply nat_ind.
  - trivial.
  - intros n IH. cbn. f_equal.
    exact IH.
Qed.

Goal forall X Y Z : Prop,
    (X -> Y) -> (Y -> Z) -> X -> Z.
Proof.
  intros X Y Z f g x.
  apply g. apply f. apply x.
  Show Proof.
Qed.

Goal forall X Y : Prop,
    (forall Z: Prop, (X -> Y -> Z) -> Z) -> X.
Proof.
  intros X Y f.
  apply f. intros x _. apply x.
  Show Proof.
Qed.

Goal forall X : Prop,
    False -> X.
Proof.
  intros X H.
  destruct H.
  Show Proof.
Qed.

Goal forall X: Prop,
    ~ ~ ~ X -> ~ X.
Proof.
  unfold not.
  intros X f x.
  apply f. intros g. apply g, x.
  Show Proof.
Qed.

Goal forall X: Prop,
    (X -> ~ X) -> (~ X -> X) -> False.
Proof.
  unfold not.
  intros X f g.
  assert (x: X).
  { apply g. intros x.
    apply (f x x). }
  apply (f x x).
  Show Proof.
Qed.

Goal forall X Y Z : Prop,
    X /\ (Y \/ Z) -> X /\ Y \/ X /\ Z.
Proof.
  intros X Y Z [x [y|z]].
  - left. split.
    + apply x.
    + apply y.
  - right.  split.
    + apply x.
    + apply z.
 Show Proof.
Qed.
