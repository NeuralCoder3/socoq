Inductive bool :=
| true : bool
| false : bool.

Definition negb x :=
  match x with
    | true => false
    | false => true
  end. 

Print negb.

Goal negb (negb true) = true.
Proof.
  cbn. trivial.
Qed.

Goal forall x, negb (negb x) = x.
Proof.
  intros x.
  destruct x.
  - trivial.
  - trivial.
Qed.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint plus x y :=
  match x with
  | O => y
  | S x' => S (plus x' y)
  end.

Notation "x + y" := (plus x y).

Fact plusO x :
  x + O = x.
Proof.
  induction x as [|x IH].
  - trivial.
  - cbn. rewrite IH. trivial.
Qed.

Fact plusS x y :
  x + S y = S (x + y).
Proof.
  induction x as [|x IH].
  - cbn. trivial.
  - cbn. rewrite IH. trivial.
Qed.

Goal forall x y, x + S y = S ( x + y).
Proof.
  intros. induction x; cbn; congruence.
Qed.

Fact plus_com x y :
  x + y = y + x.
Proof.
  induction x as [|x IH]; cbn.
  - now rewrite plusO.
  - rewrite plusS. now rewrite IH.
Qed.

Goal forall x y, x + y = y + x.
Proof.
  intros x y.
  revert x y.
Abort All.


