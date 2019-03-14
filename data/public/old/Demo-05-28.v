Set Implicit Arguments.
Require Import List Omega.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).

Section Lists.
  Variable X : Type.
  Implicit Types (x y z : X) (A B C : list X).

  Goal forall x y A B, x::A = y::B -> x = y /\ A = B.
  Proof.
    intros x y A B H.
    change (match x::A with nil => True | z::C => z = y /\ C = B end).
    rewrite H. auto.
  Qed.

  Inductive mem x : list X -> Prop :=
  | memB A : mem x (x::A)
  | memC y A : mem x A -> mem x (y::A).

  Goal forall x A, mem x A <-> x el A.
  Proof.
    intros x A. split.
    - induction 1 as [|y A _ IH].
      + left. trivial.
      + right. exact IH.
    - induction A as [|y A IH]; cbn.
      + intros [].
      + intros [->|H].
        * constructor.
        * constructor. apply IH, H.
  Qed.

  Fact filter_iff x A f :
    x el filter f A <-> x el A /\ f x = true.
  Proof.
    induction A as [|y A]; cbn.
    - tauto.
    - destruct (f y) eqn:H; cbn; split.
      + intros [->|H1]; tauto.
      + intros [[->|H1] H2]; tauto.
      + tauto.
      + intros [[->|H1] H2].
        * congruence.
        * tauto.
  Qed.

  Goal forall A B, length (A ++ B) = length A + length B.
  Proof.
    intros A B. induction A as [|x A]; cbn.
    - trivial.
    - f_equal. exact IHA.
  Qed.

  Inductive dupfree : list X -> Prop :=
  | dupfreeN : dupfree nil
  | dupfreeC x A : x nel A -> dupfree A -> dupfree (x::A).

  Fact dup_inv x A :
    dupfree (x::A) -> x nel A /\ dupfree A.
  Proof.
    enough (forall B, dupfree B -> B = x::A -> x nel A /\ dupfree A) by eauto.
    destruct 1 as [|y B H1].
    - intros [=].
    - intros [= -> ->]. auto.
  Qed.

  Inductive card : list X -> nat -> Prop :=
  | cardN : card nil 0
  | cardCN x A n : x el A -> card A n -> card (x::A) n
  | cardCP x A n : x nel A -> card A n -> card (x::A) (S n).

  Fact card_len A n :
    card A n -> n <= length A.
  Proof.
    induction 1 as [|x A n H H3 IH|x A n H _ IH]; cbn; omega.
  Qed.

  Fact card_dupfree A :
    dupfree A <-> card A (length A).
  Proof.
    split.
    - induction 1 as [|x A H1 H2 IH]; cbn.
      + constructor.
      + constructor 3; auto.
    - enough (forall n, card A n -> length A = n -> dupfree A) by eauto.
      induction 1 as [|x A n H H3 IH|x A n H _ IH]; cbn.
      + intros _. constructor.
      + intros <-. exfalso. apply card_len in H3. omega.
      + intros [= <-]. constructor; auto.
  Qed.

 
End Lists.
