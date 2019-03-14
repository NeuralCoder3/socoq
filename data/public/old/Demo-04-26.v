Set Implicit Arguments.
Unset Strict Implicit.

(* Conversion Demo *)

Definition D: nat -> nat :=
  fix f x := match x with 0 => 0 | S x' => S (S (f x')) end.

Goal D 1 = 2.
Proof.
  cbv delta [D].
  cbv fix. cbv beta.
  cbv match. cbv beta.
  cbv fix. cbv beta.
  cbv match.
  trivial.
Qed.

(* Inductive Definition of Equality *)

Module Eq.
  
  Inductive eq (X : Type) (x : X) : X -> Prop :=
  | Q : eq x x.

  Arguments Q {X x}.  (* Make both parameters implicit arguments *)
  
  Fact rewrite X (x y: X) (p: X -> Type) :
    eq x y -> p y -> p x.
  Proof.
    intros []. trivial.
  Qed.

  Fact rewrite' X (x y: X) (p: X -> Type) :
    eq x y -> p x -> p y.
  Proof.
    intros []. trivial.
  Qed.

  (* Rewrite law with proof terms *)
  
  Goal forall X (x y: X) p,
      eq x y -> p y -> p x.
  Proof.
    exact (fun X x y p H => match H with Q => fun H1 => H1 end).
  Qed.

  Goal forall X (x y: X) p,
      eq x y -> p y -> p x.
  Proof.
    refine (fun X x y p H => match H with Q => _ end).
    trivial.
  Qed.

  (* Disequations *)
  
  Goal ~ eq True False.
  Proof.
    intros H.
    pattern False.
    apply (rewrite' H).
    exact I.
  Qed.

  Goal ~ eq true false.
  Proof.
    exact (fun H => rewrite (p:= fun b: bool => if b then False else True) H I).
  Qed.

  Goal ~ eq true false.
  Proof.
    intros H.
    change ((fun b: bool  => if b then False else True) true).
    apply (rewrite H I).
  Qed.

  (* Impredicative Characterization *)
  
  Goal forall X (x y: X),
      eq x y <-> forall p: X -> Prop, p x -> p y.
  Proof.
    intros X x y. split.
    - intros []. auto.
    - intros H. pattern y. apply H. apply Q.
  Qed.

  (* Agreement with predefined equality *)
  
  Goal forall X (x y: X),
      eq x y <-> x = y.
  Proof.
    intros X x y. split.
    - intros []. reflexivity.
    - intros H. rewrite H. apply Q.
  Qed.

  (* Disjointness and injectivity for 0, S *)

  Goal forall x,
      ~ eq (S x) 0.
  Proof.
    intros x H.
    change (match 0 with 0 => False | S _ => True end).
    pattern 0.
    apply (rewrite' H I).
  Qed.

  Goal forall x y,
      eq (S x) (S y) -> eq x y.
  Proof.
    intros x y H.
    change (eq match S x with 0 => 0 | S x' => x' end y).
    pattern (S x).
    apply (rewrite H). apply Q.
  Qed.
  
End Eq.

(* Disequality of types *)

Goal
  bool <> True.
Proof.
  pose (p X := forall x y : X, x = y).
  assert (H1: p True).
  { unfold p. intros [] []. trivial. }
  assert (H2: ~ p bool).
  { unfold p. intros H. discriminate (H true false). }
  intros H. apply H2. rewrite H. exact H1.
Qed.

Goal
  nat <> bool.
Proof.
  pose (p X := forall x y z : X, x = y \/ x = z \/ y = z).
  assert (H1: p bool).
  { intros [|] [|] [|]; auto. }
  assert (H2: ~ p nat).
  { intros H.
    destruct (H 0 1 2) as [H3|[H3|H3]];
      discriminate H3. }
  intros H. apply H2. rewrite H. exact H1.
Qed.

(* Kaminski *)

Goal forall (f: bool -> bool) x,
    f (f (f x)) = f x.
Proof.
  intros f x.
  destruct x.
  - destruct (f true) eqn:H1.
    + congruence.
    + destruct (f false) eqn:H2.
      * exact H1.
      * exact H2.
  - destruct (f false) eqn:H1.
    + destruct (f true) eqn:H2.
      * exact H2.
      * exact H1.
    + congruence.
Qed.
        