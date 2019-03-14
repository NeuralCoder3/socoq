Set Implicit Arguments.
Unset Strict Implicit.

Inductive le (x: nat) : nat -> Prop :=
| le0 : le x x
| leS : forall y, le x y -> le x (S y).

Notation "x <= y" := (le x y).
Notation "x < y" := (le (S x) y).

Lemma elim_le x (p: nat -> Prop) :
  p x ->
  (forall y, x <= y -> p y -> p (S y)) ->
  forall y, x <= y -> p y.
Proof.
  refine (fun H f => fix g y h {struct h} :=
            match h with
            | le0 _ => H
            | @leS _ y' h' => _
            end).
  (* We declare h as recursive argument since Coq
     otherwise chooses y given that the recursive call is missing.
     In the patterns of the match parameters must apear as "_".
     Moreover, for leS we need the implicit argument h'. *)   
  refine (f y' h' (g y' h')).
  Show Proof.
Qed.

Arguments elim_le {x} p.

Goal 2 <= 4.
Proof.
  constructor. constructor. constructor.
  Show Proof.
Qed.

Goal ~ 1 <= 0.
Proof.
  enough (forall y, le 1 y -> y = 0 -> False) by eauto.
  apply (elim_le (fun y => y <> 0)); discriminate.
Qed.

Goal ~ 1 <= 0.
Proof.
  enough (forall y, le 1 y -> y = 0 -> False) by eauto.
  destruct 1 as [|y' H]; discriminate.
Qed.

Fact le_O x :
  0 <= x.
Proof.
  induction x as [|x IH].
  - constructor.
  - constructor. exact IH.
Qed.

Fact le_O_eq x :
  x <= 0 -> x = 0.
Proof.
  enough (forall y, x <= y -> y = 0 -> x = 0) as H.
  { eauto. }
  destruct 1 as [|y H]. trivial. discriminate.
Qed.

Corollary lt_O x :
  ~ x < 0.
Proof.
  intros H % le_O_eq. discriminate.
Qed.

Goal forall x y z,
    x <= y -> y <= z -> x <= z.
Proof.
  intros x y z H. revert z.
  apply (elim_le (fun z => x <= z)).
  - exact H.
  - intros z _ IH. constructor. apply IH.
Qed.

Fact le_trans x y z :
  x <= y -> y <= z -> x <= z.
Proof.
  intros H.
  induction 1 as [|z _ IH].
  - exact H.
  - constructor. exact IH.
Qed.

Corollary lt_le_lt x y z :
  x < y -> y <= z -> x < z.
Proof.
  apply le_trans.
Qed.

Lemma lt_le x y :
  x < y -> x <= y.
Proof.
  apply le_trans. constructor. constructor.
Qed.

Fact le_SS' x y :
  S x <= S y -> x <= y.
Proof.
  enough (forall z, S x <= z -> z = S y -> x <= y) as H by eauto.
  destruct 1 as [|z H].
  - intros [= <-]. constructor.
  - intros [= <-]. apply lt_le, H.
Qed.

Fact le_SS x y :
  x <= y -> S x <= S y.
Proof.
  induction 1 as [|y _ IH].
  - constructor.
  - constructor. exact IH.
Qed.

Fact le_tricho x y :
  x < y \/ x = y \/ y < x.
Proof.
  revert y.
  induction x as [|x IH]; intros [|y].
  - auto.
  - left. apply le_SS, le_O.
  - right. right. apply le_SS, le_O.
  - specialize (IH y) as [H|[<-|H]].
    + left. apply le_SS, H.
    + auto.
    + right. right. apply le_SS, H.
Qed.

Fact le_lt_lt x y z :
  x <= y -> y < z -> x < z.
Proof.
  intros H. apply le_trans. apply le_SS, H.
Qed.

Fact lt_neq x y :
  x < y -> x <> y.
Proof.
  (* surprising *)
  revert x.
  induction y as [|y IH]; intros x H.
  - contradiction (lt_O H).
  - intros ->. apply (IH y).
    + apply le_SS', H.
    + trivial.
Qed.

Corollary lt_irr x :
  ~ x < x.
Proof.
  intros H % lt_neq. auto.
Qed.
  
Fact le_anti x y :
  x <= y -> y <= x -> x = y.
Proof.
  destruct 1 as [|y H].
  - trivial.
  - intros H1. contradiction (lt_irr (le_lt_lt H H1)).
Qed.

Fact complete_ind (p : nat -> Type) :
  (forall n, (forall m, m < n -> p m) -> p n) -> forall n, p n.
Proof.
  intros H n. apply H.
  induction n as [|n IH]; intros m H1.
  - contradiction (lt_O H1). 
  - apply H. intros k H2. apply IH.
    apply (le_trans H2). apply le_SS', H1.
Qed.

Fact size_ind X (p: X -> Type) (f: X -> nat) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H.
  enough (forall n x, f x < n -> p x) as H1.
  { intros x. apply (H1 (S (f x))). constructor. }
  induction n as [|n IH]; intros x H1.
  - contradiction (lt_O H1). 
  - apply H. intros y H2. apply IH.
    apply (le_trans H2). apply le_SS', H1.
Qed.

(** You may switch to Coq's predefined le predicate by
    deleting the initial defininitions including the
    definition of elim_le and the goals using elim_le.
    The remaining proofs go through unchanged since 
    the tactic constructor abstracts from the names 
    chosen for the constructors. **)
