Goal forall X Y (p: X -> Y -> Prop),
    (exists x, exists y, p x y) -> exists y, exists x, p x y.
Proof.
  intros X Y p.
  intros [x [y H]].
  exists y. exists x. exact H.
Qed.

(* De Morgan law for exists *)

Goal forall X (p: X -> Prop),
    ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  intros X p. split.
  - intros H x H1. apply H. exists x. exact H1.
  - intros H [x H1]. apply (H x). exact H1.
Qed.

(* De Morgan law for /\ *)

Goal forall X Y : Prop,
    X \/ ~ X -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof.
  intros X Y [H1|H1] H2.
  - right. intros H3. apply H2. auto.
  - left. exact H1.
Qed.

Goal forall X Y : Prop,
    ~ ~ (~ (X /\ Y) -> ~ X \/ ~ Y).
Proof.
  intros X Y H.
  apply H. intros H1. left. intros H2.
  apply H. intros _. right. intros H3.
  apply H1. auto.
Qed.

(* Peirce's law *)

Goal forall X Y : Prop,
    X \/ ~ X -> ((X -> Y) -> X) -> X.
Proof.
  intros X Y [H1|H1] H2.
  - exact H1.
  - apply H2. intros H3. exfalso. apply H1, H3.
Qed.

Goal forall X Y : Prop,
    ~ ~ (((X -> Y) -> X) -> X).
Proof.
  intros X Y H.
  apply H. intros H1. apply H1. intros H2. exfalso.
  apply H. intros _. exact H2.
Qed.

(* De Morgan law for forall *)

Goal forall X (p: X -> Prop),
    (forall X: Prop, ~ ~ X -> X) ->
    ~ (forall x, p x) <-> exists x, ~ p x.
Proof.
  intros X p H. split.
  - intros H1. apply H. intros H2.
    apply H1. intros x. apply H. intros H3.
    apply H2. exists x. exact H3.
  - intros [x H1] H2. apply H1,
                      H2.
Qed.

Fact Russell (X : Prop) :
  ~ (X <-> ~ X).
Proof.
  intros [H1 H2].
  assert (H3: X).
  { apply H2. intros H3. exact (H1 H3 H3). }
  exact (H1 H3 H3).
Qed.
  
Fact barber X (p: X -> X -> Prop) :
  ~ exists x, forall y, p x y <-> ~ p y y.
Proof.
  intros [x H].
  generalize (H x).
  apply Russell.
Qed.

(* Most of the proofs above can be done by the
   automation tactic "tauto". Here is an example. *)

Goal forall X Y : Prop,
    X \/ ~ X -> ((X -> Y) -> X) -> X.
Proof.
  tauto.
Qed.

Goal forall X Y : Prop,
    ~ ~ (~ (X /\ Y) -> ~ X \/ ~ Y).
Proof.
  tauto.
Qed.

Goal forall X: Prop,
  ~ (X <-> ~ X).
Proof.
  tauto.
Qed.

Module LogicalConstants.
  (* We define the logial constants using the
   proof constructor names from the lecture notes.
   We use the "Arguments" command for the 
   proof constructors L, R, and E to get 
   the implicit arguments we want.
   We  give a couple of proof terms and observe
   the type inference done by Coq 
   with the "Show Proof" command. *)

  Set Implicit Arguments.

  Inductive True: Prop := I: True.
  Inductive False: Prop := .

  Inductive and (X Y: Prop) : Prop :=
  | C: X -> Y -> and X Y.
  
  Inductive or (X Y: Prop) : Prop :=
  | L: X -> or X Y
  | R: Y -> or X Y.

  Arguments L {X Y}.
  Arguments R {X Y}.

  Goal forall X: Prop,
      False -> X.
  Proof.
    exact (fun X H => match H with end).
  Qed.

  Goal forall X Y Z : Prop,
      and X (or Y Z) -> or (and X Y) (and X Z).
  Proof.
    exact (fun X Y Z H => match H with
                       | C x (L y) => L (C x y)
                       | C x (R z) => R (C x z)
                       end).
    Show Proof.
  Qed.

  Goal forall X Y : Prop,
      or X Y <-> forall Z:Prop, (X -> Z) -> (Y -> Z) -> Z.
  Proof.
    intros X Y. split.
    - intros H Z f g. destruct H as [x|y].
      + apply f, x.
      + apply g, y.
    - intros H. apply H. exact L. exact R.
      Show Proof.
  Qed.

  Inductive ex (X: Type) (p: X -> Prop) : Prop :=
  | E: forall x: X, p x -> ex p.

  Arguments E {X p}.

  Goal forall X Y (p: X -> Y -> Prop),
      ex (fun x => (ex (fun y => p x y))) ->
      ex (fun y => (ex (fun x => p x y))).
  Proof.
    exact (fun X Y p H => match H with
                       | E x (E y H1) => E y (E x H1)
                       end).
    Show Proof.
  Qed.

End LogicalConstants.