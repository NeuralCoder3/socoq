Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "A '<<=' B" := (forall x, x el A -> x el B) (at level 70).

Definition dec P := {P} + {~P}.

Structure eqType := EqType
{ eqTypeX :> Type
; eqTypeD : forall x y : eqTypeX, dec (x = y) }.

Notation "x == y" := (eqTypeD x y) (at level 70).

Definition eqb (X: eqType) (x y: X) : bool :=
  if x == y then true else false.
  
Fact eqb_correct (X: eqType) (x y: X) :
  x = y <-> eqb x y = true.
Proof.
  unfold eqb.
  destruct (x == y) as [<-|H].
  - tauto.
  - split.
    + intros <-. tauto.
    + congruence.
Qed.

Fact dec_eq_list (X: eqType) (A B: list X) :
  dec (A = B).
Proof.
  revert B.
  induction A as [|x A IH]; intros B.
  - destruct B as [|y B].
    + now left.
    + right. discriminate.
  - destruct B as [|y B].
    + right. discriminate.
    + specialize (IH B). destruct IH as [<-|IH].
      * destruct (x == y) as [<-|H].
        -- now left.
        -- right. intros H1. injection H1. exact H.           
      * right. intros H. injection H.
        intros <- _. now apply IH.
Qed.

Definition eqType_list (X: eqType) := EqType (@dec_eq_list X).

(* Definition of discrete types not using syntactic sugar *)

Module eqType.
  Inductive eqType : Type :=
  | EqType : forall X: Type, (forall x y: X, dec (x = y)) -> eqType.

  Definition eqTypeX D :=
    match D with @EqType X _ => X end.
  Definition eqTypeD D : forall x y : eqTypeX D, dec (x = y) :=
    match D with EqType f => f end.

  Coercion eqTypeX : eqType >-> Sortclass.
  Check eqTypeD.
End eqType.

(* Decidability of list membership and list inclusion *)

Fact dec_list_all X (p: X -> Prop) A :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros d.
  induction A as [|x A IH].
  - left. intros x [].
  - destruct (d x) as [H|H].
    + destruct IH as [IH|IH].
      * left. intros y [->|H1]; auto.
      * right. contradict IH.
        intros z H1. apply IH. cbn. auto.
    + right. contradict H. apply H. cbn. auto.
Qed.

Fact dec_list_ex X (p: X -> Prop) A :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros d.
  induction A as [|x A IH].
  - right. intros [x [[] _]].
  - destruct (d x) as [H|H].
    + left. exists x. split. now left. exact H.
    + destruct IH as [IH|IH].
      * left. destruct IH as (y&H1&H2).
        exists y. split. now right. exact H2.
      * right. contradict IH.
        destruct IH as (y&H1&H2).
        exists y. split; [|exact H2].
        destruct H1 as [->|H1].
        -- destruct (H H2) as [].
        -- exact H1.
Qed.

Fact dec_trans P Q :
  P <-> Q -> dec P -> dec Q.
Proof.
  unfold dec. tauto.
Qed.

Fact dec_list_el (X: eqType) (x: X) A :
  dec (x el A).
Proof.
  apply dec_trans with (P:= exists z, z el A /\ z = x).
  - split.
    + now intros (z&H&->).
    + intros H. now exists x.
  - refine (dec_list_ex _ _).
    intros y. apply eqTypeD.
Qed.

Fact dec_list_incl (X: eqType) (A B: list X) :
  dec (A <<= B).
Proof.
  refine (dec_list_all _ _).
  intros x.
  apply dec_list_el.
Qed.

(* Cardinality function for lists *)

Inductive card X : list X -> nat -> Prop :=
| cardN : card nil 0
| cardCN x A n : x el A -> card A n -> card (x::A) n
| cardCP x A n : x nel A -> card A n -> card (x::A) (S n).

Section Card.
  Variable X : eqType.
  Implicit Types A B : list X.
  
  Fixpoint Card (A: list X) :=
    match A with
    | nil => 0
    | x::A' => if dec_list_el x A' then Card A' else S (Card A')
    end.

  Fact card_Card A n :
    Card A = n <-> card A n.
  Proof.
    split.
    - intros <-.
      induction A as [|y A IH]; cbn.
      + constructor.
      + destruct (dec_list_el y A) as [H|H].
        * now constructor. 
        * now constructor.
    - induction 1 as [|x A n H _ <-|x A H n _ <-]; cbn.
      + trivial.
      + destruct (dec_list_el x A) as [H1|H1]; tauto.
      + destruct (dec_list_el x A) as [H1|H1]; tauto.
  Qed.
End Card.
