Set Implicit Arguments.
Unset Strict Implicit.
Require Import Omega List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 50).
Notation "A <<= B" := (forall x, x el A -> x el B) (at level 50).



(*** Intuitionistic ND ***)

(* inductive type expressing implicational propositional formulas *)

Inductive form : Type :=
| var : nat -> form
| bot : form
| imp : form -> form -> form.

(* notation for object-level logical operations *)

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "- s" := (s ~> bot) (at level 35, right associativity).
Reserved Notation "A |- s" (at level 70).

(* intuitionistic natural deduction as inductive predicate *)

Inductive nd : list form -> form -> Prop :=
| ndA A s : s el A -> A |- s
| ndE A s : A |- bot -> A |- s
| ndII A s t : s::A |- t -> A |- s ~> t
| ndIE A s t : A |- s ~> t -> A |- s -> A |- t
where "A |- s" := (nd A s).

(* intuitionistic ND coincides with derivations on Coq level *)

Goal forall X : Prop, X -> ~ ~ X.
Proof.
  intros X.
  intros H.
  intros H'.
  apply H'.
  exact H.
Qed.  

Goal forall s, [] |- s ~> - - s.
Proof.
  intros s.
  apply ndII.
  apply ndII.
  apply ndIE with (s:=s). apply ndA. firstorder.
  apply ndA. firstorder.
Qed.

Goal ~ ~ False -> False.
Proof.
  intros H.
  apply H.
  intros H'.
  exact H'.
Qed.

Goal [] |- - - bot ~> bot.
Proof.
  apply ndII.
  apply ndIE with (s:=-bot). apply ndA. firstorder.
  apply ndII.
  apply ndA. firstorder.
Qed.

(* intuitionistic ND satisfies weakening, agreement, and cut *)

Fact weak A B s :
  A |- s -> A <<= B -> B |- s.
Proof.
  intros H. revert B.
  induction H as [A s H | A s _ IH | A s t _ IH | A s t _ IH1 _ IH2]; intros B H1.
  - apply ndA. auto.
  - apply ndE. apply IH, H1.
  - apply ndII. apply IH. firstorder.
  - apply ndIE with (s:=s).
    + apply IH1, H1.
    + apply IH2, H1.
Qed.

Fact agree A s t :
  A |- s~>t <-> s::A |- t.
Proof.
  split.
  - intros H % (weak (B:= s::A)).
    + apply (ndIE H). apply ndA; cbn; auto.
    + cbn; auto.
  - apply ndII.
Qed.

Fact cut A s t :
  A |- s -> s::A |- t -> A |- t.
Proof.
  intros H1 H2 % agree. apply (ndIE H2 H1).
Qed.



(*** Heyting Entailment ***)
           
Module DN.

  (* assume a three-valued type of ordered truth values *)

  Inductive tval := ff | nn | tt.
  
  Implicit Types (a b : tval) (alpha : nat -> tval).

  Definition le a b : bool :=
    match a, b with
    | ff , _ => true
    | _, tt => true
    | nn, nn => true
    | _, _ => false
    end.

  Notation "a <= b" := (le a b).

  (* evaluation of formulas and lists w.r.t. truth value assignments *)
  
  Fixpoint eva alpha s : tval :=
    match s with
    | var x => alpha x
    | bot => ff
    | s~>t => if eva alpha s <= eva alpha t then tt else eva alpha t
    end.

  Fixpoint inf alpha A : tval :=
    match A with
    | nil => tt
    | s::A' => if eva alpha s <= inf alpha A' then eva alpha s else inf alpha A'
    end.

  Fact inf_in alpha A s :
    s el A -> (inf alpha A <= eva alpha s) = true.
  Proof.
    induction A as [|t A IH]; cbn.
    + intros [].
    + intros [->|H].
      * destruct eva, inf; cbn; congruence.
      * generalize (IH H). destruct  inf, eva, eva; cbn ; congruence.
  Qed.

  (* A implies s in Heyting semantics if under every alpha s is as least as true as A *)
          
  Notation "A |= s" := (forall alpha, inf alpha A <= eva alpha s = true) (at level 70).

  (* intuitionistic ND is sound w.r.t. Heyting semantics *)

  Lemma sound A s :
    A |- s -> A |= s.
  Proof.
    intros H alpha.
    induction H as [A s H | A s _ IH | A s t _ IH | A s t _ IH1 _ IH2].
    - apply inf_in, H.
    - revert IH. cbn.
      destruct inf, eva; cbn; congruence.
    - revert IH. cbn.
      destruct inf, eva, eva; cbn; congruence.
    - revert IH1 IH2. cbn.
      destruct inf, eva, eva; cbn; congruence.
  Qed.

  (* intuitionistic ND is constructive as it does not prove all instances of double negation *)

  Fact DN n :
    ~ nil |- -- var n ~> var n.
  Proof.
    intros H.
    apply sound with (alpha:= fun _ => nn) in H. 
    revert H. simpl eva. cbn. discriminate.
  Qed.

  (* intuitionistic ND is consistent as it does not prove all formulas (and hence not false) *)

  Fact consistent :
    ~ nil |- bot.
  Proof.
    intros H. apply DN with (n:=0). apply ndE, H.
  Qed.

End DN.
