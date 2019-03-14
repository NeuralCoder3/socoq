Set Implicit Arguments.
Unset Strict Implicit.
Require Import Omega List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 50).
Notation "A <<= B" := (forall x, x el A -> x el B) (at level 50).



(*** Intuitionistic ND ***)

Inductive form : Type :=
| var : nat -> form
| bot : form
| imp : form -> form -> form.

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "- s" := (s ~> bot) (at level 35, right associativity).
Reserved Notation "A |- s" (at level 70).

Inductive nd : list form -> form -> Prop :=
| ndA A s : s el A -> A |- s
| ndE A s : A |- bot -> A |- s
| ndII A s t : s::A |- t -> A |- s ~> t
| ndIE A s t : A |- s ~> t -> A |- s -> A |- t
where "A |- s" := (nd A s).


(*** Substitution ***)
 
Implicit Types  (theta : nat -> form).

(* variable substitution can be lifted to formulas and contexts *)
  
Fixpoint subst theta s : form :=
  match s with
  | var x => theta x
  | bot => bot
  | s ~> t => subst theta s ~> subst theta t
  end.

Fixpoint substC theta A : list form :=
  match A with
  | nil => nil
  | s::A' => subst theta s :: substC theta A'
  end.

Fact substC_in s A theta:
  s el A -> subst theta s el substC theta A.
Proof.
  induction A as [|t A IH]; cbn.
  - intros [].
  - intros [->|H]; auto.
Qed.

(* intuitionistic provability respects substitution *)

Fact nd_subst A s theta :
  A |- s -> substC theta A |- subst theta s.
Proof.
  induction 1 as [A s H | A s _ IH | A s t _ IH | A s t _ IH1 _ IH2]; cbn in *.
  - apply ndA. apply substC_in. apply H.
  - apply ndE, IH.
  - apply ndII, IH.
  - apply (ndIE IH1 IH2).
Qed.

(* definition of boolean semantics *)

Implicit Types alpha : nat -> bool.

Fixpoint eva alpha s : bool :=
  match s with
  | var x => alpha x
  | bot => false
  | s~>t => if eva alpha s then eva alpha t else true
  end.

Fixpoint inf alpha A : bool :=
  match A with
  | nil => true
  | s::A' => if eva alpha s then inf alpha A' else false
  end.

Definition valid A s :=
  forall alpha, if inf alpha A then eva alpha s = true else True.
         
Notation "A |= s" := (valid A s) (at level 70).

(* boolean semantics respects substitution *)

Definition beta theta alpha :=
  fun x => eva alpha (theta x).

Lemma beta_eva theta alpha s :
  eva alpha (subst theta s) = eva (beta theta alpha) s.
Proof.
  induction s; unfold beta; cbn; try reflexivity.
  rewrite IHs1, IHs2. reflexivity.
Qed.

Lemma beta_inf theta alpha A :
  inf alpha (substC theta A) = inf (beta theta alpha) A.
Proof.
  induction A; unfold beta; cbn; try reflexivity.
  rewrite IHA. rewrite beta_eva. reflexivity.
Qed.

Fact ce_subst A s theta :
  A |= s -> substC theta A |= subst theta s.
Proof.
  intros H alpha.
  rewrite beta_eva, beta_inf.
  apply H.
Qed.
