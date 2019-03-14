Set Implicit Arguments.
Unset Strict Implicit.
Require Import Omega List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 50).
Notation "A <<= B" := (forall x, x el A -> x el B) (at level 50).

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

Fact weak A B s :
  A |- s -> A <<= B -> B |- s.
Proof.
  intros H. revert B.
  induction H as [A s H | A s _ IH | A s t _ IH | A s t _ IH1 _ IH2];
    intros B H1.
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

Fact ndAbsurd A s u:
  A |- s -> A |- -s -> A |- u.
Proof.
  intros H1 H2. apply ndE, (ndIE H2 H1).
Qed.

Fact DN A s :
  --s el A -> s::A |- bot -> A |- bot.
Proof.
  intros H1  H2 % agree.
  revert H2. apply ndIE. apply ndA, H1.
Qed.

Fact app2 A s1 s2 t :
  A |- s1 ~> s2 ~> t -> A |- s1 -> A |- s2 -> A |- t.
Proof.
  intros H1 H2 H3.
  apply (ndIE (ndIE H1 H2) H3).
Qed.

Fact DNI A s t :
  s::-t::A |- bot -> A |- --(s~>t).
Proof.
  intros H % agree % agree.
  revert H. apply ndIE.
  apply ndII, ndII.
  apply ndIE with (s:= s~>t).
  { apply ndA; cbn; auto. }
  apply ndII, ndE.
  apply app2 with (s1:= -t) (s2:= s).
  { apply ndA; cbn; auto. }
  - apply ndII.
    apply ndIE with (s:= s~>t).
    { apply ndA; cbn; auto. }
    apply ndII, ndA; cbn; auto.
  - apply ndA; cbn; auto.
Qed.

Goal forall s t, [s ~> --t] |- --(s ~> t).
Proof.
  intros s t.
  apply ndII.
  apply ndIE with (s:= s~>t).
  { apply ndA; cbn; auto. }
  apply ndII, ndE.
  apply app2 with (s1:=s) (s2:= -t).
  - apply ndA; cbn; auto.
  - apply ndA; cbn; auto.
  - apply ndII, ndE.
    apply ndIE with (s:= s~>t).
    { apply ndA; cbn; auto. }
    apply ndII, ndA; cbn; auto.
Qed.

Fixpoint ground s : bool :=
  match s with
  | var _ => false
  | bot => true
  | s1 ~> s2 => if ground s1 then ground s2 else false
  end.

Fact ground_ldec s :
  if ground s then {nil |- s} + {nil |- -s} else True.
Proof.
  induction s as [x| |s IH1 t IH2]; cbn.
  - trivial.
  - right. apply ndII, ndA. cbn; auto.
  - destruct (ground s); [|exact I].
    destruct (ground t); [|exact I].
    destruct IH2 as [IH2|IH2].
    + left. apply ndII. apply (weak IH2). cbn; auto.
    + destruct IH1 as [IH1|IH1].
      * right. apply ndII. apply ndAbsurd with (s:=t).
        -- apply ndIE with (s:=s).
           ++ apply ndA. cbn; auto.
           ++ apply (weak IH1). cbn; auto.
        -- apply (weak IH2). cbn; auto.
      * left. apply ndII. apply ndAbsurd with (s:=s).
        -- apply ndA. cbn; auto.
        -- apply (weak IH1). cbn; auto.
Qed.
           
Module DN.
  Inductive tval := ff | nn | tt.
  
  Implicit Types (a b: tval) (alpha: nat -> tval).

  Definition le a b : bool :=
    match a, b with
    | ff , _ => true
    | _, tt => true
    | nn, nn => true
    | _, _ => false
    end.

  Notation "a <= b" := (le a b).
  
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
          
  Notation "A |= s" := (forall alpha, inf alpha A <= eva alpha s = true) (at level 70).

  Lemma sound A s :
    A |- s -> A |= s.
  Proof.
    intros H alpha.
    induction H as [A s H | A s _ IH | A s t _ IH | A s t _ IH1 _ IH2].
    - apply inf_in, H.
    - revert IH. cbn.
      destruct inf, eva; cbn ; congruence.
    - revert IH. cbn.
      destruct inf, eva, eva; cbn ; congruence.
    - revert IH1 IH2. cbn.
      destruct inf, eva, eva; cbn ; congruence.
  Qed.

  Fact DN n :
    ~ nil |- -- var n ~> var n.
  Proof.
    intros H.
    apply sound with (alpha:= fun _ => nn) in H. 
    revert H. simpl eva. cbn. discriminate.
  Qed.

  Fact consistent :
    ~ nil |- bot.
  Proof.
    intros H. apply DN with (n:=0). apply ndE, H.
  Qed.

End DN.

Implicit Types  (theta: nat -> form).
  
Fixpoint subst theta s : form :=
  match s with
  | var x => theta x
  | bot => bot
  | s~>t => subst theta s ~> subst theta t
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

Fact nd_subst A s theta :
  A |- s -> substC theta A |- subst theta s.
Proof.
  induction 1 as [A s H | A s _ IH | A s t _ IH | A s t _ IH1 _ IH2];
    cbn in *.
  - apply ndA, substC_in, H.
  - apply ndE, IH.
  - apply ndII, IH.
  - apply (ndIE IH1 IH2).
Qed.

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
         
Notation "A |= s" := (forall alpha, if inf alpha A then eva alpha s = true else True)
                      (at level 70).

Section Sandwich.
  Variable E: list form -> form  -> Prop.
  Notation "A ||- s" := (E A s) (at level 70).
  Variable Eassu: forall s A, s el A -> A ||- s.
  Variable Ecut: forall A s t, A ||- s -> s::A ||- t -> A ||- t.
  Variable Eweak: forall A s B, A ||- s -> A <<= B -> B ||- s.
  Variable Esubst: forall A s theta, A ||- s -> substC theta A ||- subst theta s.
  Variable Econs: exists s, ~ nil ||- s.
  Variable Eexfalso : forall A s, A ||- bot -> A ||- s.
  Variable Eimpl: forall A s t, A ||- s ~> t <-> s::A ||- t.

  Fact EIE A s t :
    A ||- s~>t -> A ||- s -> A ||- t.
  Proof.
    intros H1 % Eimpl H2. apply (Ecut H2 H1).
  Qed.

  Fact absurd s :
    nil ||- s -> nil ||- -s -> False.
  Proof.
    intros H1 H2. destruct Econs as [t H].
    apply H. apply Eexfalso, (EIE H2 H1).
  Qed.

  Definition hat alpha n := if alpha n then -bot else bot.

  Lemma Tebbi alpha s :
    if eva alpha s then nil ||- subst (hat alpha) s
    else nil ||- -subst (hat alpha) s.
  Proof.
    induction s as [n| |s1 IH1 s2 IH2]; cbn.
    - unfold hat. destruct alpha.
      + apply Eimpl, Eassu. cbn; auto.
      + apply Eimpl, Eassu. cbn; auto.
    - apply Eimpl, Eassu. cbn; auto.
    - set (sigma := subst (hat alpha)) in *.
      destruct (eva alpha s1).
      + destruct eva.
        * apply Eimpl. apply (Eweak IH2). cbn; auto.
        * apply Eimpl. apply EIE with (s:= sigma s2).
          -- apply (Eweak IH2). cbn; auto.
          -- apply EIE with (s:= sigma s1).
             ++ apply Eassu. cbn; auto.
             ++ apply (Eweak IH1). cbn; auto.
      + apply Eimpl, Eexfalso, Eimpl. exact IH1.
  Qed.
  
  Lemma E2BE' s :
    nil ||- s -> nil |= s.
  Proof.
    intros H alpha. cbn. generalize (Tebbi alpha s).
    destruct eva.
    - auto.
    - intros H1. exfalso.
      apply Esubst with (theta:= hat alpha) in H. cbn in H.
      apply (absurd H H1).
  Qed.

  Fixpoint rev A s :=
    match A with
    | nil => s
    | u::A' => rev A' (u ~> s)
    end.

  Fact reversion A s :
    A ||- s <-> nil ||- rev A s.
  Proof.
    revert s.
    induction A as [|u A IH]; intros s; simpl rev.
    - tauto.
    - split.
      + intros H. apply IH, Eimpl, H.
      + intros H. apply Eimpl, IH, H.
  Qed.

  Fact Bimpl A s t :
    A |= s ~> t <-> s::A |= t.
  Proof.
    cbn; split; intros H alpha;
      specialize (H alpha); destruct eva, inf; auto.
  Qed.

  Fact breversion A s :
    A |= s <-> nil |= rev A s.
  Proof.
    revert s.
    induction A as [|u A IH]; intros s; simpl rev.
    - tauto.
    - split.
      + intros H. apply IH, Bimpl, H.
      + intros H. apply Bimpl, IH, H.
  Qed.

  Theorem E2BE A s :
    A ||- s -> A |= s.
  Proof.
    intros H. apply breversion, E2BE'.
    apply reversion with (A:= A), H.
  Qed.
    
End Sandwich.
    
  

