Set Implicit Arguments.
Require Import List.
Notation "x 'el' A" := (In x A) (at level 70).

Definition bdec X (f: X -> bool) (p: X -> Prop) :=
  forall x, p x <-> f x = true.

Definition dec P := {P} + {~P}.
Definition xm P := P \/ ~P.

Locate "+".
Print sumbool.

Fact dec_xm P :
  dec P -> xm P.
Proof.
  unfold xm; intros [H|H]; auto.
Qed.

Fact dec_imp P Q :
  dec P -> dec Q -> dec (P -> Q).
Proof.
  intros H1 [H2|H2].
  - left. trivial.
  - destruct H1 as [H1|H1].
    + right. contradict H2. apply H2, H1.
    + left. intros [] % H1.
Qed.

Goal forall P Q,
    dec P -> dec Q -> dec (P -> Q).
Proof.
  unfold dec. tauto.
Qed.

Section Decider.
  Variable (X: Type).
  Implicit Types (f: X -> bool) (p: X -> Prop).

  (** A function translating a boolean decider
      into an informative decider. *)

  Fact bdec_idec f p : 
    bdec f p -> forall x, dec (p x).
  Proof.
    intros H x. specialize (H x).
    destruct (f x).
    - left. apply H. trivial.
    - right. intros H1 % H. discriminate H1.
  Qed.
 
  (** From an informative decider one can get
      a boolean decider *)
  
  Fact idec_bdec p (d: forall x, dec (p x)) :
    bdec (fun x => if d x then true else false) p.
  Proof.
    intros x.
    destruct (d x) as [H|H].
    - split; trivial.
    - split. tauto. discriminate.
  Qed.

  Fact list_all_idec p :
    (forall x, dec (p x)) -> forall A, dec (forall x, x el A -> p x).
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

  Fixpoint list_all f A :=
    match A with
    | nil => true
    | x::A' => if f x then list_all f A' else false
    end.

  (** If f is a boolean decider for p, then (list_all f)
      is a boolean decider for (fun A => forall x, x el A -> p x) *)    
                                               
  Fact list_all_bdec f p :
    bdec f p ->
    bdec (list_all f) (fun A => forall x, x el A -> p x).
  Proof.
    intros H A.
    induction A as [|x A IH]; cbn.
    - split.
      + trivial.
      + intros _ x [].
    - specialize (H x). destruct (f x); split; intros H1.
      + apply IH. intros y H2. apply H1. auto.
      + intros y [<-|H2].
        * apply H. trivial.
        * apply IH; auto.
      + apply H, H1. auto.
      + discriminate H1.
  Qed.

End Decider.
