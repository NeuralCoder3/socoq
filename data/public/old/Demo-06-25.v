Set Implicit Arguments.
Unset Strict Implicit.


(* preliminary definitions *)

Definition dec P := {P} + {~ P}.
Definition dec1 X (p: X -> Prop) := forall x, dec (p x).
Definition dec2 X Y (p: X -> Y -> Prop) := forall x y, dec (p x y).
Definition discrete X := dec2 (@eq X).

Definition choice X := forall p: X -> Prop, ex p -> sig p.
Definition achoice X := forall p: X -> Prop, dec1 p -> ex p -> sig p.

Definition pi1 X (p: X -> Prop) (u: sig p) : X :=
  match u with exist _ x _ => x end.

Definition pi2 X (p: X -> Prop) (u: sig p) : p (pi1 u) :=
  match u with exist _ _ H => H end.

Definition echoice X :=
  { gamma : choice X | forall p q Hp Hq,
      (forall x, p x <-> q x) -> pi1 (gamma p Hp) = pi1 (gamma q Hq) }.

Definition eachoice X :=
  { gamma : achoice X | forall p q dp dq Hp Hq,
      (forall x, p x <-> q x) -> pi1 (gamma p dp Hp) = pi1 (gamma q dq Hq) }.

Definition range X Y (f: X -> Y) y := exists x, f x = y.
Definition fp X (f: X -> X) x := f x = x.

Implicit Types m n k : nat.


(* definition of retracts and some basic properties *)

Section Retract.

  Variables (A X : Type) (I : A -> X) (R : X -> option A).
  Implicit Types (a b c : A) (x y z : X).
  Definition retract := forall a, R (I a) = Some a.
  Definition tight := forall x a, R x = Some a -> I a = x.
  Variable Req : retract.
  
  Fact retract_injective a b :
    I a = I b -> a = b.
  Proof.
    intros H % (f_equal R).
    rewrite !Req in H. congruence.
  Qed.

  Fact retract_surjective a :
    exists x, R x = Some a.
  Proof.
    exists (I a). apply Req.
  Qed.

  Fact retract_some a b :
    R (I a) = Some b -> a = b.
  Proof.
    rewrite Req. congruence.
  Qed.

  Fact retract_none a :
    R (I a) <> None.
  Proof.
    rewrite Req. congruence.
  Qed.

  Fact RIS x :
    range I x -> { a | I a = x}.
  Proof.
    intros H.
    destruct (R x) as [a|] eqn:H1.
    - exists a. destruct H as [b <-].
      apply retract_some in H1 as ->. trivial.
    - exfalso. destruct H as [a <-].
      apply retract_none in H1 as [].
  Qed.

  Fact retract_discrete :
    discrete X -> discrete A.
  Proof.
    intros H a b.
    destruct (H (I a) (I b)) as [H1|H1].
    - left. apply retract_injective, H1.
    - right. contradict H1. congruence.
  Qed.

  
  (* the range of retractions for discrete types are decidable *)

  Fact retract_discrete_dec :
    discrete X -> dec1 (range I).
  Proof.
    intros H x.
    destruct (R x) as [a|] eqn: H1.
    - destruct (H (I a) x) as [<-|H2].
      + left. exists a. trivial.
      + right. intros [b <-]. destruct (retract_some H1). auto.
    - right. intros [b <-]. destruct (retract_none H1).
  Qed.


  (* tight retracts *)

  Fact retract_tight_image_R x :
    tight -> range I x <-> R x <> None.
  Proof.
    intros H. split.
    - intros [a <-]. rewrite Req. congruence.
    - destruct (R x) as [a|] eqn:H1.
      + apply H in H1 as <-. intros _. now exists a.
      + tauto.
  Qed.

  Fact retract_tight_dec :
    tight -> dec1 (range I).
  Proof.
    intros H x.
    apply (retract_tight_image_R x) in H.
    destruct (R x) as [a|].
    - left. apply H. congruence.
    - right. tauto. 
  Qed.


  (* inheritance of choice functions *)
  
  Definition hat p : X -> Prop :=
    fun x => match R x with Some a => p a | _ => False end.

  Fact hat_ex p :
    ex p -> ex (hat p).
  Proof.
    intros [a H]. exists (I a). unfold hat. rewrite Req. assumption.
  Qed.

  Fact hat_dec p :
    dec1 p -> dec1 (hat p).
  Proof.
    intros H x. unfold hat.
    destruct (R x) as [a|].
    - apply H.
    - right. intros [].
  Qed.

  Fact hat_sig p :
    sig (hat p) -> sig p.
  Proof.
    intros [x H]. unfold hat in H.
    destruct (R x) as [a|]. 
    + exists a. trivial.
    + contradiction H.
  Qed.
  
  Definition retract_choice : choice X -> choice A
    := fun gamma p H => hat_sig (gamma (hat p) (hat_ex H)).
  
  Definition retract_cchoice : achoice X -> achoice A
    := fun gamma p d H => hat_sig (gamma (hat p) (hat_dec d) (hat_ex H)).
  
  Fact hat_sig' p :
    forall u: sig (hat p), { a | p a /\ R (pi1 u) = Some a }.
  Proof.
    intros [x H]. cbn. unfold hat in H.
    destruct (R x) as [a|]. 
    + eauto.
    + tauto.
  Qed.
  
  Fact hat_sig'' p q (u: sig (hat p))  (v: sig (hat q)) :
      pi1 u = pi1 v -> pi1 (hat_sig' u) = pi1 (hat_sig' v).
  Proof.
    destruct (hat_sig' u) as (a&Ha&Haeq).
    destruct (hat_sig' v) as (b&Hb&Hbeq).
    cbn. congruence.
  Qed.
 
  Fact retract_ecchoice :
    eachoice X -> eachoice A.
  Proof.
    intros [gamma H].
    pose (delta p d H := hat_sig' (gamma (hat p) (hat_dec d) (hat_ex H))).
    exists (fun p d H => exist p (pi1 (delta p d H)) (proj1 (pi2 (delta p d H)))).
    cbn. intros * H1. 
    apply hat_sig''. apply H.
    intros x. unfold hat.
    destruct (R x) as [c|]. apply H1. tauto.
  Qed.

End Retract.


(* Decidable predicates can be obtained with retracts *)

Section Sub.

  Variables (X: Type) (p: X -> Prop) (d: dec1 p).
  Implicit Types (x y: X).

  Definition C x := if d x then True else False.

  Fact C_equiv x :
    C x <-> p x.
  Proof.
    unfold C. destruct (d x); tauto.
  Qed.

  Fact trans x :
    p x -> C x.
  Proof.
    apply C_equiv.
  Qed.

  Fact C_pure x :
    forall alpha beta : C x, alpha = beta.
  Proof.
    unfold C.
    destruct (d x) as [H1|H1].
    - intros [] []. trivial.
    - intros [].
  Qed.
    
  Definition sub := sig C.

  Implicit Types a b : sub.
  
  Definition inj a : X := pi1 a.
  
  Definition ret x : option sub :=
    match d x with
    | left H => Some (exist _ x (trans H))
    | right _ => None
    end.

  Fact sub_retract :
    retract inj ret.
  Proof.
    unfold retract.
    intros [x H]. cbn. unfold ret.
    destruct (d x) as [H1|H1].
    - f_equal. f_equal. apply C_pure.
    - contradict H1. apply C_equiv, H.
  Qed.

  Fact sub_image x :
    range inj x <-> p x.
  Proof.
    split.
    - intros [a <-]. apply C_equiv, (pi2 a).
    - intros H % C_equiv. exists (exist _ x H). trivial.
  Qed.

  Fact sub_tight :
    tight inj ret.
  Proof.
    unfold tight.
    intros x a.
    destruct a as [y H]. cbn.
    unfold ret. destruct (d x) as [H1|H1].
    - congruence.
    - discriminate.
  Qed.

End Sub.
