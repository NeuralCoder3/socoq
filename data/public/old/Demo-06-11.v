Set Implicit Arguments.
Require Import List.
Notation "x 'el' A" := (In x A) (at level 70).

Section Find.
  Variables (X: Type) (f: X -> bool).
  Implicit Types (x y z: X) (A B C: list X).
  
  Fixpoint find A : option X :=
    match A with
    | nil => None
    | x::A' => if f x then Some x else find A'
    end.

  Fact find_correct A :
    match find A with
    | Some x => x el A /\ f x = true
    | None => forall x, x el A -> f x = false
    end.
  Proof.
    induction A as [|x A IH]; cbn.
    - tauto.
    - destruct (f x) eqn:H.
      + auto.
      + destruct (find A) as [y|].
        * tauto.
        * intros y [<-|H1]; auto.
  Qed.

  Fact Find A :
    { x | x el A /\ f x = true } + (forall x, x el A -> f x = false).
  Proof.
    induction A as [|x A IH]; cbn.
    - tauto.
    - destruct (f x) eqn:H.
      + eauto.
      + destruct IH as [(y&H1&H2)|H1].
        * eauto.
        * right. intros y [<-|H2]; auto.
  Qed.

  Definition find' A :=
    match Find A with
    | inl (exist _ x _) => Some x
    | _ => None
    end.

  Fact find'_correct A :
    match find' A with
    | Some x => x el A /\ f x = true
    | None => forall x, x el A -> f x = false
    end.
  Proof.
    unfold find'.
    destruct (Find A) as [(x&H)|H]; exact H.
  Qed.
 
  Fact find_agree A :
    find A = None <-> find' A = None.
  Proof.
    unfold find'.
    pose proof (find_correct A) as H. 
    destruct (Find A) as [(x&H1)|H1]; destruct (find A) as [y|].
    - intuition congruence.
    - exfalso. destruct H1 as [H1 % H H2]. congruence.
    - exfalso. destruct H as [H % H1 H2]. congruence.
    - tauto.
  Qed.

End Find.
