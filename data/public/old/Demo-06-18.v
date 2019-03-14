Set Implicit Arguments.

Definition dec1 X (p: X -> Prop) :=
  forall x, p x + ~p x.

Definition CF X : Type :=
  forall p: X -> Prop, ex p -> sig p.

Definition ACF X : Type :=
  forall p: X -> Prop, dec1 p -> ex p -> sig p.

Lemma gamma_True : CF True.
Proof.
  intros p H.
  exists I. destruct H as [h H].
  destruct h. exact H.
Qed.

Lemma gamma_False : CF False.
Proof.
  intros p H.
  assert (H1: False).
  {destruct H as [H _]. exact H. }
  destruct H1.
Qed.

(* Unfortunatly, Coq registers sig p as a proposition
   if the first component is a proof.  Thus there is
   no elim restriction and naive proofs become possible. *)    

Check sig (fun x: True => True).

Fact elim_or (gamma: CF bool) :
  forall P Q, P \/ Q -> P + Q.
Proof.
  intros P Q H.
  pose (p (b: bool) := if b then P else Q).
  destruct (gamma p) as [b H1].
  - unfold p. destruct H as [H|H].
    + exists true. exact H.
    + exists false. exact H.
  - destruct b.
    + left. exact H1.
    + right. exact H1.
Qed.

(* For the proofs to come the projections for Sigma-pairs
   will be essential.  Note the use of pi1 in the type
   of pi2, which is essential for several resons. *)

Definition pi1 X (p: X -> Prop) (a: sig p) :=
  match a with exist _ x _ => x end.

Definition pi2 X (p: X -> Prop) (a: sig p) : p (pi1 a) :=
  match a with exist _ _ b => b end.

Definition ext X (gamma: CF X) :=
  forall p q: X -> Prop,
    (forall x, p x <-> q x) ->
    forall H1 H2, pi1 (gamma p H1) = pi1 (gamma q H2).

Theorem Diaconescu X (gamma: CF X) :
  ext gamma -> (exists a b: X, a <> b) -> forall P, P \/ ~ P.
Proof.
  intros H (a&b&H1) P .
  pose (p x := P \/ x = a).
  pose (q x := P \/ x = b).
  assert (Hp: ex p) by (exists a; now right).
  assert (Hq: ex q) by (exists b; now right).
  assert (H2: P -> pi1 (gamma p Hp) = pi1 (gamma q Hq)).
  { intros H2. apply H. intros x. unfold p, q. tauto. }
  destruct (pi2 (gamma p Hp)) as [H3|H3].
  - left; exact H3.
  - destruct (pi2 (gamma q Hq)) as [H4|H4].
    + left; exact H4.
    + right. intros H5 % H2. apply H1. congruence.
Qed.

Theorem Skolem X Y (R: X -> Y -> Prop) (gamma: CF Y) :
  (forall x, exists y, R x y) -> { f | forall x, R x (f x) }.
Proof.
  intros H.
  exists (fun x => pi1 (gamma (R x) (H x))).
  intros x.

  exact (pi2 (gamma (R x) (H x))).
  Show Proof.
Qed.

Require Import Omega.

Section ACC_nat.
  Variable p : nat -> Prop.
  Implicit Types n k : nat.
  
  Inductive acc n : Prop :=
  | Acc : (~ p n -> acc (S n)) -> acc n.

  (* n must be specified as a uniform index 
     so that Coq exempts acc from the elim restriction *)
 
  Check fun q f => fix g n a :=
    match a: acc n with Acc phi => f n phi (fun h => g (S n) (phi h)) end : q n a.

  Lemma acc_elim (q: nat -> Type) :
    (forall n, (~p n -> acc (S n)) -> (~p n -> q (S n)) -> q n) ->
    forall n, acc n -> q n.
  Proof.
    refine (fun f => fix g n a :=
              match a: acc n with
                Acc phi => f n phi (fun h => g (S n) (phi h))
              end: q n).
  Qed.

  Lemma acc_elim' (q: forall n, acc n -> Type) :
    (forall n (phi: ~p n -> acc (S n)), (forall h: ~p n, q (S n) (phi h)) -> q n (Acc phi)) ->
    forall n (a: acc n), q n a.
  Proof.
    refine (fun f => fix g n a :=
              match a: acc n with
                Acc phi => f n phi (fun h => g (S n) (phi h))
              end: q n a).
  Qed.


  Lemma acc_suff k :
    forall n, p (n + k) -> acc n.
  Proof.
    induction k as [|k IH]; cbn; intros n H. 
    - constructor.
      replace (n + 0) with n in H by omega.
      tauto.
    - constructor.
      replace (n + S k) with (S n + k) in H by omega.
      auto.
  Qed.

  Lemma ex_acc :
    ex p -> acc 0.
  Proof.
    intros [n H]. eapply acc_suff, H.
  Qed.

  Variable d : dec1 p.

  Lemma acc_sig n :
    acc n -> sig p.
  Proof.
    (* canonical elimination lemma suffices *)
    induction 1 as [n _ IH]. 
    destruct (d n) as [H1|H1].
    - exists n. exact H1.
    - apply IH, H1.
  Qed.

  Lemma cc_nat :
    ex p -> sig p.
  Proof.
    intros H % ex_acc % acc_sig. exact H.
  Qed.

  Fixpoint first n (a: acc n) : nat :=
    match a with
      Acc f => match d n with inl _ => n | inr h => first (f h) end
    end.

  Arguments first : clear implicits.
  
  Fact first_correct n a :
    p (first n a).
  Proof.
    revert n a.
    apply acc_elim'. intros n phi IH. cbn.
    destruct (d n) as [H|H].
    - exact H.
    - exact (IH H).
  Qed.

  Lemma acc_sig_plus :
    forall n (a: acc n), { k | p (n +k) }.
  Proof.
    induction 1 as [n _ IH].
    destruct (d n) as [H1|H1].
    - exists 0. now replace (n + 0) with n by omega.
    - specialize (IH H1) as [k IH]. exists (S k).
      now replace (n + S k) with (S n + k) by omega.
  Qed.
  
  Goal forall n, acc n <-> exists k, p (n + k).
  Proof.
    split.
    - intros [k H] % acc_sig_plus. eauto.
    - intros (k&H % acc_suff). exact H.
  Qed.

  Fact first_least' n a :
    forall k, k >= n -> p k -> first n a <= k.
  Proof.
    pattern n, a. revert n a.
    apply acc_elim'. intros n phi IH. cbn.
    destruct (d n) as [H|H].
    - auto.
    - intros k H1 H2.
      assert (H3: k >= S n).
      { enough (k = n \/ k > n) as [->| H4]; omega || tauto. }
      exact (IH H k H3 H2).
  Qed.

  Definition least n k := n <= k /\ p k /\ forall i, n <= i -> p i -> k <= i.

  Fact first_least n a :
    least n (first n a).
  Proof.
    revert n a.
    apply acc_elim'. intros n phi IH. cbn.
    destruct (d n) as [H|H].
    - hnf. auto.
    - hnf. specialize (IH H). split. 2:split.
      + destruct IH as [IH _]. omega.
      + apply IH.
      + intros i H1 H2. apply IH; [|exact H2].
        assert (n = i \/ S n <= i) as [<-| H3].
        * omega.
        * contradict (H H2).
        * auto.
  Qed.        
  
End ACC_nat.

Goal forall p n k, least p n k <-> p k /\ n <= k /\ forall i, i < k -> n <= i -> ~p i.
Proof.
  split.
  - intros H. split. 2:split.
    + apply H.
    + apply H.
    + intros i H1 H2 H3. destruct H as (_&H&H4).
      specialize (H4 i H2 H3). omega.
  - intros (H1&H2&H3). split. exact H2. split. exact H1.
    intros i H4 H5.
    assert (k <= i \/ i < k) as [H6|H6] by omega. 1:exact H6.
    exfalso. apply (H3 i H6 H4 H5).
Qed.

Definition unique X (p: X -> Prop) : Prop :=
  forall x y, p x -> p y -> x = y.

Goal forall p n, unique (least p n).
Proof.
  unfold least.
  intros p n a b Ha Hb. 
  enough (a <= b <= a) by omega.
  split.
  - apply Ha; apply Hb.
  - apply Hb; apply Ha.
Qed.
  
