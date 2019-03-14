Set Implicit Arguments.
Unset Strict Implicit.


(* Preliminary definitions *)

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

Definition retract A X (I: A -> X) (R: X -> option A) :=
  forall a, R (I a) = Some a.

Implicit Types m n k : nat.


(* Positions and map-products for lists *)

Require Import List Omega.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 50).

Section Positions.
  Variables (X: Type) (d: discrete X).
  Implicit Types (x y: X) (A B : list X).

  Fixpoint pos x A : option nat :=
    match A with
    | nil => None
    | y :: A' => if d x y then Some 0
                else match pos x A' with
                     | Some n => Some (S n)
                     | None => None
                     end
    end.

  Lemma el_pos x A :
    x el A -> { n | pos x A = Some n }.
  Proof.
    induction A as [|y A IH]; cbn; intros H.
    - destruct H as [].
    - destruct (d x y) as [<-|H1].
      + now exists 0.
      + destruct IH as [n IH].
        * destruct H as [->|H]; tauto.
        * rewrite IH. now exists (S n).
  Qed.

  Fixpoint nth n A : option X :=
    match A, n with
    | nil, _ => None
    | x::_, 0 => Some x
    | _::A', S n' => nth n' A'
    end.

  Lemma nth_length A n :
    length A > n -> { x | nth n A = Some x }.
  Proof.
    induction A as [|y A IH] in n |- *; cbn; intros H.
    - exfalso. omega.
    - destruct n as [|n]; cbn.
      + now exists y.
      + destruct (IH n) as [x H1]. omega. now exists x.
  Qed.
  
 Lemma pos_nth x A n :
    pos x A = Some n -> nth n A = Some x.
 Proof.
   induction A as [|y A IH] in n |-*; cbn.
    - intros [=].
    - destruct (d x y) as [<-|H1].
      + now intros [= <-].
      + destruct (pos x A) as [k|]; intros [= <-]; cbn.
        now apply IH.
  Qed.
  
  Lemma nth_app_l x n A B :
    nth n A = Some x -> nth n (A ++ B) = Some x.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn.
    - intros [|n] [=].
    - intros [|n]; cbn; auto. 
  Qed.

End Positions.

Section MapProduct.
  Variables (X Y Z: Type) (f: X -> Y -> Z).

  Fixpoint map_pro (A: list X) (B: list Y) : list Z :=
    match A with
    | x :: A' => map_pro A' B ++ map (f x) B
    | nil => nil
    end.

  Lemma map_pro_in x A B :
    x el map_pro A B <-> exists a b, a el A /\ b el B /\ f a b = x.
  Proof.
  induction A as [|a A IH]; cbn.
  - firstorder.
  - rewrite in_app_iff, IH, in_map_iff. 
    firstorder; subst; eauto.
  Qed.

End MapProduct.


(* Countable types *)

Structure countable X := Countable
{ to_nat : X -> nat ;
  of_nat : nat -> option X ;
  is_retract : retract to_nat of_nat }.

Arguments Countable {_} _ _.

Section EnumCount.

  Variable (X: Type).
  Implicit Types (A B: list X).

  Definition cumulative (L: nat -> list X) :=
    forall n, exists x A, L (S n) = L n ++ x :: A.

  Section Cumulative.
    Variables (L: nat -> list X) (cum : cumulative L).

    Lemma cum_length n :
      length (L n) >= n.
    Proof.
      induction n as [|n IH].
      - omega.
      - destruct (cum n) as (x&A&->).
        rewrite app_length. cbn; omega.
    Qed.

    Lemma cum_nth_ex n:
      { x | nth n (L (S n)) = Some x }.
    Proof.
      apply nth_length, cum_length.
    Qed.
 
    Lemma cum_ge m n :
      m >= n -> exists A, L m = L n ++ A.
    Proof.
      induction 1 as [|m _ IH].
      - exists nil. now rewrite app_nil_r.
      - destruct (cum m) as (x&A&->), IH as [B ->].
        exists (B ++ x :: A). now rewrite app_assoc.
    Qed.

    Lemma cum_ge' x n m:
      x el L n -> m >= n -> x el L m.
    Proof.
      intros H [A ->] % cum_ge. apply in_app_iff. auto.
    Qed.
    
    Lemma cum_nth k m n x :
      nth k (L m) = Some x -> m <= n -> nth k (L n) = Some x.
    Proof.
      intros H1 [A ->] % cum_ge.
      apply nth_app_l, H1.
    Qed.
    
    Lemma cum_nth_eq k m n x y :
      nth k (L m) = Some x -> nth k (L n) = Some y -> x = y.
    Proof.
      intros H1 H2.
      assert (m <= n \/ n <= m) as [H3|H3] by omega.
      - apply (cum_nth H1) in H3. congruence.
      - apply (cum_nth H2) in H3. congruence.
    Qed.
          
  End Cumulative.
  
  Definition enum (L: nat -> list X) (beta : X -> nat) :=
    cumulative L /\ forall x, x el L (beta x).

  Variables (L: nat -> list X) (beta : X -> nat).
  Variable d: discrete X.
            
  Definition ofNat n := nth n (L (S n)).
  Definition toNat x :=
    match pos d x (L (beta x)) with
    | Some n => n
    | None => 0
    end.

  Lemma enum_count :
    enum L beta -> countable X.
  Proof.
    intros [H1 H2].
    apply (@Countable X toNat ofNat).
    intros x. unfold ofNat, toNat.
    specialize (H2 x).
    apply el_pos with (d:=d) in H2 as [n H2].
    rewrite H2. apply pos_nth in H2.
    pose proof (cum_nth_ex H1 n) as [y H3].
    destruct (cum_nth_eq H1 H2 H3) as [].
    exact H3.
  Qed.
      
End EnumCount.

Structure enumerable (X : Type) := Enumerable
  { L : nat -> list X ;
    beta : X -> nat ;
    L_prefix : enum L beta
  }.

Arguments Enumerable {_} _ _.


(* Binary trees are countable *)

Inductive tree : Type :=
| TL : nat -> tree
| TN : tree -> tree -> tree.

Fixpoint treeL n : list (tree) :=
  match n with
  | 0 => nil
  | S n => treeL n ++ [TL n] ++ map_pro TN (treeL n) (treeL n)
  end.

Fixpoint treeB t :=
  match t with
  | TL n => S n
  | TN t1 t2 => S (treeB t1 + treeB t2)
  end.

Lemma treeLcum :
  cumulative treeL.
Proof.
  intros n; induction n; cbn; eauto.
Qed.

Lemma countable_tree :
  countable tree.
Proof.
  apply (@enum_count tree treeL treeB).
  - intros s t. unfold dec. repeat decide equality.
  - split.
    + intros n; induction n; cbn; eauto.
    + intros t. induction t as [n|t1 IH1 t2 IH2]; cbn.
      * apply in_app_iff. cbn. auto.
      * apply in_app_iff. right. right.
        apply map_pro_in. exists t1,t2. repeat split.
        -- apply (cum_ge' treeLcum IH1). omega.
        -- apply (cum_ge' treeLcum IH2). omega.
Qed.
