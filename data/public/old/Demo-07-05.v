Require Import Setoid.
(* Set Printing Universes. *)

Module Aczel.
  Polymorphic Cumulative Inductive tree : Type :=
  | T : forall X: Type, (X -> tree) -> tree.

  Implicit Types s t : tree.

  Definition sub s t : Prop :=
    match t with T X f => exists x, f x = s end.

  Fact wf s :
    ~ sub s s.
  Proof.
    induction s as [X f IH].
    cbn. intros [x H]. apply (IH x).
    rewrite H at 2. cbn. eauto.
  Qed.

  Definition u := T tree (fun s => s).

  Goal False.
  Proof.
    apply (wf u).
    unfold u at 2. cbn.
    (* exists u. *)
  Abort All.

  Definition v := T tree (fun s => s).

  Goal sub v u.
  Proof.
    exists v. reflexivity.
  Qed.

  Goal sub u v.
  Proof.
    (* exists v. reflexivity. *)
  Abort All.
  
End Aczel.

Module Coquand.
  Inductive tree : Prop :=
  | T : forall X: Prop, (X -> tree) -> tree.

  Lemma elim_tree (p: tree -> Prop) :
    (forall (X: Prop) (f: X -> tree), (forall x, p (f x)) -> p (T X f)) ->
    forall s, p s.
  Proof.
    refine (fun f => fix g s :=
              match s : tree with T X h => f X h (fun x => g (h x)) end: p s: Prop).
  Qed.
  
  Implicit Types s t : tree.

  Section Coquand.
    Variables (A: Prop) (E: Prop -> A) (D: A -> Prop)
              (equiv: forall X, D (E X) <-> X).

    Definition sub s t : Prop :=
      D match t with T X f => E (exists x, f x = s) end.

    Fact sub_ex s X f :
      sub s (T X f) <-> exists x, f x = s.
    Proof.
      cbv. split; apply equiv.
    Qed.

    Fact wf s :
      ~ sub s s.
    Proof.
      revert s.
      apply elim_tree. intros X f IH.
      unfold sub. intros [x H] % equiv. 
      apply (IH x). rewrite H at 2. unfold sub.
      apply equiv. eauto.
    Qed.
    
    Definition u := T tree (fun s => s).

    Theorem Coquand :
      False.
    Proof.
      apply (wf u). unfold u at 2, sub.
      apply equiv. eauto.
    Qed.
  End Coquand.

  Goal forall X: Prop, Prop <> X.
  Proof.
    intros X H. generalize (Coquand X). destruct H.
    intros H. apply (H (fun X => X) (fun X => X)).
    tauto.
  Qed.
  
  Theorem XM_PI :
    (forall X: Prop, X \/ ~ X) -> forall (X: Prop) (x y : X), x = y.
  Proof.
    intros d A a b.
    destruct (d (a = b)) as [H|H].
    - exact H.
    - exfalso.
      apply (Coquand A (fun Z => if d Z then a else b) (eq a)).
      intros X. destruct (d X) as [H1|H1]; tauto.
  Qed.

End Coquand.

Module Hierarchy.

  Definition Tyi := Type.

  (* Inductive tree : Tyi :=
     | T : forall X: Tyi, (X -> tree) -> tree.
     does not type-check because Tyi is predicative. *)

  Definition cast (X Y: Tyi) : X = Y -> X -> Y :=
    fun h x => match h with eq_refl => x end.

  Lemma elim_eq' X (y: X) (p: forall x, x = y -> Type) :
    p y eq_refl -> forall x (h : x = y), p x h.
  Proof.
    intros H x h. revert y h p H. 
    destruct h. auto.
  Qed.

  Section Hierarchy.
    Variables (A: Tyi) (E: Tyi -> A) (D: A -> Tyi).
    
    Inductive tree : Tyi:=
    | T : forall a, (D a -> tree) -> tree.

    Implicit Types s t : tree.
    
    Definition sub s t : Prop :=
      match t with T a f => exists x: D a, f x = s end.

    Fact wf s :
      ~ sub s s.
    Proof.
      induction s as [a f IH].
      intros [x H]. apply (IH x).
      rewrite H at 2. cbn. eauto.
    Qed.
   
    Theorem hierarchy :
      exists X: Tyi, D (E X) <> X.
    Proof.
      exists tree. intros H.
      pose (u := T (E tree) (cast (D(E tree)) tree H)).
      apply (wf u). unfold u at 2. cbn.
      (* rewrite H. (* rewrite tactic is smart *) *)
      pattern (D (E tree)), H. apply elim_eq'.
      cbn. eauto.
    Qed.
  End Hierarchy.
  
  Goal forall X:Tyi, Tyi <> X.
  Proof.
    intros X H.
    generalize (hierarchy X). destruct H. intros H1.
    specialize (H1 (fun x => x) (fun x => x)) as [X H1]. 
    auto.
  Qed.
  
End Hierarchy.

Module Hierarchy_le.

  (* less or equal for types *)
  Definition tle X Y := 
    exists (E: X -> Y) (D: Y -> X), forall x, D (E x) = x.

  Definition Tyi := Type.
  
  Section Hier.
    Variables (A: Tyi) (E: Tyi -> A) (D: A -> Tyi).
    
    Inductive tree : Tyi:=
    | T : forall a, (D a -> tree) -> tree.

    Implicit Types s t : tree.
    
    Definition sub s t : Prop :=
      match t with T a f => exists x: D a, f x = s end.

    Fact wf s :
      ~ sub s s.
    Proof.
      induction s as [a f IH].
      intros [x H]. apply (IH x).
      rewrite H at 2. cbn. eauto.
    Qed.
   
    Lemma hier :
      ~ tle tree (D (E tree)).
    Proof.
      intros (F&G&H).
      pose (u:= T (E tree) G).
      apply (wf u). unfold u at 2. cbn. 
      exists (F u). apply H.
    Qed.
    
  End Hier.

  Theorem hierarchy (A: Tyi) (E: Tyi -> A) (D: A -> Tyi) :
    exists X, D (E X) <> X.
  Proof.
    exists (tree A D). intros H.
    apply (hier A E D). rewrite H.
    exists (fun s => s), (fun s => s). eauto.
  Qed.
  
  Goal forall X:Tyi, Tyi <> X.
  Proof.
    intros X H.
    generalize (hierarchy X). destruct H. intros H1.
    specialize (H1 (fun x => x) (fun x => x)) as [X H1].
    auto.
  Qed.
  
End Hierarchy_le.

