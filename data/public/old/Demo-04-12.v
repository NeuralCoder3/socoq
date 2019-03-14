(* Ackermann Function.
   Write a function f satisfying
   f 0 y = S y
   f (S x) 0 = f x 1
   f (S x) (S y) = f x (f (S x) y) 
*)

Module Ackermann1.
  Fixpoint g h y := match y with
                    | 0 => h 1
                    | S y' => h (g h y')
                    end.

  Fixpoint f x := match x with
                  | 0 => S
                  | S x' => g (f x')
                  end.

  Goal forall x y, f (S x) (S y) = f x (f (S x) y).
  Proof.
    intros. cbn. trivial.
  Qed.
  
  Goal forall y, f 0 y = S y.
  Proof.
    trivial.
  Qed.
  
  Goal forall x, f (S x) 0 = f x 1.
  Proof.
    trivial.
  Qed.
End Ackermann1.

Module Ackermann2.
  Definition f := fix f x := match x with
                             | 0 => S
                             | S x' => fix g y := match y with
                                                 | 0 => f x' 1
                                                 | S y' => f x' (g y')
                                                 end
                             end.
  
  Goal forall x y, f (S x) (S y) = f x (f (S x) y).
  Proof.
    intros. cbn. trivial.
  Qed.
  
  Goal forall y, f 0 y = S y.
  Proof.
    trivial.
  Qed.
  
  Goal forall x, f (S x) 0 = f x 1.
  Proof.
    trivial.
  Qed.
End Ackermann2.

Print Ackermann2.f.

Set Implicit Arguments.

Module Pairs.
  Section Pairs.
    Variables X Y : Type.

    Inductive prod : Type :=
    | pair : X -> Y -> prod.

    Definition fst p :=
      match p with pair x _ => x end.

    Definition snd p :=
      match p with pair _ y => y end.

    Goal forall p, p = pair (fst p) (snd p).
    Proof.
      intros p. destruct p as [x y]. trivial.
    Qed.

    Goal forall p, p = pair (fst p) (snd p).
    Proof.
      intros [x y]. trivial.
    Qed.
  End Pairs.

  Check prod.
  Check pair.
  Check fst.
  Print fst.

  Check pair 2 true.

  Notation "( x , y )" := (pair x y).
  Notation "X ** Y" := (prod X Y) (at level 10).

  Check (2,true).
  
End Pairs.

Module Iter.
  Fixpoint it X (f: X -> X) n x :=
    match n with
    | 0 => x
    | S n' => f (it f n' x)
    end.

  Check it.

  Goal forall x y, x + y = it S x y.
  Proof.
    intros x y.
    induction x as [|x IH]; cbn.
    - trivial.
    - rewrite IH. trivial.
  Qed.

  Goal forall x y, x * y = it (fun z => y + z) x 0.
  Proof.
    intros x y.
    induction x as [|x IH]; cbn.
    - trivial.
    - rewrite IH. trivial.
  Qed.
  
  Goal forall x y, x * y = it (fun z => y + z) x 0.
  Proof.
    intros x y; induction x; cbn; congruence.
  Qed.

  Lemma shift X (f: X -> X) n x :
    it f (S n) x = it f n (f x).
  Proof.
    induction n as [|n IH]; cbn.
    - trivial.
    - rewrite <- IH. trivial.
  Qed.
End Iter.


  

  
 

 