From Coq Require Import Arith List Omega Bool Program.Tactics.

Definition beqn (a b : bool) := if a then b else negb b.

Goal forall f (x:bool), f x = f(f(f x)).
Proof.
  intros f [|]; destruct (f true) eqn:F;destruct (f false) eqn:H;congruence.
Qed.

Goal forall f (x:bool), f x = f(f(f x)).
Proof.
	intros f x; destruct x eqn:F, (beqn  x (f x)) eqn: H.
    - unfold beqn in H;rewrite F in H;try congruence.
    - unfold beqn in H;rewrite F in H;try congruence.
      rewrite H. (*  *)
    - 