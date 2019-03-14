From Coq Require Import Arith List Omega Bool Program.Tactics.

Goal forall f (x:bool), f x=f(f(f(x))).
Proof.
  intros f [|]; destruct (f true) eqn:H, (f false) eqn: G;auto.
  - rewrite H. now rewrite H.
  - rewrite H. now rewrite H.
  - rewrite H. now rewrite H.
  - rewrite G. now rewrite G.
  - rewrite H. now rewrite G.
  - rewrite G. now rewrite G.
Qed.

