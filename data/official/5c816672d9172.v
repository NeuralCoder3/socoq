From Coq Require Import Arith List Omega Bool Program.Tactics.

Goal forall (n:nat), True.
Proof.
intros x.
exact I.
Qed.            