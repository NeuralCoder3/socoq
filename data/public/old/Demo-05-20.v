(** 
    We define elimination functions for various inductive types.
    The definitions are obtained mechanically with the following scheme: 
    Start with the match annotated with the match type and the target type.
    If the elim restriction applies, place the target type in Prop.
    In each rule of the match, use a function 
    taking all non-parametric arguments of the constructor.
    Then collect the necessary arguments ordered as follows: 
    First the parameters,
    then the target type function, 
    then the functions for the value constructors,
    then the indices, 
    and finally the argument that is matched on.
    Type inference will determine all argument types.

    For a recursive elimination function,
    consume the indices and the argument that is matched on
    with a recursive abstraction and add recursive arguments
    to the applications of the functions in the rules of the match.
    
 **)

Definition elim_True :=
  fun p a x => 
    match x: True with I => a end: p x.

Check elim_True.

Definition elim_bool :=
  fun p a b x =>
    match x: bool with true => a | false => b end: p x.

Check elim_bool.

Definition elim_nat :=
  fun p a f x =>
      match x: nat with 0 => a | S x' => f x' end: p x.

Check elim_nat.

Definition ind_nat :=
  fun p a f => fix g x :=
    match x: nat with 0 => a | S x' => f x' (g x') end: p x.

Check ind_nat.
Check fun p H f => ind_nat p H (fun x _ => f x).

Definition elim_prod :=
  fun A B p f x =>
    match x: A * B with (a,b) => f a b end: p x.

Check elim_prod.

Definition elim_and :=
  fun A B Z f h =>
    match h: A /\ B with conj a b => f a b end: Z.

Check elim_and.

Definition elim_and' :=
  fun A B p f h =>
    match h: A /\ B with conj a b => f a b end: p h.

Check elim_and'.

Definition elim_or :=
  fun X Y Z f g h =>
    match h: X \/ Y with or_introl x => f x | or_intror y => g y end: Z: Prop.

Check elim_or.

Definition elim_or' :=
  fun X Y p f g h =>
    match h: X \/ Y with or_introl x => f x | or_intror y => g y end: p h: Prop.

Check elim_or'.

Definition elim_False :=
  fun Z h => 
    match h: False with end: Z.

Check elim_False.

Definition elim_ex :=
  fun X q p f h =>
    match h: @ex X q with ex_intro _ x H => f x H end: p h: Prop.

Check elim_ex.

Definition elim_eq :=
  fun X x p H y h =>
    match h: x = y :> X with eq_refl => H end: p y.

Check elim_eq.

Definition elim_eq' :=
  fun X x p H y h =>
    match h: x = y :> X with eq_refl => H end: p y h.

Check elim_eq'.

Inductive le (x: nat) : nat -> Prop :=
| leB: le x x
| leS: forall y, le x y -> le x (S y).

Definition elim_le :=
  fun x p H f y h =>
    match h: le x y with leB _ => H | leS _ y' h' => f y' h' end : p y: Prop.

Check elim_le.

Definition ind_le :=
  fun x p H f => fix g y h :=
    match h: le x y with leB _ => H | leS _ y' h' => f y' h' (g y' h') end: p y: Prop.

Check ind_le.

Inductive even: nat -> Prop :=
| evenB : even 0
| evenS : forall x, even x -> even (S (S x)).

Definition ind_even :=
  fun p H f => fix g x h :=
    match h: even x with evenB => H | evenS x' h' => f x' h' (g x' h') end: p x: Prop.

Check ind_even.