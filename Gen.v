Require Import OrderedType.
Require Import Reg.

Theorem faithful_encoding (T : Type) (Φ : type)
  (codify : T -> value Φ Φ) (codify_faithful : forall x y, codify x = codify y -> x = y) :
  forall x y : T, Compare (fun x y => value_lt Φ Φ (codify x) (codify y)) (@eq _) x y.
intros.
destruct (value_compare Φ Φ (codify x) (codify y)).
apply LT; assumption.
apply EQ; apply codify_faithful; assumption.
apply GT; assumption.
Defined.

(** examples **)

Definition nat_code := Summ Unit Loop.
Fixpoint nat_codify (n : nat) : value nat_code nat_code :=
  let o := Inl _ _ _ (The _) in
  let s n := Inr _ _ _ (Rec _ n) in
  match n with O => o | S n => s (nat_codify n) end.
Theorem nat_codify_faithful (n m : nat) : nat_codify n = nat_codify m -> n = m.
Admitted.

Definition nat_lt : nat -> nat -> Prop :=
  fun n m => value_lt nat_code nat_code (nat_codify n) (nat_codify m).
Definition nat_compare : forall x y, Compare nat_lt (@eq nat) x y := 
  faithful_encoding nat nat_code nat_codify nat_codify_faithful.

Eval compute in nat_compare 3 5.
(* LT *)



Definition bool_list_code := Summ Unit (Prod (Summ Unit Unit) Loop).

Fixpoint bool_list_codify (b : list bool) : value bool_list_code bool_list_code :=
  let n := Inl _ _ _ (The _) in
  let c x xs := Inr _ _ _ (And _ _ _ x (Rec _ xs)) in
  let t := Inl _ _ _ (The _) in
  let f := Inr _ _ _ (The _) in
  match b with
    | nil => n
    | true :: xs => c t (bool_list_codify xs)
    | false :: xs => c f (bool_list_codify xs)
  end.
Theorem bool_list_codify_faithful (n m : list bool) : bool_list_codify n = bool_list_codify m -> n = m.
Admitted.

Definition bool_list_lt : list bool -> list bool -> Prop :=
  fun n m => value_lt bool_list_code bool_list_code (bool_list_codify n) (bool_list_codify m).
Definition bool_list_compare : forall x y, Compare bool_list_lt (@eq (list bool)) x y := 
  faithful_encoding (list bool) bool_list_code bool_list_codify bool_list_codify_faithful.

Eval compute in bool_list_compare
  (false :: true :: false :: nil)
  (false :: true :: nil).

