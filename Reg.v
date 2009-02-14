Require Import OrderedType.

Require Import Eqdep_dec_defined.
Require Import INeq.

Notation "'!'" := (False_rect _ _).
Definition cast {I:Type}(F:I -> Type)(i:I) {j:I} (e : j = i) : F j -> F i :=
  fun t' => eq_rect _ F t' _ e.


Inductive type : Set := Void | Unit | Loop
| Summ : type -> type -> type
| Prod : type -> type -> type.

Definition eq_type_dec : forall τ σ : type, {τ = σ} + {τ <> σ}.
decide equality.
Defined.

Section Reg.

Variable Φ : type.

Inductive value : type -> Set :=
  
| The : value Unit

| Rec : value Φ -> value Loop

| Inl : forall τ σ, value τ -> value (Summ τ σ)
| Inr : forall τ σ, value σ -> value (Summ τ σ)

| And : forall τ σ, value τ -> value σ -> value (Prod τ σ).

Definition value_lt (ρ : type) (x y : value ρ) : Prop.
refine (fix value_lt (ρ : type) (x y : value ρ) {struct x} : Prop := _).
refine (
  match x in value ρ, y in value ρ' return ρ = ρ' -> Prop with
    | The, The => fun e1 => True
    | The, Rec φ' => fun e1 => !
    | The, Inl τ' σ' l' => fun e1 => !
    | The, Inr τ' σ' r' => fun e1 => !
    | The, And τ' σ' u' v' => fun e1 => !

    | Rec φ, The => fun e1 => !
    | Rec φ, Rec φ' => fun e1 => value_lt Φ φ φ'
    | Rec φ, Inl τ' σ' l' => fun e1 => !
    | Rec φ, Inr τ' σ' r' => fun e1 => !
    | Rec φ, And τ' σ' u' v' => fun e1 => !

    | Inl τ σ l, The => fun e1 => !
    | Inl τ σ l, Rec φ' => fun e1 => !
    | Inl τ σ l, Inl τ' σ' l' => fun e1 => value_lt τ l (cast value τ _ l')
    | Inl τ σ l, Inr τ' σ' r' => fun e1 => True
    | Inl τ σ l, And τ' σ' u' v' => fun e1 => !

    | Inr τ σ r, The => fun e1 => !
    | Inr τ σ r, Rec φ' => fun e1 => !
    | Inr τ σ r, Inl τ' σ' l' => fun e1 => False
    | Inr τ σ r, Inr τ' σ' r' => fun e1 => value_lt σ r (cast value σ _ r')
    | Inr τ σ r, And τ' σ' u' v' => fun e1 => !

    | And τ σ u v, The => fun e1 => !
    | And τ σ u v, Rec φ' => fun e1 => !
    | And τ σ u v, Inl τ' σ' l' => fun e1 => !
    | And τ σ u v, Inr τ' σ' r' => fun e1 => !
    | And τ σ u v, And τ' σ' u' v' => fun e1 =>
      value_lt τ u (cast value τ _ u') \/
      (u = (cast value τ _ u') /\ value_lt σ v (cast value σ _ v'))
  end
  (refl_equal ρ)
);
match goal with
  | |- False => discriminate
  | _ => congruence
end.
Defined.

Ltac resolve_INeq :=
  match goal with Q : @INeq _ _ ?I ?x ?I ?y |- _ =>
    (rewrite -> Q || rewrite <- Q); [ apply eq_type_dec |]; clear Q
  end.

Ltac snap_Summ :=
  match goal with Q : Summ _ _ = Summ _ _ |- _ =>
    injection Q; intro; intro; clear Q
  end.

Ltac snap_Prod :=
  match goal with Q : Prod _ _ = Prod _ _ |- _ =>
    injection Q; intro; intro; clear Q
  end.

Definition value_compare (ρ : type) (x y : value ρ) : Compare (value_lt ρ) (@eq (value ρ)) x y.
refine (fix value_compare (ρ : type) (x y : value ρ) {struct x} : Compare (value_lt ρ) (@eq (value ρ)) x y := _).
refine (
  match x as x' in value ρ',
        y as y' in value ρ''
  return ρ' = ρ'' -> ρ = ρ' -> ρ = ρ'' ->
         INeq value x ρ' x' -> INeq value y ρ'' y' ->
         Compare (value_lt ρ) (@eq (value ρ)) x y
  with
    | The, The => fun e1 e2 e3 e4 e5 => EQ _ _
    | The, Rec φ' => fun e1 => !
    | The, Inl τ' σ' l' => fun e1 => !
    | The, Inr τ' σ' r' => fun e1 => !
    | The, And τ' σ' u' v' => fun e1 => !

    | Rec φ, The => fun e1 => !
    | Rec φ, Rec φ' => fun e1 e2 e3 e4 e5 =>
      match value_compare Φ φ φ' with
        | LT _ => LT _ _ | EQ _ => EQ _ _ | GT _ => GT _ _
      end
    | Rec φ, Inl τ' σ' l' => fun e1 => !
    | Rec φ, Inr τ' σ' r' => fun e1 => !
    | Rec φ, And τ' σ' u' v' => fun e1 => !

    | Inl τ σ l, The => fun e1 => !
    | Inl τ σ l, Rec φ' => fun e1 => !
    | Inl τ σ l, Inl τ' σ' l' => fun e1 e2 e3 e4 e5 =>
      let Q := _ in
      match value_compare τ l (cast value τ Q l') with
        | LT _ => LT _ _ | EQ _ => EQ _ _ | GT _ => GT _ _
      end
    | Inl τ σ l, Inr τ' σ' r' => fun e1 e2 e3 e4 e5 => LT _ _
    | Inl τ σ l, And τ' σ' u' v' => fun e1 => !

    | Inr τ σ r, The => fun e1 => !
    | Inr τ σ r, Rec φ' => fun e1 => !
    | Inr τ σ r, Inl τ' σ' l' => fun e1 e2 e3 e4 e5 => GT _ _
    | Inr τ σ r, Inr τ' σ' r' => fun e1 e2 e3 e4 e5 =>
      let Q := _ in
      match value_compare σ r (cast value σ Q r') with
        | LT _ => LT _ _ | EQ _ => EQ _ _ | GT _ => GT _ _
      end
    | Inr τ σ r, And τ' σ' u' v' => fun e1 => !

    | And τ σ u v, The => fun e1 => !
    | And τ σ u v, Rec φ' => fun e1 => !
    | And τ σ u v, Inl τ' σ' l' => fun e1 => !
    | And τ σ u v, Inr τ' σ' r' => fun e1 => !
    | And τ σ u v, And τ' σ' u' v' => fun e1 e2 e3 e4 e5 =>
      let Q := _ in let Q' := _ in
      match value_compare τ u (cast value τ Q u') with
        | LT _ => LT _ _
        | EQ _ =>
          match value_compare σ v (cast value σ Q' v') with
            | LT _ => LT _ _
            | EQ _ => EQ _ _
            | GT _ => GT _ _
          end
        | GT _ => GT _ _
      end
  end
  (refl_equal ρ) (refl_equal ρ) (refl_equal ρ)
  (INeq_refl value ρ x) (INeq_refl value ρ y)
);
match goal with
  | |- False => discriminate
  | _ => repeat snap_Summ; repeat snap_Prod; subst; repeat resolve_INeq
  | _ => repeat snap_Summ; repeat snap_Prod;
    generalize dependent Q; subst; repeat resolve_INeq;
    intro Q; rewrite (eq_proofs_unicity eq_type_dec Q (refl_equal _)); clear Q;
    simpl; intros
  | _ => repeat snap_Summ; repeat snap_Prod;
    generalize dependent Q'; generalize dependent Q; subst; repeat resolve_INeq;
    intro Q; try rewrite (eq_proofs_unicity eq_type_dec Q (refl_equal _)); clear Q;
    simpl; intros;
      generalize dependent Q'; subst; repeat resolve_INeq;
    intro Q'; try rewrite (eq_proofs_unicity eq_type_dec Q' (refl_equal _)); clear Q';
    simpl in *; intros
  | _ => idtac
end;
try (exact I || reflexivity || congruence || assumption).
left; assumption.
right; split; [reflexivity | assumption].
right; split; [reflexivity | assumption].
left; assumption.
Defined.

End Reg.


