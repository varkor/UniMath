Require Import UniMath.Foundations.PartD.

Inductive Pointed (T : UU) :=
  | Space : T -> Pointed T
  | Point : Pointed T
  .
Definition Pointed_map (T T' : UU) (f : T -> T') (p : Pointed T) : Pointed T' :=
  Pointed_rect T (λ _, Pointed T')
    (λ t, Space _ (f t))
    (Point _)
  p.

(* Inductive Coproduct (A B : UU) :=
  | L : A -> Coproduct A B
  | R : B -> Coproduct A B
  . *)

Inductive Σ (T : UU -> UU) (Γ : UU) :=
  | Abs : T (Pointed Γ) -> Σ T Γ
  | App : T Γ -> T Γ -> Σ T Γ
  .
Definition Σ_map (T T' : UU -> UU) (Γ Γ' : UU) (f : ∏ Γ, T Γ -> T' Γ) (g : Γ -> Γ') (s : Σ T Γ) : Σ T' Γ.
  Check Σ_rect T Γ (λ _, Σ T' Γ')
    (λ pt, Abs _ _ (f _ (Pointed_map Γ Γ' g pt))).
  Σ_rect T (λ _, Pointed T')
  (λ t, Space _ (f t))
  (Point _)
p.
Definition Σm (T T' : UU -> UU) (Γ : UU) (f : ∏ Γ, T Γ -> T' Γ) (s : Σ T Γ) : Σ T' Γ :=
  match s with
  | Abs _ _ pt => Abs _ _ (f _ pt)
  | App _ _ t1 t2 => App _ _ (f _ t1) (f _ t2)
  end.

(* Check map.

Definition Σm' (T : UU -> UU) (Γ Γ' : UU) (f : Γ -> Γ') (s : Σ T Γ) : Σ T Γ' :=
  match s with
  | Abs _ _ pt => Abs _ _ (Pointedm Γ Γ' f pt)
  | App _ _ t1 t2 => App _ _ (f t1) (f t2)
  end. *)

Check Σ_rec.

Inductive Term (V : UU -> UU) (Γ : UU) :=
  | Var : V Γ -> Term V Γ
  | Sig : Σ (Term V) Γ -> Term V Γ
  .
Definition Term_map (V : UU -> UU) (Γ Γ' : UU) (f : Γ -> Γ') (t : Term V Γ) :=
  match t

Definition Term_st (Γ Γ' : UU) (tg : (Term Id Γ) × Γ') : Term Id (Γ × Γ') :=
  let (t, g) := tg in match t with
  | Var _ _ vg => Var _ _ (vg, g)
  | Sig _ _ sg => Sig _ _

Let Id := (λ x : UU, x).

(* λ x. x *)
Let lambda_x_x := Sig Id ∅ (Abs (Term Id) ∅ (Var Id (Pointed ∅) (Point ∅))).
Let lambda_x_x' := Sig Id ∅ (Abs _ _ (Var _ _ (Point _))).

(* Definition st (Γ : UU) (U U' : UU -> UU) (t : Σ U (U' Γ)) : Σ (U (U' Γ)). *)

(* Parameterised initiality. *)
Section Parameterised_Initiality.

Context (A P : UU -> UU).
Context (ϵ : ∏ (Γ : UU), P Γ -> A Γ).
Context (ϕ : ∏ (Γ : UU), Σ Id (A Γ) -> A Γ).

(* Context (Γ : UU) (t : Term Id Γ) (p : P Γ). *)

(* Check ϕ Γ (λ x, match x with
  | Abs _ _ t => Abs _ _ (λ o, match o with Space _ z => Space _ (σ x) | Point _ => Point _ end)
  | App _ _ t1 t2 => App _ _ (σ t1) (σ t2)
  end). *)

Fixpoint σ (Γ : UU) (t : Term Id Γ) (p : P Γ) {struct t} : A Γ :=
  match t with
  | Var _ _ _ => ϵ Γ p
  | Sig _ _ x => (*ϕ Γ (Σm _ _ Γ σ x)*) ϵ Γ p
  end.

End Parameterised_Initiality.

Definition compose : ∏ Γ : UU, Term Id Γ → Term Id Γ → Term Id Γ :=
  σ (Term Id) (Term Id) (λ _ x, x).

Definition substitute (Γ Γ' : UU) (t : Term Id Γ') (s : Γ' -> Term Id Γ) (f : Γ' -> Term Id Γ) : Term Id Γ.
Proof.
  Check (∏ x, f x).
  Check (λ x, f x).
  Check Term_st Id Γ' (λ x, f x).
  Check
