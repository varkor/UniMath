Require Import UniMath.Foundations.PartD.

(* The tensor product for UU. *)
Inductive Tensor (A : UU) (B : UU) : UU :=
  | TensorPair : A -> B -> Tensor A B.
(* The unit for the tensor product. *)
Context (I : UU).
(* The metavariable object. *)
Context (M : UU).

Definition λ' {A : UU} (t : Tensor I A) : A :=
  let (_, a) := t in a.

(* The functor δ ≡ (-) + 1. *)
Inductive Option (A : UU) :=
  | Some : A -> Option A
  | None : Option A
  .
Definition Option_map {A B : UU} (o : Option A) (f : A -> B) : Option B :=
  match o with
  | Some _ a => Some _ (f a)
  | None _ => None _
  end.

(* A single level of the untyped λ-calculus with no free variables. *)
Inductive Σ (T : UU -> UU) (V : UU) : UU :=
  | Abs : T (Option V) -> Σ T V
  | App : (T V) -> (T V) -> Σ T V
  .
(* Definition Σ_map {A B : UU} (T : UU -> UU) (f : A -> B) (s : Σ T A) : Σ T B :=
  match s with
  | Abs _ _ o => Abs _ _ (Option_map o f)
  | App _ _ v1 v2 => App _ _ (f v1) (f v2)
  end. *)

(* The untyped λ-calculus with variables and metavariables as an inductive type (i.e. the initial algebra of the functor (ΔI + Σ + M ⊗)). *)
Inductive μ (V : UU) : UU :=
  | (* ɛ *) Var : V -> μ V
  | (* φ *) μΣ : Σ (μ V) -> (μ V)
  | (* ϰ *) Metavar : Tensor M (μ V) -> (μ V)
  .

(* The strength for Σ. *)
Definition s {X Y : UU} (t : Tensor (Σ X) Y) : Σ (Tensor X Y) :=
  let (sx, y) := t in Σ_map (λ v, TensorPair _ _ v y) sx.

Section Parameterised_Initiality.
(* Parameterised initiality for μ. *)
Context (A P : UU).
Context (ϵ : P -> A).
Context (ϕ : Σ A -> A).
Context (κ : Tensor M A -> A).

(* We'd prefer to take μ ⊗ P here, but `Fixpoint` doesn't like that, so we're implicitly using the monoidal isomorphisms here. *)
Fixpoint σ (m : μ I) (p : P) {struct m} : A :=
  match m with
  | Var _ _ => ϵ p
  | μΣ _ sm => (*ϕ (Σ_map (λ (t: Tensor μ P),

    let (a, b) := t in σ a b

  ) (s (TensorPair _ _ sm p)))*)
  ϵ p
  | Metavar _ (TensorPair _ _ mv x) => κ (TensorPair _ _ mv (σ x p))
  end.

End Parameterised_Initiality.

Check σ.

Definition mult := σ (μ I) (μ I) (λ m, m) (Metavar _) (* should need φ too *).
Check mult.

Context (a b c : I).

Compute mult (Var _ a) (Var _ b).


(* Fixpoint σ (t : Tensor μ P) {struct t} : A :=
  let (m, p) := t in match m with
  | Var _ => ϵ p
  | μΣ sm => (*ϕ (Σ_map σ (s (TensorPair _ _ sm p)))*) ϵ p
  | Metavar (TensorPair _ _ mv x) => κ (TensorPair _ _ mv (σ (TensorPair _ _ x p)))
  end. *)

(* A single level of the untyped λ-calculus with no free variables. *)
Inductive Σ (V : UU) : UU :=
  | Abs : Option V -> Σ V
  | App : V -> V -> Σ V
  .

(* The untyped λ-calculus with variables and metavariables as an inductive type (i.e. the initial algebra of the functor Δ). *)
Inductive Δμ : UU :=
  | (* ɛ *) Var : I -> Δμ
  | (* φ *) μΣ : Σ Δμ -> Δμ
  | (* ϰ *) Metavar : Tensor M Δμ -> Δμ
  .
