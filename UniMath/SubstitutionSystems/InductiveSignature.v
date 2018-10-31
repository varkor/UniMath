Require Import UniMath.Foundations.PartD.

(* The tensor product for UU. *)
Inductive Tensor (A : UU) (B : UU) : UU :=
  | TensorPair : A -> B -> Tensor A B.
(* The unit for the tensor product. *)
Context (I : UU).
(* The metavariable object. *)
Context (M : UU).

(* The functor δ ≡ (-) + 1. *)
Inductive Option (A : UU) :=
  | Some : A -> Option A
  | None : Option A
  .

(* A single level of the untyped λ-calculus with no free variables. *)
Inductive Σ (V : UU) : UU :=
  | Abs : Option V -> Σ V
  | App : V -> V -> Σ V
  .

(* The untyped λ-calculus with variables and metavariables as an inductive type (i.e. the initial algebra of the functor (ΔI + Σ + M ⊗)). *)
Inductive μ : UU :=
  | (* ɛ *) Var : I -> μ
  | (* φ *) μΣ : Σ μ -> μ
  | (* ϰ *) Metavar : Tensor M μ -> μ
  .
