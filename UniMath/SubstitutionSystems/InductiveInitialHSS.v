Require Import UniMath.Foundations.PartD.
Require Import UniMath.SubstitutionSystems.LiftingInitial_generalised.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.

Require Import UniMath.SubstitutionSystems.LamHSET.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import  UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.SubstitutionSystems.LamFromBindingSig.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration_alt.

Local Open Scope cat.

(*
  An axiom allowing us to use native Coq inductive definitions as HSETs. This should be sound for the inductive types we define. Besides, UniMath uses type-in-type.
*)
Definition types_are_sets (X : UU) : isaset X. Admitted.
 Definition type_to_hset (X : UU) : HSET := (X,, types_are_sets X).
 Definition hset_to_type (S : HSET) : UU := pr1hSet S.
 (* Definition hset_map_to_fn {S T : HSET} (u : S --> T) : hset_to_type S -> hset_to_type T := u.
 Definition fn_to_hset_map {X Y : UU} (f : X -> Y) : type_to_hset X --> type_to_hset Y := f. *)
 (* The untyped λ-calculus as an inductive type. *)
 Inductive Σ (T : UU -> UU) (Γ : UU) :=
  | Abs : T (unit ⨿ Γ) -> Σ T Γ
  | App : T Γ -> T Γ -> Σ T Γ
  .
Inductive Term (V : UU -> UU) (Γ : UU) :=
  | Var : V Γ -> Term V Γ
  | Sig : Σ (Term V) Γ -> Term V Γ
  .
 Definition IdVar := (λ X : UU, X).
 (* we can replace this with coprod_rect or something *)
Definition PointedMap {Γ Γ' : UU} (ρ : Γ -> Γ') (pt : unit ⨿ Γ) : unit ⨿ Γ' :=
  match pt with
  | inr ctx => inr (ρ ctx)
  | inl tt => inl tt
  end.
 (* We're defining fixpoints, without proving that they're actually total. For now we simply assert that they are, but later we will come back and prove this. *)
Definition unreachable {T : UU} : T. Admitted.
 Fixpoint SigMap' (size : nat) {Γ Γ' : UU} (ρ : Γ -> Γ') (s : Σ (Term IdVar) Γ) {struct size} : Σ (Term IdVar) Γ' :=
  match size with
  | O => unreachable
  | S n => match s with
    | Abs _ _ pt => Abs _ _ (TermMap' n (PointedMap ρ) pt)
    | App _ _ t1 t2 => App _ _ (TermMap' n ρ t1) (TermMap' n ρ t2)
    end
  end
 (* The functor map for `Term IdVar`. *)
with TermMap' (size : nat) {Γ Γ' : UU} (ρ : Γ -> Γ') (t : Term IdVar Γ) {struct size} : Term IdVar Γ' :=
  match size with
  | O => unreachable
  | S n => match t with
    | Var _ _ ctx => Var _ _ (ρ ctx)
    | Sig _ _ sig => Sig _ _ (SigMap' n ρ sig)
    end
  end.
 Fixpoint TermSize {Γ : UU} (t : Term IdVar Γ) {struct t} : nat :=
  match t with
  | Var _ _ _ => 1
  | Sig _ _ sig => add 1 (SigSize sig)
  end
 with SigSize {Γ : UU} (s : Σ (Term IdVar) Γ) {struct s} : nat :=
  match s with
  | Abs _ _ pt => (*TermSize pt*) 1
  | App _ _ t1 t2 => (*add 1 (add (TermSize t1) (TermSize t2))*) 1
  end.
 Definition TermMap {Γ Γ' : UU} (ρ : Γ -> Γ') (t : Term IdVar Γ) : Term IdVar Γ' := TermMap' (TermSize t) ρ t.
Definition SigMap {Γ Γ' : UU} (ρ : Γ -> Γ') (s : Σ (Term IdVar) Γ) : Σ (Term IdVar) Γ' := SigMap' (SigSize s) ρ s.

Definition TermFunctorData : functor_data HSET HSET.
  exists (λ Γ, type_to_hset (Term IdVar (hset_to_type Γ))).
  exact (λ _ _ ρ, (λ t, TermMap ρ t)).
Defined.

 (* hopefully we shouldn't need to prove this *)
Definition TermFunctorData_is_functor : is_functor TermFunctorData.
Proof. Admitted.

Definition TermFunctor : functor HSET HSET := mk_functor TermFunctorData TermFunctorData_is_functor.

Let Id_H' := (LiftingInitial_generalised.Id_H HSET has_homsets_HSET BinCoproductsHSET
Lam_S).

 (* (Id_H TermFunctor) --> TermFunctor *)
Definition IHTFTF_map : nat_trans_data (pr1 (Id_H' TermFunctor)) TermFunctor.
Proof.
  intros S t.
  simpl in t.
  destruct t as [v | t'].
  - exact (Var _ _ v).
  - destruct t' as [i | j].
    destruct i.
    + exact (Sig _ _ (App _ _ pr1 pr2)).
    + exact (Sig _ _ (Abs _ _ j)).
Defined.
 (* we don't need to prove this... hopefully *)
Definition IHTFTF_is_nat_trans : is_nat_trans (pr1 (Id_H' TermFunctor)) TermFunctor IHTFTF_map. Admitted.
 Definition NatTran_Id_H_TermFunctor_to_TermFunctor : (Id_H' TermFunctor) --> TermFunctor.
Proof.
  exists IHTFTF_map.
  exact IHTFTF_is_nat_trans.
Defined.
 Definition IHTFTF_alg : algebra_ob Id_H'.
Proof.
  exists TermFunctor.
  exact NatTran_Id_H_TermFunctor_to_TermFunctor.
Defined.

Definition LamHSS_Initial_HSET : Initial (hss_precategory BinCoproductsHSET Lam_S).
Proof.
apply InitialHSS.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- apply is_omega_cocont_Lam_S.
- exact IHTFTF_alg.
Defined.

Definition LamMonad : Monad HSET.
Proof.
use Monad_from_hss.
- apply has_homsets_HSET.
- apply BinCoproductsHSET.
- apply Lam_S.
- apply LamHSS_Initial_HSET.
Defined.

(* Check LamMonad.

Check μ LamMonad.
Check pr2 (pr1 LamMonad) emptyHSET. *)

(* λ x. x *)
Let lambda_x_x := Sig IdVar ∅ (Abs _ _ (Var _ _ (inl tt))).

(* λ x. x *)
Let lambda_z_z := Sig IdVar (Term IdVar ∅) (Abs _ _ (Var _ _ (inl tt))).

(* [λ x. [λ z. x] x] *)
Let lambda_x_z_x_x := Sig IdVar (Term IdVar ∅)
  (Abs _ _ (Sig _ _ (App _ _ (Sig _ _ (Abs _ _ (Var _ _ (inl tt)))) (Var _ _ (inl tt))))
  ).

Eval vm_compute in lambda_x_z_x_x.

Compute lambda_x_z_x_x.

(* Check μ LamMonad emptyHSET (lambda_x_z_x_x). *)

Check unit.

Definition compute_monad := hset_to_type (μ LamMonad emptyHSET (lambda_z_z)).

Check compute_monad.

(* Eval vm_compute in (μ LamMonad emptyHSET (lambda_z_z)). *)

(* Eval vm_compute in (μ LamMonad emptyHSET (lambda_x_z_x_x)). *)

(* Compute (μ LamMonad emptyHSET (lambda_x_z_x_x)). *)
