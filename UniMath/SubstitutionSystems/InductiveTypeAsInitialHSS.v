Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.SubstitutionSystems.LamFromBindingSig.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.

(*Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.SubstitutionSystems.LamFromBindingSig.
*)

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
  | Abs _ _ pt => 1(*TermSize pt*)
  | App _ _ t1 t2 => (*add 1 (add (TermSize t1) (TermSize t2))*) 1
  end.

Definition TermMap {Γ Γ' : UU} (ρ : Γ -> Γ') (t : Term IdVar Γ) := TermMap' (TermSize t) ρ t.

(* Taken from `LamHSET.v`. *)
Let Lam_S : Signature HSET has_homsets_HSET _ _ :=
Lam_Sig HSET has_homsets_HSET TerminalHSET BinCoproductsHSET BinProductsHSET.

Definition hss_precat := hss_precategory BinCoproductsHSET Lam_S.

Definition TermFunctorData : functor_data HSET HSET.
  exists (λ Γ, type_to_hset (Term IdVar (hset_to_type Γ))).
  exact (λ _ _ ρ, (λ t, TermMap ρ t)).
Defined.

(* hopefully we shouldn't need to prove this *)
Definition TermFunctorData_is_functor : is_functor TermFunctorData.
Proof. Admitted.

Definition TermFunctor : functor HSET HSET := mk_functor TermFunctorData TermFunctorData_is_functor.

Local Notation "'HSET2'":= [HSET, HSET, has_homsets_HSET].

(* Taken from SubstitutionSystems.v *)
Let BinCoproductsHSET2 : BinCoproducts HSET2 := BinCoproducts_functor_precat _ _ BinCoproductsHSET has_homsets_HSET.
Let Id_H : functor HSET2 HSET2 :=
  BinCoproduct_of_functors _ _ BinCoproductsHSET2 (constant_functor _ _ (functor_identity _ : HSET2)) LamSignature.

(* (Id_H TermFunctor) --> TermFunctor *)
Definition IHTFTF_map : nat_trans_data (pr1 (Id_H TermFunctor)) TermFunctor.
Proof.
  unfold nat_trans_data.
  intro S.
  intro t.
  simpl in t.
  destruct t as [v | t'].
  - exact (Var _ _ v).
  - destruct t' as [i ob].
    destruct i.
    + exact (Sig _ _ (App _ _ (pr1 ob) (pr2 ob))).
    + simpl in ob.
      exact (Sig _ _ (Abs _ _ ob)).
Defined.

(* we don't need to prove this... hopefully *)
Definition IHTFTF_is_nat_trans : is_nat_trans (pr1 (Id_H TermFunctor)) TermFunctor IHTFTF_map. Admitted.

Definition NatTran_Id_H_TermFunctor_to_TermFunctor : (Id_H TermFunctor) --> TermFunctor.
Proof.
  exists IHTFTF_map.
  exact IHTFTF_is_nat_trans.
Defined.

Definition IHTFTF_alg : algebra_ob Id_H.
Proof.
  exists TermFunctor.
  exact NatTran_Id_H_TermFunctor_to_TermFunctor.
Defined.

Definition subst (S : HSET) (t : Term IdVar (Term IdVar (hset_to_type S))) : Term IdVar (hset_to_type S).
(* this is the substitution we need to define *)
Admitted.

(* a natural transformation from the composite of a pointed functor with TermFunctor to TermFunctor *)
Definition pointed_term_composite_to_term_data (Z : precategory_Ptd HSET has_homsets_HSET) (f : Z --> ptd_from_alg IHTFTF_alg) : nat_trans_data (functor_composite (functor_from_ptd_obj _ Z) TermFunctor) TermFunctor.
Proof.
  intro S.
  simpl.
  intro t.
  pose (wrap := #TermFunctor (pr1 f S)).
  pose (sbst := subst S).
  exact (sbst (wrap t)).
Defined.

(* we probably don't need this *)
Definition PTCTT_is_nat_trans (Z : precategory_Ptd HSET has_homsets_HSET) (f : Z --> ptd_from_alg IHTFTF_alg) : is_nat_trans (functor_composite (functor_from_ptd_obj _ Z) TermFunctor) TermFunctor (pointed_term_composite_to_term_data Z f). Admitted.

Definition pointed_term_composite_to_term (Z : precategory_Ptd HSET has_homsets_HSET) (f : Z --> ptd_from_alg IHTFTF_alg) : functor_composite (functor_from_ptd_obj _ Z) TermFunctor ⟹ TermFunctor.
  exists (pointed_term_composite_to_term_data Z f).
  exact (PTCTT_is_nat_trans Z f).
Defined.

(* we can probably get away with not defining this *)
Definition PTCTT_bracket_property (Z : precategory_Ptd HSET has_homsets_HSET) (f : Z --> ptd_from_alg IHTFTF_alg) : bracket_property f (pointed_term_composite_to_term Z f). Admitted.

(* we can probably get away with not defining this *)
Definition PTCTT_uniq (Z : precategory_Ptd HSET has_homsets_HSET) (f : Z --> ptd_from_alg IHTFTF_alg) : ∏
t : ∑ h : functor_composite_data (pr1 Z) TermFunctorData ⟹ TermFunctorData,
    bracket_property f h,
t = pointed_term_composite_to_term Z f,, PTCTT_bracket_property Z f. Admitted.

Definition IHTFTF_alg_bracket : bracket IHTFTF_alg.
Proof.
  unfold bracket.
  intros Z f.
  unfold bracket_at.
  use tpair.
  - use tpair.
    + exact (pointed_term_composite_to_term Z f).
    + exact (PTCTT_bracket_property Z f).
  - exact (PTCTT_uniq Z f).
Defined.

Definition inductive_ob : hss_precategory BinCoproductsHSET LamSignature.
Proof.
  exists IHTFTF_alg.
  exact IHTFTF_alg_bracket.
Defined.

(* we're going to need to prove *some* of this *)
Definition inductive_ob_is_initial : isInitial (hss_precategory BinCoproductsHSET LamSignature) inductive_ob.
Proof.
  intro A.
  use tpair.
  (* a map from inductive_ob to A *)
  (* well, maybe we don't have to define it. it might not actually be used computationally... *)
Admitted.

Definition InductiveSignature : Initial (hss_precategory BinCoproductsHSET LamSignature).
Proof.
  exists inductive_ob.
  exact inductive_ob_is_initial.
Defined.
