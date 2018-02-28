Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.

Local Open Scope cat.

Section metasubstitution.

Local Notation "'endofunctor' C" := (functor C C) (at level 60).
Local Definition endofunctor_precategory (C : precategory) := functor_precategory C C.

(* The category (K, I, P) is a monoidal category. Here, we specifically set K = [HSET, HSET], I = Id_HSET and P = ∘. *)
Definition C := hset_precategory.
(* [C, C]. *)
Definition K := endofunctor_precategory C has_homsets_HSET.
(* Identity of the tensor product on K. *)
Definition I := functor_identity C.
(* Tensor product on K. *)
Definition P := @functor_composite C.

Local Definition hsC := has_homsets_HSET.
Local Definition hsK : has_homsets K := functor_category_has_homsets C C hsC.

Section msfunctor.

Context (X : endofunctor C) (HX : is_omega_cocont X).

Definition BinCoproductsC : BinCoproducts C := BinCoproductsHSET.

Definition BinCoproductsK : BinCoproducts K.
Proof.
apply (BinCoproducts_functor_precat _ _ BinCoproductsC).
Defined.

Definition BinProductsC : BinProducts C := BinProductsHSET.

Definition BinProductsK : BinProducts K.
Proof.
apply (BinProducts_functor_precat _ _ BinProductsC).
Defined.

(* X ∘ — *)
Definition X_precomp := pre_composition_functor C C C hsC hsC X.

(* ΔId_C *)
Definition const_I_functor := constant_functor K K I.

(* Id_C + X ∘ — *)
Definition F' := BinCoproduct_of_functors K K BinCoproductsK const_I_functor X_precomp.

Definition ColimsC_of_shape := ColimsHSET_of_shape.

Definition CLC : Colims_of_shape nat_graph C := ColimsC_of_shape nat_graph.

Lemma is_omega_cocont_X_precomp : is_omega_cocont X_precomp.
Proof.
    refine (is_omega_cocont_pre_composition_functor X hsC hsC CLC).
Defined.

Lemma is_omega_cocont_F' : is_omega_cocont F'.
Proof.
    refine (is_omega_cocont_BinCoproduct_of_functors BinCoproductsK hsK const_I_functor X_precomp _ _).
    refine (is_omega_cocont_constant_functor _ _).
    exact hsK.
    exact is_omega_cocont_X_precomp.
Defined.

Local Notation "'C2'" := [C, C, hsC].

Local Lemma InitialC : Initial C.
Proof.
    exact InitialHSET.
Defined.

Local Lemma InitialC2 : Initial C2.
Proof.
apply (Initial_functor_precat _ _ InitialC).
Defined.

Lemma F'_initial : Initial (precategory_FunctorAlg F' hsK).
Proof.
    apply (colimAlgInitial _ InitialC2 is_omega_cocont_F').
    apply ColimsFunctorCategory_of_shape; apply ColimsC_of_shape.
Defined.

(* F *)
Local Definition F : C2 := alg_carrier _ (InitialObject F'_initial).

Check F.

End msfunctor.

Local Definition List : endofunctor HSET.
Proof.
    refine (BinCoproduct_of_functors HSET HSET BinCoproductsHSET _ _).
    - exact (constant_functor HSET HSET (pr1 TerminalHSET)).
    - exact (functor_identity HSET).
Defined.

End metasubstitution.

Local Close Scope cat.
