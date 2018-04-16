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
Require Import UniMath.CategoryTheory.Monoidal.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.LamFromBindingSig.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.MetaSubstitutionSystems.MetaSubstitutionSystem.

Local Open Scope cat.

Local Notation "C ²" := (binprod_precat C C) (at level 10).

Definition tensor_product {C : precategory} := C² ⟶ C.

Section FΣMonoid_Definition.

(* C here is actually what we've been calling K (i.e. C ⟶ C)) *)

Context {C : precategory} (FΣ : endofunctor C) (T : C² ⟶ C) (I : C).

Local Notation "X ⊗ Y" := (T (X , Y)) (at level 31).
Local Notation "X ⊗# Y" := (#T (X #, Y)) (at level 31).

Check ∑ X : C, (X ⊗ X --> X) × (I --> X).

Definition monoid_ob : UU := ∑ X : C, (X ⊗ X --> X) × (I --> X).

Definition FΣMonoid_ob : UU := ∑ X : C,
    (FΣ X --> X) (* F-algebra morphism *)
  × ((X ⊗ X --> X) (* Monoid multiplication *)
  × (I --> X)). (* Monoid identity *)

(* We'll do the strength later. *)

(* Extract the FunctorAlgebra from the FΣMonoid. *)
Definition FΣMonoid_alg_ob (X : FΣMonoid_ob) : algebra_ob FΣ.
Proof.
    use tpair.
    - apply (pr1 X).
    - apply (pr1 (pr2 X)).
Defined.

Definition FΣMonoid_carrier (X : FΣMonoid_ob) : C := pr1 X.
Local Coercion FΣMonoid_carrier : FΣMonoid_ob >-> ob.

Definition FΣMonoid_map (X : FΣMonoid_ob) : (FΣ X --> X) := pr1 (pr2 X).

Definition FΣMonoid_coherence (X : FΣMonoid_ob) : (X ⊗ X --> X) × (I --> X) := pr2 (pr2 X).

Definition FΣMonoid_coher_mul (X : FΣMonoid_ob) := pr1 (FΣMonoid_coherence X).

Definition FΣMonoid_coher_id (X : FΣMonoid_ob) := pr2 (FΣMonoid_coherence X).

Definition FΣMonoid_monoid (X : FΣMonoid_ob) : monoid_ob := (pr1 X),, (pr2 (pr2 X)).

(* Definition FΣMonoid_subst (X : FΣMonoid_ob). *)

(* Morphisms. *)
Definition is_FΣMonoid_mor (X Y : FΣMonoid_ob) (f : FΣMonoid_carrier X --> FΣMonoid_carrier Y) : UU
    :=  (* F-algebra morphism condition. *)
        (is_algebra_mor FΣ (FΣMonoid_alg_ob X) (FΣMonoid_alg_ob Y) f)
        (* Monoid identity coherence condition. *)
      × (FΣMonoid_coher_id X) · f = (FΣMonoid_coher_id Y)
        (* Monoid multiplication coherence condition. *)
      × (FΣMonoid_coher_mul X) · f = (f ⊗# f) · (FΣMonoid_coher_mul Y).

Definition FΣMonoid_mor (X Y : FΣMonoid_ob) : UU := ∑ f : X --> Y, is_FΣMonoid_mor X Y f.
Local Coercion mor_from_FΣMonoid_mor (X Y : FΣMonoid_ob) (f : FΣMonoid_mor X Y) : X --> Y := pr1 f.

Definition FΣMonoid_alg_mor (X Y : FΣMonoid_ob) (f : FΣMonoid_mor X Y) : algebra_mor FΣ (FΣMonoid_alg_ob X) (FΣMonoid_alg_ob Y).
Proof.
    use tpair.
    - apply (pr1 f).
    - apply (pr1 (pr2 f)).
Defined.

(* The category of FΣ-Monoids. *)

Definition isaset_FΣMonoid_mor (hs : has_homsets C) (X Y : FΣMonoid_ob) : isaset (FΣMonoid_mor X Y).
Proof.
  apply (isofhleveltotal2 2).
  - apply hs.
  - intro f.
    apply isasetaprop.
    unfold is_FΣMonoid_mor.
    refine (isapropdirprod _ _ _ _).
    + apply hs.
    + admit. (* isaprop, which I don't get yet. *)
Admitted.

Definition FΣMonoid_mor_eq (hs : has_homsets C) {X Y : FΣMonoid_ob} {f g : FΣMonoid_mor X Y}
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro a.
  unfold is_FΣMonoid_mor.
  refine (isapropdirprod _ _ _ _).
  - apply hs.
  - admit. (* isaprop, which I don't get yet. *)
Admitted.

Definition FΣMonoid_mor_id (X : FΣMonoid_ob) : FΣMonoid_mor X X.
Proof.
    exists (identity _).
    unfold is_FΣMonoid_mor.
    split.
    - apply (pr2 (algebra_mor_id FΣ (FΣMonoid_alg_ob X))).
    - split.
      + rewrite id_right.
        apply idpath.
      + rewrite id_right.
        rewrite <- id_on_binprod_precat_pair_of_el.
        rewrite functor_id_id.
        * rewrite id_left.
          reflexivity.
        * reflexivity.
Defined.

Definition FΣMonoid_mor_comp (X Y Z : FΣMonoid_ob) (f : FΣMonoid_mor X Y) (g : FΣMonoid_mor Y Z) : FΣMonoid_mor X Z.
Proof.
    exists (f · g).
    unfold is_FΣMonoid_mor.
    split.
    - apply (pr2 (algebra_mor_comp FΣ (FΣMonoid_alg_ob X) (FΣMonoid_alg_ob Y) (FΣMonoid_alg_ob Z) (FΣMonoid_alg_mor X Y f) (FΣMonoid_alg_mor Y Z g))).
    - split.
      + rewrite assoc.
        rewrite <- (pr1 (pr2 (pr2 g))).
        rewrite <- (pr1 (pr2 (pr2 f))).
        apply idpath.
      + unfold mor_from_FΣMonoid_mor.
        rewrite assoc.
        rewrite (pr2 (pr2 (pr2 f))).
        rewrite <- assoc.
        rewrite (pr2 (pr2 (pr2 g))).
        rewrite assoc.
        rewrite <- binprod_precat_comp.
        rewrite functor_comp.
        reflexivity.
Defined.

Definition precategory_FΣMonoid_ob_mor : precategory_ob_mor.
Proof.
    exists FΣMonoid_ob.
    exact FΣMonoid_mor.
Defined.

Definition precategory_FΣMonoid_data : precategory_data.
Proof.
    exists precategory_FΣMonoid_ob_mor.
    exists FΣMonoid_mor_id.
    exact FΣMonoid_mor_comp.
Defined.

Lemma is_precategory_precategory_FΣMonoid_data (hs : has_homsets C)
  : is_precategory precategory_FΣMonoid_data.
Proof.
  repeat split; intros; simpl.
  - apply FΣMonoid_mor_eq.
    + apply hs.
    + apply id_left.
  - apply FΣMonoid_mor_eq.
    + apply hs.
    + apply id_right.
  - apply FΣMonoid_mor_eq.
    + apply hs.
    + apply assoc.
Qed.

Definition precategory_FΣMonoid (hs : has_homsets C)
  : precategory := tpair _ _ (is_precategory_precategory_FΣMonoid_data hs).

End FΣMonoid_Definition.

Local Notation FΣMonoid := precategory_FΣMonoid.

Section MuΣ_as_FΣMonoid.

(* In this section, C, K, I, P are from MetaSubstitutionSystem. *)

Print P.

(* In this section, MΣ := μA. I + X ⊗ A + FΣ(A) is an FΣ monoid *)

Context (FΣ : endofunctor K) (X : endofunctor C).

Check MuΣ FΣ X. (* C ⟶ C *)

Definition composition_tensor_product : K² ⟶ K. (* Need to define this. *)
Proof.
  admit.
Admitted.

(* Definition MΣ := MΣ FΣ. *)
Definition MΣ := MΣ FΣ.
Definition MuΣ := MuΣ FΣ.

Context (Z : C).

Check (pr1 (pr1 (MuΣ X))).

(* Specific FΣ monoid *)
Definition sp_FΣMonoid := FΣMonoid FΣ composition_tensor_product I hsK.

Local Notation "X ⊗ Y" := (composition_tensor_product (X , Y)) (at level 31).
Local Notation "X ⊗# Y" := (#composition_tensor_product (X #, Y)) (at level 31).

Check ob sp_FΣMonoid.

(* Prove that MuΣ is actually an FΣ-monoid. *)
Definition MuΣ_as_FΣMonoid : sp_FΣMonoid.
Proof.
  use tpair.
  - exact (pr1 (pr1 (MuΣ X))). (* i.e. ∀X. MΣ(X) is a functor C ⟶ C *)
  - split.
    + admit. (* F-algebra morphism *)
    + split.
      * admit. (* Monoid multiplication *)
      * (* Need to prove that I --> MΣ(X), by injection *)
      (* Given an initial algebra, there is injection from any element of chain into limit *)
      Check pr2 (pr2 (pr1 (MuΣ X))).
      * admit. (* Monoid identity *)
Admitted.
  (* Construct this: ∑ X : C,
    (FΣ X --> X) (* F-algebra morphism *)
  × ((X ⊗ X --> X) (* Monoid multiplication *)
  × (I --> X)). (* Monoid identity *) *)

(* Prove that MuΣ is an initial FΣ-monoid. *)

End MuΣ_as_FΣMonoid.
