Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
(* Require Import UniMath.CategoryTheory.categories.category_hset_structures. *)
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
(* Require Import UniMath.CategoryTheory.PrecategoryBinProduct. *)
(* Require Import UniMath.CategoryTheory.CocontFunctors. *)
(* Require Import UniMath.CategoryTheory.whiskering. *)
Require Import UniMath.CategoryTheory.FunctorAlgebras.
(* Require Import UniMath.CategoryTheory.limits.bincoproducts. *)
(* Require Import UniMath.CategoryTheory.limits.binproducts. *)
(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)
(* Require Import UniMath.CategoryTheory.limits.initial. *)
Require Import UniMath.CategoryTheory.Monoidal.
(* Require Import UniMath.SubstitutionSystems.Signatures. *)
(* Require Import UniMath.SubstitutionSystems.BindingSigToMonad. *)
(* Require Import UniMath.SubstitutionSystems.LamFromBindingSig. *)
(* Require Import UniMath.SubstitutionSystems.LiftingInitial_alt. *)
(* Require Import UniMath.MetaSubstitutionSystems.MetaSubstitutionSystem. *)

Local Open Scope cat.

(* Assumed: monoidal categories *)
Require Import UniMath.CategoryTheory.Monoidal.
(* Required for # *)
Require Import UniMath.CategoryTheory.functor_categories.

(* Parametrised algebras *)
(* Omitted for brevity. We shall use nonparametrised algebras instead. *)

(* Parametrised initial-algebra functors *)
(* Omitted for brevity. We shall use nonparametrised initial-algebra functors instead. *)

(* Tensorial strength *)

(* Generalisation of theta in Signatures.v *)

(* (Σ, s)-Mon *)

(* Useful notation. *)
Notation "'endofunctor' C" := (functor C C) (at level 60).

Section Category_Σ_s_Mon.

(* Definition *)

Context (Mon : monoidal_precat). (* A monoidal precategory (C, I, ⊗). *)

Let C := monoidal_precat_to_precat Mon.
Let I := monoidal_precat_to_unit Mon.
Notation "X ⊗ Y" := ((monoidal_precat_to_tensor Mon) (X , Y)) (at level 31).
Notation "X #⊗ Y" := (#(monoidal_precat_to_tensor Mon) (X #, Y)) (at level 31).
Let α := monoidal_precat_to_associator Mon.
Let λ' := monoidal_precat_to_left_unitor Mon.
Let ρ := monoidal_precat_to_right_unitor Mon.

Context (Σ: endofunctor C).

Let tensorial_strength : UU :=
	∏ (Q : C × ∑ (X : C), I --> X), Σ (pr1 Q) ⊗ (pr1 (pr2 Q)) --> Σ ((pr1 Q) ⊗ (pr1 (pr2 Q))).

Context (s : tensorial_strength).

Definition monoid_ob_data : UU :=
  ∑ X : C, (X ⊗ X --> X) × (I --> X).

Definition is_monoid_ob (X : C) (μ : X ⊗ X --> X) (η : I --> X) : UU :=
	(μ #⊗ identity X · μ = pr1 α ((X, X), X) · identity X #⊗ μ · μ) × (* Pentagon diagram *)
	(pr1 (pr1 λ' X) = η #⊗ identity X · μ) × (pr1 (pr1 ρ X) = identity X #⊗ η · μ). (* Unitor diagrams *)

Definition monoid_ob : UU :=
	∑ X : monoid_ob_data, is_monoid_ob (pr1 X) (pr1 (pr2 X)) (pr2 (pr2 X)).

Definition monoid_carrier (X : monoid_ob) : C := pr1 (pr1 X).
Local Coercion monoid_carrier : monoid_ob >-> ob.

Definition monoid_mult (X : monoid_ob) := pr1 (pr2 (pr1 X)).

Definition monoid_unit (X : monoid_ob) := pr2 (pr2 (pr1 X)).

Definition is_monoid_mor (X Y : monoid_ob) (f : monoid_carrier X --> monoid_carrier Y) : UU :=
	((@monoid_mult X) · f = f #⊗ f · (@monoid_mult Y)) ×
  (@monoid_unit X) · f = (@monoid_unit Y).

Definition monoid_mor (X Y : monoid_ob) : UU :=
  ∑ f : X --> Y, is_monoid_mor X Y f.
Coercion mor_from_monoid_mor (X Y : monoid_ob) (f : monoid_mor X Y) : X --> Y := pr1 f.

Definition isaset_monoid_mor (hs : has_homsets C) (X Y : monoid_ob) : isaset (monoid_mor X Y).
Proof.
  apply (isofhleveltotal2 2).
  - apply hs.
  - intro.
    apply isasetaprop.
    unfold is_monoid_mor.
    refine (isapropdirprod _ _ _ _); apply hs.
Qed.

Definition monoid_mor_eq (hs : has_homsets C) {X Y : monoid_ob} {f g : monoid_mor X Y} : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro.
  unfold is_monoid_mor.
  refine (isapropdirprod _ _ _ _); apply hs.
Defined.

Definition monoid_mor_id (X : monoid_ob) : monoid_mor X X.
Proof.
  exists (identity _ ).
  unfold is_monoid_mor.
  rewrite id_right.
  rewrite <- id_on_binprod_precat_pair_of_el.
  rewrite functor_id.
  rewrite id_left.
  rewrite id_right.
  split; apply idpath.
Defined.

Set Printing All.

(* Coq's unification algorithm is utterly, thoroughly useless. It fails at unifying the most obviously-identical terms. That's why I've extracted this totally meaningless lemma, because Coq will not accept it otherwise. What a completely awful language/compiler. *)
Lemma monoid_mor_commutes_1 (X Y : monoid_ob) (f : monoid_mor X Y) : monoid_mult X · f = f #⊗ f · monoid_mult Y.
Proof.
  exact (pr1 (pr2 f)).
Qed.

Lemma monoid_mor_commutes_2 (X Y Z : monoid_ob) (f : monoid_mor X Y) (g : monoid_mor Y Z) : f #⊗ f · (monoid_mult Y · g) = f #⊗ f · (g #⊗ g · monoid_mult Z).
Proof.
	rewrite monoid_mor_commutes_1.
	reflexivity.
Qed.

Definition monoid_mor_comp (X Y Z : monoid_ob) (f : monoid_mor X Y) (g : monoid_mor Y Z) : monoid_mor X Z.
Proof.
	use tpair.
	- exact (f · g).
	- split.
		+ rewrite assoc.
			rewrite monoid_mor_commutes_1.
			rewrite <- assoc.
			rewrite <- binprod_precat_comp.
			rewrite functor_comp.
			rewrite monoid_mor_commutes_2.
			rewrite assoc.
			reflexivity.
		+ rewrite assoc.
			rewrite <- (pr2 (pr2 g)).
			rewrite <- (pr2 (pr2 f)).
			apply idpath.
Defined.

Definition Σs_mon_coher (X : C) (μ : X ⊗ X --> X) (ι : I --> X) (χ : Σ X --> X) : UU :=
	χ #⊗ identity X · μ = s (X,, (X,, ι)) · #Σ μ · χ.

Definition Σs_mon_ob_data : UU :=
	∑ X : C, (X ⊗ X --> X) × (I --> X) × Σ X --> X.

Definition Σs_mon_carrier (X : Σs_mon_ob_data) : C := pr1 X.
Local Coercion Σs_mon_carrier : Σs_mon_ob_data >-> ob.

Definition Σs_mon_mult {X : Σs_mon_ob_data} := pr1 (pr2 X).

Definition Σs_mon_unit {X : Σs_mon_ob_data} := pr1 (pr2 (pr2 X)).

Definition Σs_mon_map {X : Σs_mon_ob_data} := pr2 (pr2 (pr2 X)).

Definition Σs_mon_alg_ob (X : Σs_mon_ob_data) : algebra_ob Σ.
Proof.
	use tpair.
	- exact (Σs_mon_carrier X).
	- exact Σs_mon_map.
Defined.

Definition is_Σs_mon_ob (X : C) (μ : X ⊗ X --> X) (ι : I --> X) (χ : Σ X --> X) : UU :=
	(is_monoid_ob X μ ι) × (Σs_mon_coher X μ ι χ).

Definition Σs_mon_ob : UU :=
	∑ X : Σs_mon_ob_data, is_Σs_mon_ob (Σs_mon_carrier X) Σs_mon_mult Σs_mon_unit Σs_mon_map.

Definition Σs_mon_ob_to_data (X : Σs_mon_ob) : Σs_mon_ob_data := pr1 X.
Local Coercion Σs_mon_ob_to_data : Σs_mon_ob >-> Σs_mon_ob_data.

Definition Σs_mon_monoid_ob (X : Σs_mon_ob) : monoid_ob.
Proof.
	use tpair.
	- use tpair.
		+ exact (Σs_mon_carrier X).
		+ use tpair.
			* exact Σs_mon_mult.
			* exact Σs_mon_unit.
	- exact (pr1 (pr2 X)).
Defined.

Definition is_Σs_mon_mor (X Y : Σs_mon_ob) (f : Σs_mon_carrier X --> Σs_mon_carrier Y) : UU :=
	(is_algebra_mor Σ (Σs_mon_alg_ob X) (Σs_mon_alg_ob Y) f) ×
	(is_monoid_mor (Σs_mon_monoid_ob X) (Σs_mon_monoid_ob Y) f).

Definition Σs_mon_mor (X Y : Σs_mon_ob) : UU :=
	∑ f : X --> Y, is_Σs_mon_mor X Y f.
Coercion mor_from_Σs_mon_mor (X Y : Σs_mon_ob) (f : Σs_mon_mor X Y) : X --> Y := pr1 f.

Definition Σs_mon_monoid_mor {X Y : Σs_mon_ob} (f : Σs_mon_mor X Y) : monoid_mor (Σs_mon_monoid_ob X) (Σs_mon_monoid_ob Y).
Proof.
	use tpair.
	- exact f.
	- exact (pr2 (pr2 f)).
Defined.

Definition Σs_mon_alg_mor {X Y : Σs_mon_ob} (f : Σs_mon_mor X Y) : algebra_mor Σ (Σs_mon_alg_ob X) (Σs_mon_alg_ob Y).
Proof.
	use tpair.
	- exact f.
	- exact (pr1 (pr2 f)).
Defined.

Definition isaset_Σs_mon_mor (hs : has_homsets C) (X Y : Σs_mon_ob) : isaset (Σs_mon_mor X Y).
Proof.
	(* This is essentially inlining `isaset_algebra_mor` and `isaset_monoid_mor`, which is horrible, but I spent too long trying to figure out how to map them correctly. *)
  apply (isofhleveltotal2 2).
		- apply hs.
		- intro.
			apply isasetaprop.
			unfold is_Σs_mon_mor.
			refine (isapropdirprod _ _ _ _).
			+ apply hs.
			+ unfold is_monoid_mor.
			refine (isapropdirprod _ _ _ _); apply hs.
Qed.

Definition Σs_mon_mor_eq (hs : has_homsets C) {X Y : Σs_mon_ob} {f g : Σs_mon_mor X Y}
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro a.
  unfold is_Σs_mon_mor.
  refine (isapropdirprod _ _ _ _).
  - apply hs.
  - unfold is_monoid_mor.
    refine (isapropdirprod _ _ _ _); apply hs.
Defined.

Definition Σs_mon_mor_id (X : Σs_mon_ob) : Σs_mon_mor X X.
Proof.
	exists (identity _).
	unfold is_Σs_mon_mor.
	split.
  - apply (pr2 (algebra_mor_id Σ (Σs_mon_alg_ob X))).
	- apply (pr2 (monoid_mor_id (Σs_mon_monoid_ob X))).
Defined.

Definition Σs_mon_mor_comp (X Y Z : Σs_mon_ob) (f : Σs_mon_mor X Y) (g : Σs_mon_mor Y Z) : Σs_mon_mor X Z.
Proof.
	exists (f · g).
	unfold is_Σs_mon_mor.
	split.
	- apply (algebra_mor_comp Σ (Σs_mon_alg_ob X) (Σs_mon_alg_ob Y) (Σs_mon_alg_ob Z) (Σs_mon_alg_mor f) (Σs_mon_alg_mor g)).
	- apply (monoid_mor_comp (Σs_mon_monoid_ob X) (Σs_mon_monoid_ob Y) (Σs_mon_monoid_ob Z) (Σs_mon_monoid_mor f) (Σs_mon_monoid_mor g)).
Defined.

Definition precategory_Σs_mon_ob_mor : precategory_ob_mor.
Proof.
	exists Σs_mon_ob.
	exact Σs_mon_mor.
Defined.

Definition precategory_Σs_mon_data : precategory_data.
Proof.
	exists precategory_Σs_mon_ob_mor.
	exists Σs_mon_mor_id.
	exact Σs_mon_mor_comp.
Defined.

Lemma is_precategory_precategory_Σs_mon_data (hs : has_homsets C)
  : is_precategory precategory_Σs_mon_data.
Proof.
  repeat split; intros; simpl.
  - apply Σs_mon_mor_eq.
	+ apply hs.
	+ apply id_left.
  - apply Σs_mon_mor_eq.
	+ apply hs.
	+ apply id_right.
  - apply Σs_mon_mor_eq.
	+ apply hs.
	+ apply assoc.
Qed.

Definition precategory_Σs_mon (hs : has_homsets C)
  : precategory := tpair _ _ (is_precategory_precategory_Σs_mon_data hs).

End Category_Σ_s_Mon.