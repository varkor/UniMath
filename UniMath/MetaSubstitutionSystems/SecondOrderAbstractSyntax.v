Require Import UniMath.Foundations.PartD.
(* Require Import UniMath.Foundations.Sets. *)
Require Import UniMath.CategoryTheory.Categories.
(* Require Import UniMath.CategoryTheory.categories.category_hset. *)
(* Require Import UniMath.CategoryTheory.categories.category_hset_structures. *)
(* Require Import UniMath.CategoryTheory.functor_categories. *)
(* Require Import UniMath.CategoryTheory.ProductCategory. *)
(* Require Import UniMath.CategoryTheory.PrecategoryBinProduct. *)
Require Import UniMath.CategoryTheory.CocontFunctors.
(* Require Import UniMath.CategoryTheory.whiskering. *)
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
(* Require Import UniMath.CategoryTheory.limits.binproducts. *)
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.initial.
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
Require Import UniMath.MetaSubstitutionSystems.ParameterisedFunctorAlgebras.

(* Tensorial strength *)
Require Import UniMath.MetaSubstitutionSystems.ActionsAndStrengths.

(* (Σ, s)-Mon *)

(* Useful notation. *)
Notation "'endofunctor' C" := (functor C C) (at level 60).

(* Definition *)

Context (Mon : monoidal_precat). (* A monoidal precategory (C, I, ⊗). *)

Let C := monoidal_precat_to_precat Mon.
Let I := monoidal_precat_to_unit Mon.
Notation "X ⊗ Y" := ((monoidal_precat_to_tensor Mon) (X , Y)) (at level 31).
Notation "X #⊗ Y" := (#(monoidal_precat_to_tensor Mon) (X #, Y)) (at level 31).
Let α' := monoidal_precat_to_associator Mon.
Let λ' := monoidal_precat_to_left_unitor Mon.
Let ρ := monoidal_precat_to_right_unitor Mon.

Context (Σ: endofunctor C).

Let tensorial_strength : UU :=
	∏ (Q : C × ∑ (X : C), I --> X), Σ (pr1 Q) ⊗ (pr1 (pr2 Q)) --> Σ ((pr1 Q) ⊗ (pr1 (pr2 Q))).

(* we need to replace this with a parameterised strength soon *)
Context (s : tensorial_strength).

Section Category_Σ_s_Mon.

Definition monoid_ob_data : UU :=
  ∑ X : C, (X ⊗ X --> X) × (I --> X).

Definition is_monoid_ob (X : C) (μ : X ⊗ X --> X) (η : I --> X) : UU :=
	(μ #⊗ identity X · μ = pr1 α' ((X, X), X) · identity X #⊗ μ · μ) × (* Pentagon diagram *)
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

Definition rewrite_codom {C : precategory} (X X' Y : C) (f : X --> Y) (eq : X = X') : X' --> Y.
Proof.
	rewrite <- eq.
	assumption.
Defined.

Section Tensor_Preapplication_Functor.

Check functor_data.

Definition tensor_preapp_functor_data (X : Mon) : functor_data Mon Mon.
Proof.
	exists (λ Y, X ⊗ Y).
	exact (λ _ _ f, identity X #⊗ f).
Defined.

Definition is_functor_tensor_preapp (X : Mon) : is_functor (tensor_preapp_functor_data X).
Proof.
	split.
	- intro Y.
		simpl.
		rewrite <- id_on_binprod_precat_pair_of_el.
		rewrite (functor_id (monoidal_precat_to_tensor Mon)).
		reflexivity.
	- intros ? ? ? ? ?.
		simpl.
		rewrite <- (functor_comp (monoidal_precat_to_tensor Mon)).
		rewrite binprod_precat_comp.
		rewrite id_right.
		reflexivity.
Qed.

Definition tensor_preapp_functor (X : Mon) : functor _ _ :=
	tpair _ _ (is_functor_tensor_preapp X).

End Tensor_Preapplication_Functor.

Context (bin_coproduct : BinCoproducts C).

Definition dom {X Y : C} (f : X --> Y) := X.
Definition codom {X Y : C} (f : X --> Y) := Y.

Notation "X + Y" := (bin_coproduct X Y).
Notation "f #+ g" := (BinCoproductOfArrows C (bin_coproduct (dom f) (dom g)) (bin_coproduct (codom f) (codom g)) f g) (at level 41).

Section Σ_I_X_Algebra.

(* Assume our monoidal category (C, I, ⊗) has an initial object and binary coproducts. *)
Context (X : C) (Z : Initial C).

(* We're dealing with nonenriched categories here. *)
Context (has_homsets_C : has_homsets C).

(* Σ is also ω-cocontinuous by assumption. *)
Context (is_ω_cocont_Σ : is_omega_cocont Σ).

(* ΔI *)
Definition ΔI_functor := constant_functor C C I.

(* X ⊗ - *)
Definition X_preapp_functor := tensor_preapp_functor X.

(* Σ + ΔI + X ⊗ *)
Definition Σ_I_X_functor := tern_coprod_of_functors bin_coproduct Σ ΔI_functor X_preapp_functor.
Definition Σ_I_X := tern_coprod_of_functors_coprod Σ_I_X_functor.

Section Parameterised_Initial_Algebra.

Context (MX : FunctorAlg Σ_I_X has_homsets_C).
Let MX_ob := pr1 MX.
Let MX_map := pr2 MX.

Let ΣY_I (Y : C) := bin_coproduct (Σ Y) (ΔI_functor Y).
Let ΣY_I_XY (Y : C) := bin_coproduct (ΣY_I Y) (X_preapp_functor Y).

Let ΣY_Y (Y : C) := bin_coproduct (Σ Y) Y.
Let ΣY_Y_XY (Y : C) := bin_coproduct (ΣY_Y Y) (X_preapp_functor Y).

Definition opaque_coproduct_strength : UU :=
	∏ (W X Y Z : C), (W + X + Y) ⊗ Z --> (W ⊗ Z + X ⊗ Z + Y ⊗ Z).

Definition opaque_tensorial_strength : UU :=
	∏ (X Y : C), (Σ X) ⊗ Y --> Σ (X ⊗ Y).

Context (A : FunctorAlg Σ_I_X has_homsets_C).
Let A_ob := pr1 A.
Let A_map := pr2 A.

(* P is a pointed parameter. *)
Context (P : C) (basepoint_P : I --> P) (cs : opaque_coproduct_strength) (ts : opaque_tensorial_strength) (ψ : P --> A_ob) (ρ : MX_ob ⊗ P --> A_ob).

Definition τ_X (Y: FunctorAlg Σ_I_X has_homsets_C) : Σ (pr1 Y) --> (pr1 Y) :=
	pr1 (pr2 (pr1 (ΣY_I (pr1 Y)))) · pr1 (pr2 (pr1 (ΣY_I_XY (pr1 Y)))) · (pr2 Y).
Definition ɛ_X (Y: FunctorAlg Σ_I_X has_homsets_C) : I --> (pr1 Y) :=
	pr2 (pr2 (pr1 (ΣY_I (pr1 Y)))) · pr1 (pr2 (pr1 (ΣY_I_XY (pr1 Y)))) · (pr2 Y).
Definition α_X (Y: FunctorAlg Σ_I_X has_homsets_C) : X ⊗ (pr1 Y) --> (pr1 Y) :=
	pr2 (pr2 (pr1 (ΣY_I_XY (pr1 Y)))) · (pr2 Y).

(* [τ_X, 1_A, α_X] *)
Definition τ_X_1_A_α_X := pr1 (pr1 (pr2 (ΣY_Y_XY A_ob) A_ob (
	pr1 (pr1 (pr2 (ΣY_Y A_ob) A_ob (τ_X A) (identity A_ob)))
) (α_X A))).

Definition is_parameterised_initial : UU :=
	(* (ΣMX + I + X ⊗ MX) ⊗ P *)
	MX_map #⊗ (identity P) · (* or MX_map *)
	(* MX ⊗ MX *)
	ρ
	(* A *)

	=

	(* (ΣMX + I + X ⊗ MX) ⊗ P *)
	cs (Σ MX_ob) I (X ⊗ MX_ob) P ·
	(* ΣMX ⊗ P + I ⊗ P + X ⊗ MX ⊗ P *)
	ts MX_ob P #+ pr1 (pr1 λ' P) #+ pr1 α' ((X, MX_ob), P) ·
	(* Σ(MX ⊗ P) + P + X ⊗ (MX ⊗ P) *)
	#Σ ρ #+ ψ #+ (identity X) #⊗ ρ ·
	(* ΣA + A + X ⊗ A *)
	τ_X_1_A_α_X
	(* A *)
.

End Parameterised_Initial_Algebra.

Lemma is_ω_cocont_Σ_I_X : is_omega_cocont Σ_I_X.
Proof.
		refine (is_omega_cocont_BinCoproduct_of_functors bin_coproduct has_homsets_C _ _ _ _).
		- refine (is_omega_cocont_BinCoproduct_of_functors bin_coproduct has_homsets_C _ _ _ _).
			+ exact is_ω_cocont_Σ.
			+ exact (is_omega_cocont_constant_functor has_homsets_C _).
		- admit. (* preapp *)
Admitted.

(* The initial (Σ + ΔI + X ⊗)-algebra. *)
Definition MX : Initial (precategory_FunctorAlg Σ_I_X has_homsets_C).
Proof.
	apply (colimAlgInitial _ Z is_ω_cocont_Σ_I_X).
	(* some colims of shape stuff here *)
Admitted.

(* This actually comes from a strength, but we'll treat it as a distributor for now. *)
(* Context (δ_r : distributor_right). *)
Context (cs : opaque_coproduct_strength) (ts : opaque_tensorial_strength) (ς_X : ∏ (MX_ob : C), MX_ob ⊗ MX_ob --> MX_ob).

Check is_parameterised_initial.

Definition mk_is_parameterised_initial (MX : Initial (precategory_FunctorAlg Σ_I_X has_homsets_C)) : UU.
Proof.
	pose (init_alg := InitialObject MX).
	pose (init_ob := pr1 init_alg).
	exact (is_parameterised_initial init_alg init_alg init_ob cs ts (identity init_ob) (ς_X init_ob)).
Defined.

(* MX carries the structure of a (Σ, s)-monoid. *)
Theorem initial_Σ_I_X_algebra_is_Σs_mon (MX : Initial (precategory_FunctorAlg Σ_I_X has_homsets_C)) (ipi : mk_is_parameterised_initial MX) : Σs_mon_ob.
Proof.
	pose (MX_ob := (pr1 (InitialObject MX))).
  use tpair.
	- use tpair.
		+ exact MX_ob.
    + pose (ΣMX_I := bin_coproduct (Σ MX_ob) I). (* ΣMX + I *)
      pose (ΣMX_I_XMX := bin_coproduct (pr1 (pr1 ΣMX_I)) (X ⊗ MX_ob)). (* ΣMX + I + X ⊗ MX *)
      pose (ι_2 := pr1 (pr2 (pr1 ΣMX_I_XMX))). (* ΣMX + I --> ΣMX + I + X ⊗ MX *)
      pose (φ' := pr2 (InitialObject MX)). (* ΣMX + I + X ⊗ MX --> MX *)
      pose (coprod_functor_app := (BinCoproduct_of_functors_ob C C bin_coproduct (BinCoproduct_of_functors C C bin_coproduct Σ ΔI_functor) X_preapp_functor MX_ob)).
      assert (equal_codoms : coprod_functor_app = pr1 (pr1 ΣMX_I_XMX)) by reflexivity.
	  pose (φ := rewrite_codom coprod_functor_app (pr1 (pr1 ΣMX_I_XMX)) MX_ob φ' equal_codoms).
	  (* I --> ΣMX + I · ι_2 · φ *)
	  pose (ɛ := pr2 (pr2 (pr1 ΣMX_I)) · ι_2 · φ).
      split; [| split].
      * (* ς_X *)
        assert (initial_iso : iso (Σ_I_X MX_ob) MX_ob).
        -- use tpair.
           exact (pr2 (InitialObject MX)).
           exact (initialAlg_is_iso C has_homsets_C Σ_I_X (InitialObject MX) (pr2 MX)).
				-- exact (ς_X MX_ob).
      * (* ɛ_X *)
        exact ɛ.
      * (* τ_X *)
        pose (ι_1 := pr1 (pr2 (pr1 ΣMX_I))). (* I --> ΣMX + I *)
        exact (ι_1 · ι_2 · φ).
  - split; simpl.
    (* Σ-monoid structure *)
    + unfold is_monoid_ob.
      split; [| split].
      * admit. (* associative law *)
      * admit. (* left unit law *)
      * admit. (* right unit law *)
    + admit.
Admitted.

End Σ_I_X_Algebra.