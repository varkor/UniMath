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
(* Omitted for brevity. We shall use nonparametrised algebras instead. *)

(* Parametrised initial-algebra functors *)
(* Omitted for brevity. We shall use nonparametrised initial-algebra functors instead. *)

(* Tensorial strength *)

(* Generalisation of theta in Signatures.v *)

(* (Σ, s)-Mon *)

(* Useful notation. *)
Notation "'endofunctor' C" := (functor C C) (at level 60).

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

Section Category_Σ_s_Mon.

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

Section Distributive_Monoidal_Category.

(* This should technically be an isomorphism (and a natural transformation on top of that), but it's unimportant for our purposes. *)
Definition distributor_left : UU :=
	∏ (X Y Z : C), X ⊗ (Y + Z) --> (X ⊗ Y + X ⊗ Z).

Definition distributor_right : UU :=
	∏ (X Y Z : C), (X + Y) ⊗ Z --> (X ⊗ Z + Y ⊗ Z).

Definition distributive_monoidal_struct : UU.
Proof.
Admitted.

Definition distributive_monoidal_precat : UU.
Proof.
Admitted.

End Distributive_Monoidal_Category.

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
Definition Σ_I_X_functor := BinCoproduct_of_functors C C bin_coproduct (BinCoproduct_of_functors C C bin_coproduct Σ ΔI_functor) X_preapp_functor.

Section Parameterised_Initial_Algebra.

Check bin_coproduct.

(* This definition is rough and not general enough, but hopefully suffices for what we want to prove here. *)

(* P is a pointed parameter. *)
Context (P : C) (δ_r : distributor_right).

(* The point of the parameter *)
Context (pt : I --> P).
(* We probably shouldn't need this... *)
Context (pt_inv : P --> I).

Lemma convert_codom (A A' B : C) (f: A --> B) (eq : A = A') : A' --> B.
Proof.
  rewrite <- eq.
  assumption.
Defined.

Lemma alt_map (MX : FunctorAlg Σ_I_X_functor has_homsets_C) (A : FunctorAlg Σ_I_X_functor has_homsets_C) (u : pr1 MX ⊗ P --> pr1 A) (f : Σ_I_X_functor (pr1 A) --> pr1 A) : codom (# Σ u #+ pt_inv) + codom (# (monoidal_precat_to_tensor Mon) (identity X #, u)) --> pr1 A.
Proof.
  unfold codom.
  simpl in f.
  repeat (unfold BinCoproduct_of_functors_ob in f; simpl in f).
  unfold C.
  assumption.
Defined.

Lemma alt_map2 (MX : FunctorAlg Σ_I_X_functor has_homsets_C) (A : FunctorAlg Σ_I_X_functor has_homsets_C) (u : pr1 MX ⊗ P --> pr1 A) (f : Σ_I_X_functor (pr1 MX) ⊗ P --> pr1 A) : (Σ (pr1 MX) + I + X ⊗ pr1 MX) ⊗ P --> pr1 A.
Proof.
  unfold codom.
  simpl in f.
  repeat (unfold BinCoproduct_of_functors_ob in f; simpl in f).
  unfold C.
  assumption.
Defined.

Definition is_parameterised_initial (MX : FunctorAlg Σ_I_X_functor has_homsets_C) : UU :=
	∏ (A : FunctorAlg Σ_I_X_functor has_homsets_C),
  ∑ (u : pr1 MX ⊗ P --> pr1 A),
  (alt_map2 MX A u (pr2 MX #⊗ identity P · u)) = (δ_r (Σ (pr1 MX) + I) (X ⊗ pr1 MX) P) ·
                             (δ_r (Σ (pr1 MX)) I P #+ identity ((X ⊗ pr1 MX) ⊗ P)) ·
                             (s (pr1 MX,, (P,, pt)) #+ pr1 (pr1 λ' P) #+ pr1 α ((X, pr1 MX), P)) ·
                             (#Σ u #+ pt_inv #+ (identity X) #⊗ u) ·
                             (alt_map MX A u (pr2 A)).

Definition parameterised_initial_algebra : UU :=
	∑ (MX : FunctorAlg Σ_I_X_functor has_homsets_C), is_parameterised_initial MX.

End Parameterised_Initial_Algebra.

Lemma is_ω_cocont_Σ_I_X : is_omega_cocont Σ_I_X_functor.
Proof.
		refine (is_omega_cocont_BinCoproduct_of_functors bin_coproduct has_homsets_C _ _ _ _).
		- refine (is_omega_cocont_BinCoproduct_of_functors bin_coproduct has_homsets_C _ _ _ _).
			+ exact is_ω_cocont_Σ.
			+ exact (is_omega_cocont_constant_functor has_homsets_C _).
		- admit. (* preapp *)
Admitted.

(* The initial (Σ + ΔI + X ⊗)-algebra. *)
Definition MX : Initial (precategory_FunctorAlg Σ_I_X_functor has_homsets_C).
Proof.
	apply (colimAlgInitial _ Z is_ω_cocont_Σ_I_X).
	(* some colims of shape stuff here *)
Admitted.

(* This actually comes from a strength, but we'll treat it as a distributor for now. *)
Context (δ_r : distributor_right).

Check is_parameterised_initial X δ_r.

(* MX carries the structure of a (Σ, s)-monoid. *)
Theorem initial_Σ_I_X_algebra_is_Σs_mon (MX : Initial (precategory_FunctorAlg Σ_I_X_functor has_homsets_C)) : Σs_mon_ob.
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
      split; [| split].
      * (* ς_X *)
        assert (initial_iso : iso (Σ_I_X_functor MX_ob) MX_ob).
        -- use tpair.
           exact (pr2 (InitialObject MX)).
           exact (initialAlg_is_iso C has_homsets_C Σ_I_X_functor (InitialObject MX) (pr2 MX)).
				-- Check (inv_from_iso initial_iso) #⊗ (identity MX_ob).
					 Check pr1 (pr1 λ' MX_ob). (* via I ⊗ MX *)

      * (* ɛ_X *)
        pose (ι_1 := pr2 (pr2 (pr1 ΣMX_I))). (* I --> ΣMX + I *)
			  exact (ι_1 · ι_2 · φ).
      * (* τ_X *)
        pose (ι_1 := pr1 (pr2 (pr1 ΣMX_I))). (* I --> ΣMX + I *)
        exact (ι_1 · ι_2 · φ).
  - split; simpl.
    (* Σ-monoid structure *)
    + unfold is_monoid_ob.
      split; [| split].

    + simpl.


Admitted.

End Σ_I_X_Algebra.