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

Notation "'id' X" := (identity X) (at level 30).

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

Definition tensor := monoidal_precat_to_tensor Mon.

Let C := monoidal_precat_to_precat Mon.
Let I := monoidal_precat_to_unit Mon.
Notation "X ⊗ Y" := (tensor (X , Y)) (at level 31).
Notation "f #⊗ g" := (# tensor (f #, g)) (at level 31, format "f #⊗ g").
Let α' := monoidal_precat_to_associator Mon.
Let λ' := monoidal_precat_to_left_unitor Mon.
Let ρ' := monoidal_precat_to_right_unitor Mon.

(* I don't know why the notation for #⊗ doesn't print, but it's really annoying. *)
Check identity (I ⊗ I) #⊗ identity I.

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
	(pr1 (pr1 λ' X) = η #⊗ identity X · μ) × (pr1 (pr1 ρ' X) = identity X #⊗ η · μ). (* Unitor diagrams *)

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

Local Definition ρ_ (X : C) := pr1 (pr1 ρ' X).
Local Definition λ_ (X : C) := pr1 (pr1 λ' X).
Local Definition α_ (X Y Z : C) := pr1 α' ((X, Y), Z).
Local Definition α'inv := inv_nat_iso α'.
Local Definition αinv_ (X Y Z : C) := pr1 α'inv ((X, Y), Z).

Definition opaque_coproduct_strength : UU :=
	∏ (W X Y Z : C), (W + X + Y) ⊗ Z --> (W ⊗ Z + X ⊗ Z + Y ⊗ Z).

Definition opaque_tensorial_strength : UU :=
	∏ (X Y : C), (Σ X) ⊗ Y --> Σ (X ⊗ Y).

Definition opaque_tensorial_strength_identity_law (st : opaque_tensorial_strength) : UU :=
  ∏ (X : C), (st X I) · #Σ (pr1 (pr1 ρ' X)) = pr1 (pr1 ρ' (Σ X)).

Definition opaque_tensorial_strength_assoc_law (st : opaque_tensorial_strength) : UU :=
  ∏ (A X Y : C), (st A (X ⊗ Y)) · #Σ (αinv_ A X Y) = (αinv_ (Σ A) X Y) · (st A X) #⊗ id Y · (st (A ⊗ X) Y).

Definition opaque_tensorial_strength_nat_tran_law (st : opaque_tensorial_strength) : UU :=
	∏ (A B A' B' : C) (f : A --> A') (g : B --> B'), st A B · #Σ (f #⊗ g) = #Σ f #⊗ g · st A' B'.

Context (A : FunctorAlg Σ_I_X has_homsets_C).
Let A_ob := pr1 A.
Let A_map := pr2 A.

(* P is a pointed parameter. *)
Context (P : C) (basepoint_P : I --> P) (cs : opaque_coproduct_strength) (ts : opaque_tensorial_strength) (ψ : P --> A_ob) (υ : MX_ob ⊗ P --> A_ob).

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
	υ
	(* A *)

	=

	(* (ΣMX + I + X ⊗ MX) ⊗ P *)
	cs (Σ MX_ob) I (X ⊗ MX_ob) P ·
	(* ΣMX ⊗ P + I ⊗ P + X ⊗ MX ⊗ P *)
	ts MX_ob P #+ pr1 (pr1 λ' P) #+ pr1 α' ((X, MX_ob), P) ·
	(* Σ(MX ⊗ P) + P + X ⊗ (MX ⊗ P) *)
	#Σ υ #+ ψ #+ (identity X) #⊗ υ ·
	(* ΣA + A + X ⊗ A *)
	τ_X_1_A_α_X
	(* A *)
.

End Parameterised_Initial_Algebra.

Section Parameterised_Initiality.

Context (MX : C) (φ : Σ MX --> MX) (e : I --> MX) (α : X ⊗ MX --> MX).

(* Really, we'd like to create this from actions (which are just the tensor product). *)
Context (st : opaque_tensorial_strength) (st_il : opaque_tensorial_strength_identity_law st) (st_al : opaque_tensorial_strength_assoc_law st) (st_ntl : opaque_tensorial_strength_nat_tran_law st).

Definition parameterised_initiality {A P : C} (a : Σ A --> A) (b : P --> A) (c : X ⊗ A --> A) (it : MX ⊗ P --> A) : UU :=
  (λ_ P · b = e #⊗ id P · it) ×
  (φ #⊗ id P · it = (st MX P) · #Σ it · a) ×
  (α #⊗ id P · it = (α_ X MX P) · id X #⊗ it · c)
  .

(* also need uniqueness *)
Definition is_parameterised_initial' {A P : C} (a : Σ A --> A) (b : P --> A) (c : X ⊗ A --> A) : UU :=
  ∃! it : MX ⊗ P --> A,
  parameterised_initiality a b c it.

Context (ipi : ∏ {A P : C} (a : Σ A --> A) (b : P --> A) (c : X ⊗ A --> A), is_parameterised_initial' a b c).
Local Definition app_ipi := @ipi MX MX φ (id MX) α.
Local Definition app_conds := pr2 (pr1 app_ipi).
Local Definition app := pr1 (pr1 app_ipi).

Definition monoid_λ_law : λ_ MX = e #⊗ identity MX · app.
Proof.
	pose (λ_tri_law := pr1 app_conds).
	rewrite id_right in λ_tri_law.
	exact λ_tri_law.
Defined.

Definition Σ_alg_law : φ #⊗ id MX · app = (st MX MX) · #Σ app · φ.
Proof.
  exact (pr1 (pr2 app_conds)).
Defined.

(* this can just be replaced with maponpaths *)
Definition post_comp_comm {a b c : C} {f g : a --> b} (eq : f = g) (h : b --> c) : (f · h = g · h).
Proof.
	rewrite eq.
	reflexivity.
Defined.

(* a specialisation of the coherence conditions for monoidal categories *)
Context (monoidal_precat_coherence_1 : pr1 ρ' I = pr1 λ' I).
Context (monoidal_precat_coherence_2 : α #⊗ id I · ρ_ MX = (α_ X MX I) · id X #⊗ ρ_ MX · α).
Context (monoidal_precat_coherence_3 : (αinv_ I MX MX) · λ_ MX #⊗ id MX = λ_ (MX ⊗ MX)).
Context (monoidal_precat_coherence_4 : α_ X MX (MX ⊗ MX) · id X #⊗ (αinv_ MX MX MX) = αinv_ (X ⊗ MX) MX MX · (α_ X MX MX) #⊗ id MX · (α_ X (MX ⊗ MX) MX)).

Definition monoid_ρ_law_1_1 : λ_ I · e = e #⊗ id I · ρ_ MX.
Proof.
	pose (ρ_nat_law := pr2 ρ' I MX e).
	rewrite monoidal_precat_coherence_1 in ρ_nat_law.
	symmetry.
	exact ρ_nat_law.
Defined.

Definition monoid_ρ_law_1_2 : φ #⊗ id I · ρ_ MX = (st MX I) · #Σ (ρ_ MX) · φ.
Proof.
	pose (ρ_nat_law := pr2 ρ' (Σ MX) MX φ).
	pose (st_id_φ := post_comp_comm (st_il MX) φ).
	symmetry.

	Lemma monoid_ρ_law_1_2' (ρ_nat_law : # (monoidal_precat_to_tensor Mon) (φ #, id monoidal_precat_to_unit Mon) · pr1 (pr1 ρ' MX) = pr1 (pr1 ρ' (Σ MX)) · φ) (st_id_φ : st MX I · # Σ (pr1 (pr1 ρ' MX)) · φ = pr1 (pr1 ρ' (Σ MX)) · φ) : st MX I · # Σ (ρ_ MX) · φ = # tensor (φ #, id I) · ρ_ MX.
	Proof.
		rewrite <- ρ_nat_law in st_id_φ.
		exact st_id_φ.
	Defined.
	exact (monoid_ρ_law_1_2' ρ_nat_law st_id_φ).
Defined.

Definition monoid_ρ_law_1_3 : α #⊗ id I · ρ_ MX = (α_ X MX I) · id X #⊗ ρ_ MX · α.
	(* this is a direct consequence of the coherence theorem for monoidal categories *)
	exact monoidal_precat_coherence_2.
Defined.

Definition functor_tensor_comp {a b a' b' : C} {f g : a --> b} {f' g' : a' --> b'} (eq : f = g) (eq' : f' = g') : (f #⊗ f' = g #⊗ g').
Proof.
	rewrite eq.
	rewrite eq'.
	reflexivity.
Defined.

Definition monoid_ρ_law_2_1 : λ_ I · e = e #⊗ id I · (id MX #⊗ e · app).
Proof.
	Definition triv_2_1 : id I #⊗ e · e #⊗ id MX = e #⊗ id I · id MX #⊗ e.
	Proof.
		repeat rewrite <- functor_comp.
		repeat rewrite binprod_precat_comp.
		rewrite id_left.
		rewrite id_right.
		reflexivity.
  Defined.
  pose (λ_nat_law := pr2 λ' I MX e).
  pose (app_a_law := monoid_λ_law).
  unfold λ_ in app_a_law.
  simpl in λ_nat_law.
  unfold dom_left_unitor_on_mor in λ_nat_law.
  simpl in λ_nat_law.
  unfold nat_iso_to_nat_trans in λ_nat_law.
  Definition monoid_ρ_law_2_1' (λ_nat_law : # (monoidal_precat_to_tensor Mon) (id monoidal_precat_to_unit Mon #, e) · pr1 (pr1 λ' MX) = pr1 (pr1 λ' I) · e) (app_a_law : pr1 (pr1 λ' MX) = # tensor (e #, id MX) · app) : (# (monoidal_precat_to_tensor Mon) (id monoidal_precat_to_unit Mon #, e) · # tensor (e #, id MX) · app = pr1 (pr1 λ' I) · e).
  Proof.
    rewrite app_a_law in λ_nat_law.
    rewrite assoc in λ_nat_law.
    exact λ_nat_law.
  Defined.
  pose (pent := monoid_ρ_law_2_1' λ_nat_law app_a_law).
  fold I in pent.
  fold tensor in pent.
  rewrite triv_2_1 in pent.
  symmetry.
  rewrite assoc.
  exact pent.
Defined.

Definition monoid_ρ_law_2_2 : φ #⊗ id I · (id MX #⊗ e · app) = st MX I · #Σ (id MX #⊗ e · app) · φ.
Proof.
	Local Definition triv_2_2 : φ #⊗ id I · id MX #⊗ e = #Σ (id MX) #⊗ e · φ #⊗ id MX.
	Proof.
		repeat rewrite <- functor_comp.
		repeat rewrite binprod_precat_comp.
		rewrite functor_id.
		repeat rewrite id_right.
		repeat rewrite id_left.
		reflexivity.
	Defined.
	pose (st_nat_law := st_ntl MX I MX MX (id MX) e).
	rewrite assoc.
	rewrite triv_2_2.
	rewrite <- assoc.
	rewrite <- assoc.
	Local Definition monoid_ρ_law_2_2' (st_nat_law : st MX I · # Σ (# tensor (id MX #, e)) = # tensor (# Σ (id MX) #, e) · st MX MX) : (# tensor (# Σ (id MX) #, e) · (# tensor (φ #, id MX) · app) = st MX I · # Σ (# tensor (id MX #, e)) · (# Σ app · φ)).
  Proof.
    rewrite st_nat_law.
    pose (app_a_law := pr1 (pr2 app_conds)).
		unfold app_ipi in app_a_law.
		simpl in app_a_law.
		rewrite <- assoc.
		rewrite <- assoc in app_a_law.
		unfold app.
		unfold app_ipi.
		Local Definition monoid_ρ_law_2_2'' (app_a_law : # tensor (φ #, id MX) · pr1 (pr1 (ipi MX MX φ (id MX) α)) = st MX MX · (# Σ (pr1 (pr1 (ipi MX MX φ (id MX) α))) · φ)) : (# tensor (# Σ (id MX) #, e) · (# tensor (φ #, id MX) · pr1 (pr1 (ipi MX MX φ (id MX) α))) = # tensor (# Σ (id MX) #, e) · (st MX MX · (# Σ (pr1 (pr1 (ipi MX MX φ (id MX) α))) · φ))).
		Proof.
			rewrite <- app_a_law.
			reflexivity.
		Defined.
		exact (monoid_ρ_law_2_2'' app_a_law).
  Defined.
  rewrite (functor_comp Σ).
  pose (monoid_ρ_law_2_2'' := monoid_ρ_law_2_2' st_nat_law).
  repeat rewrite assoc in monoid_ρ_law_2_2''.
  repeat rewrite assoc.
  exact monoid_ρ_law_2_2''.
Defined.

Definition monoid_ρ_law_2_3 : α #⊗ id I · (id MX #⊗ e · app) = (α_ X MX I) · id X #⊗ (id MX #⊗ e · app) · α.
Proof.
	Definition triv_1 : α · id MX = id X #⊗ id MX · α.
	Proof.
		rewrite id_right.
		rewrite <- id_on_binprod_precat_pair_of_el.
		rewrite functor_id.
		rewrite id_left.
		reflexivity.
	Defined.
	Definition triv_2 : id I · e = e · id MX.
	Proof.
		rewrite id_left.
		rewrite id_right.
		reflexivity.
	Defined.
	pose (tensor_id_law := functor_tensor_comp triv_1 triv_2).
	simpl in tensor_id_law.
	repeat rewrite <- binprod_precat_comp in tensor_id_law.
  repeat rewrite (functor_comp tensor) in tensor_id_law.
  pose (app_c_law := pr2 (pr2 app_conds)).
	unfold app_ipi in app_c_law.
  unfold α_ in app_c_law.
  pose (α_nat_law := pr2 α' ((X, MX), I) ((X, MX), MX) ((id X #, id MX) #, e)).
	pose (α_nat_law' := post_comp_comm α_nat_law (id X #⊗ app · α)).
	rewrite <- assoc in α_nat_law'.
  rewrite <- assoc in app_c_law.
  simpl in α_nat_law'.
  unfold dom_associator_on_mor, cod_associator_on_mor in α_nat_law'.
  simpl in α_nat_law'.
  unfold app in α_nat_law'.
  unfold app_ipi in α_nat_law'.
  fold tensor in α_nat_law'.
  Definition monoid_ρ_law_2_3' (app_c_law : # tensor (α #, id MX) · pr1 (pr1 (ipi MX MX φ (id MX) α)) = pr1 α' ((X, MX), MX) · (# tensor (id X #, pr1 (pr1 (ipi MX MX φ (id MX) α))) · α)) (α_nat_law' : # tensor (# tensor (id X #, id MX) #, e) · (pr1 α' ((X, MX), MX) · (# tensor (id X #, pr1 (pr1 (ipi MX MX φ (id MX) α))) · α)) = pr1 α' ((X, MX), I) · # tensor (id X #, # tensor (id MX #, e)) · (# tensor (id X #, pr1 (pr1 (ipi MX MX φ (id MX) α))) · α)) (tensor_id_law : # tensor (α #, id I) · # tensor (id MX #, e) = # tensor (# tensor (id X #, id MX) #, e) · # tensor (α #, id MX)) : (α #⊗ id I · id MX #⊗ e · app = (α_ X MX I) · id X #⊗ (id MX #⊗ e) · id X #⊗ app · α).
  Proof.
    rewrite <- app_c_law in α_nat_law'.
    rewrite assoc in α_nat_law'.
    Definition monoid_ρ_law_2_3'' (α_nat_law' : # tensor (# tensor (id X #, id MX) #, e) · # tensor (α #, id MX) · pr1 (pr1 (ipi MX MX φ (id MX) α)) = pr1 α' ((X, MX), I) · # tensor (id X #, # tensor (id MX #, e)) · (# tensor (id X #, pr1 (pr1 (ipi MX MX φ (id MX) α))) · α)) (tensor_id_law : # tensor (α #, id I) · # tensor (id MX #, e) = # tensor (# tensor (id X #, id MX) #, e) · # tensor (α #, id MX)) : (α #⊗ id I · id MX #⊗ e · app = (α_ X MX I) · id X #⊗ (id MX #⊗ e) · id X #⊗ app · α).
    Proof.
      rewrite <- tensor_id_law in α_nat_law'.
      rewrite assoc in α_nat_law'.
      exact α_nat_law'.
    Defined.
    exact (monoid_ρ_law_2_3'' α_nat_law' tensor_id_law).
  Defined.
  rewrite assoc.
  pose (monoid_ρ_law_2_3''' := monoid_ρ_law_2_3' app_c_law α_nat_law' tensor_id_law).
  Definition monoid_ρ_law_2_3'''' : (α_ X MX I · # tensor (id X #, # tensor (id MX #, e) · app) = α_ X MX I · (# tensor (id X #, # tensor (id MX #, e)) · # tensor (id X #, app))).
    rewrite <- functor_comp.
    rewrite binprod_precat_comp.
    rewrite id_left.
    reflexivity.
  Defined.
  Check monoid_ρ_law_2_3''''.
  rewrite monoid_ρ_law_2_3''''.
  rewrite assoc.
  exact monoid_ρ_law_2_3'''.
Defined.

Local Definition it2_ipi := @ipi MX I φ e α.
Local Definition it2 := pr1 it2_ipi.

Definition ρ_MX_as_it2 : parameterised_initiality φ e α (ρ_ MX).
Proof.
  exists monoid_ρ_law_1_1.
  exists monoid_ρ_law_1_2.
  exact monoid_ρ_law_1_3.
Defined.

Definition idMX_e_app_as_it2 : parameterised_initiality φ e α (id MX #⊗ e · app).
  exists monoid_ρ_law_2_1.
  exists monoid_ρ_law_2_2.
  exact monoid_ρ_law_2_3.
Defined.

Definition monoid_ρ_law : ρ_ MX = identity MX #⊗ e · app.
Proof.
  pose (ρ_is_it := pr2 it2_ipi ((ρ_ MX),, ρ_MX_as_it2)).
  pose (idMX_e_app_is_it := pr2 it2_ipi ((id MX #⊗ e · app),, idMX_e_app_as_it2)).
  rewrite <- idMX_e_app_is_it in ρ_is_it.
  exact (maponpaths pr1 ρ_is_it).
Defined.

Tactic Notation "force" "(" ident(name) ":" constr(type) ")" := assert (name' : type) by (exact name);
  clear name;
  rename name' into name.

Definition monoid_α_law_1_1 : λ_ (MX ⊗ MX) · app = e #⊗ id (MX ⊗ MX) · (id MX #⊗ app · app).
Proof.
  pose (λ_nat_law := pr2 λ' (MX ⊗ MX) MX app).
  pose (λ_mon_law := monoid_λ_law).
  simpl in λ_nat_law.
  unfold dom_left_unitor_on_mor in λ_nat_law.
  simpl in λ_nat_law.
  fold I tensor in λ_nat_law.
  unfold λ_ in λ_mon_law.
  pose (λ_mon_law' := maponpaths (λ x, id I #⊗ app · x) λ_mon_law).
  simpl in λ_mon_law'.
  force (λ_nat_law : (# tensor (id I #, app) · pr1 λ' MX = pr1 λ' (MX ⊗ MX) · app)).
  force (λ_mon_law' : (# tensor (id I #, app) · pr1 λ' MX = # tensor (id I #, app) · (# tensor (e #, id MX) · app))).
  rewrite λ_mon_law' in λ_nat_law.
  assert (triv : id I #⊗ app · (e #⊗ id MX · app) = e #⊗ id (MX ⊗ MX) · (id MX #⊗ app · app)) by
  (repeat rewrite assoc;
  repeat rewrite <- functor_comp;
  repeat rewrite binprod_precat_comp;
  repeat rewrite id_left;
  repeat rewrite id_right;
  reflexivity).
  rewrite triv in λ_nat_law.
  symmetry in λ_nat_law.
  exact λ_nat_law.
Defined.

Definition monoid_α_law_1_2 : φ #⊗ id (MX ⊗ MX) · (id MX #⊗ app · app) = st MX (MX ⊗ MX) · #Σ (id MX #⊗ app · app) · φ.
Proof.
  Definition monoid_α_law_1_2_triv : φ #⊗ id (MX ⊗ MX) · id MX #⊗ app = id (Σ MX) #⊗ app · φ #⊗ id MX.
  Proof.
    repeat rewrite <- functor_comp.
    repeat rewrite binprod_precat_comp.
    repeat rewrite id_left.
    repeat rewrite id_right.
    reflexivity.
  Defined.
  pose (st_nat_law := st_ntl MX (MX ⊗ MX) MX MX (id MX) app).
	pose (app_b_law := pr1 (pr2 app_conds)).
	simpl in app_b_law.
	pose (monoid_α_law_1_2_triv' := post_comp_comm monoid_α_law_1_2_triv app).
	unfold app in monoid_α_law_1_2_triv'.
	repeat rewrite <- assoc in monoid_α_law_1_2_triv'.
	Definition monoid_α_law_1_2' (monoid_α_law_1_2_triv' : # tensor (φ #, id (MX ⊗ MX)) · (# tensor (id MX #, pr1 (pr1 app_ipi)) · pr1 (pr1 app_ipi)) = # tensor (id Σ MX #, pr1 (pr1 app_ipi)) · (# tensor (φ #, id MX) · pr1 (pr1 app_ipi))) (app_b_law : # tensor (φ #, id MX) · pr1 (pr1 app_ipi) = st MX MX · # Σ (pr1 (pr1 app_ipi)) · φ) : (# tensor (φ #, id (MX ⊗ MX)) · (# tensor (id MX #, pr1 (pr1 app_ipi)) · pr1 (pr1 app_ipi)) = # tensor (id Σ MX #, pr1 (pr1 app_ipi)) · (st MX MX · # Σ (pr1 (pr1 app_ipi)) · φ)).
	Proof.
		rewrite app_b_law in monoid_α_law_1_2_triv'.
		exact monoid_α_law_1_2_triv'.
	Defined.
	pose (monoid_α_law_1_2'' := monoid_α_law_1_2' monoid_α_law_1_2_triv' app_b_law).
	rewrite functor_id in st_nat_law.
	unfold app in st_nat_law.
	repeat rewrite assoc in monoid_α_law_1_2''.
	Definition monoid_α_law_1_2''' (monoid_α_law_1_2'' : # tensor (φ #, id (MX ⊗ MX)) · # tensor (id MX #, pr1 (pr1 app_ipi)) · pr1 (pr1 app_ipi) = # tensor (id Σ MX #, pr1 (pr1 app_ipi)) · st MX MX · # Σ (pr1 (pr1 app_ipi)) · φ) (st_nat_law : st MX (MX ⊗ MX) · # Σ (# tensor (id MX #, pr1 (pr1 app_ipi))) = # tensor (id Σ MX #, pr1 (pr1 app_ipi)) · st MX MX) : (φ #⊗ id (MX ⊗ MX) · id MX #⊗ app · app = st MX (MX ⊗ MX) · #Σ (id MX #⊗ app) · #Σ app · φ).
	Proof.
		rewrite <- st_nat_law in monoid_α_law_1_2''.
		exact monoid_α_law_1_2''.
  Defined.
  rewrite (functor_comp Σ).
  repeat rewrite assoc.
	exact (monoid_α_law_1_2''' monoid_α_law_1_2'' st_nat_law).
Defined.

Definition monoid_α_law_1_3 : α #⊗ id (MX ⊗ MX) · (id MX #⊗ app · app) = α_ X MX (MX ⊗ MX) · (id X #⊗ (id MX #⊗ app · app)) · α.
Proof.
	Definition monoid_α_law_1_3_triv : α #⊗ id (MX ⊗ MX) · id MX #⊗ app = id (X ⊗ MX) #⊗ app · α #⊗ id MX.
	Proof.
		repeat rewrite <- functor_comp.
		repeat rewrite binprod_precat_comp.
		repeat rewrite id_left.
		repeat rewrite id_right.
		reflexivity.
	Defined.
	pose (α_nat_law := pr2 α' ((X, MX), MX ⊗ MX) ((X, MX), MX) ((id X #, id MX) #, app)).
	pose (app_c_law := pr2 (pr2 app_conds)).
	simpl in app_c_law.
	pose (monoid_α_law_1_3_triv' := post_comp_comm monoid_α_law_1_3_triv app).
	unfold app in monoid_α_law_1_3_triv'.
	repeat rewrite <- assoc in monoid_α_law_1_3_triv'.
	Definition monoid_α_law_1_3' (monoid_α_law_1_3_triv' : # tensor (α #, id (MX ⊗ MX)) · (# tensor (id MX #, pr1 (pr1 app_ipi)) · pr1 (pr1 app_ipi)) = # tensor (id (X ⊗ MX) #, pr1 (pr1 app_ipi)) · (# tensor (α #, id MX) · pr1 (pr1 app_ipi))) (app_c_law : # tensor (α #, id MX) · pr1 (pr1 app_ipi) = α_ X MX MX · # tensor (id X #, pr1 (pr1 app_ipi)) · α) : (# tensor (α #, id (MX ⊗ MX)) · (# tensor (id MX #, pr1 (pr1 app_ipi)) · pr1 (pr1 app_ipi)) = # tensor (id (X ⊗ MX) #, pr1 (pr1 app_ipi)) · (α_ X MX MX · # tensor (id X #, pr1 (pr1 app_ipi)) · α)).
	Proof.
		rewrite app_c_law in monoid_α_law_1_3_triv'.
		exact monoid_α_law_1_3_triv'.
	Defined.
	pose (monoid_α_law_1_3'' := monoid_α_law_1_3' monoid_α_law_1_3_triv' app_c_law).
	simpl in α_nat_law.
	unfold dom_associator_on_mor, cod_associator_on_mor in α_nat_law.
	simpl in α_nat_law.
	unfold app in α_nat_law.
	(* unfold app_ipi in α_nat_law. *)
	fold tensor in α_nat_law.
	repeat rewrite <- (functor_id tensor) in monoid_α_law_1_3''.
	repeat rewrite id_on_binprod_precat_pair_of_el in monoid_α_law_1_3''.
	repeat rewrite assoc in monoid_α_law_1_3''.
	symmetry in monoid_α_law_1_3''.
	unfold α_ in monoid_α_law_1_3''.
	Definition monoid_α_law_1_3''' (monoid_α_law_1_3'' : # tensor (# tensor (id X #, id MX) #, pr1 (pr1 app_ipi)) · pr1 α' ((X, MX), MX) · # tensor (id X #, pr1 (pr1 app_ipi)) · α = # tensor (α #, # tensor (id MX #, id MX)) · # tensor (id MX #, pr1 (pr1 app_ipi)) · pr1 (pr1 app_ipi)) (α_nat_law : # tensor (# tensor (id X #, id MX) #, pr1 (pr1 app_ipi)) · pr1 α' ((X, MX), MX) = pr1 α' ((X, MX), MX ⊗ MX) · # tensor (id X #, # tensor (id MX #, pr1 (pr1 app_ipi)))) : (α #⊗ id (MX ⊗ MX) · id MX #⊗ app · app = α_ X MX (MX ⊗ MX) · id X #⊗ (id MX #⊗ app) · id X #⊗ app · α).
	Proof.
		rewrite α_nat_law in monoid_α_law_1_3''.
		simpl in monoid_α_law_1_3''.
		unfold α_.
		unfold app.
		symmetry.
		rewrite <- (functor_id tensor).
		rewrite id_on_binprod_precat_pair_of_el.
		exact monoid_α_law_1_3''.
  Defined.
  assert (comp : # tensor (id X #, # tensor (id MX #, app)) · # tensor (id X #, app) = # tensor (id X #, # tensor (id MX #, app) · app)) by
  (rewrite <- functor_comp;
  rewrite binprod_precat_comp;
  rewrite id_left;
  reflexivity).
  rewrite <- comp.
  repeat rewrite assoc.
	exact (monoid_α_law_1_3''' monoid_α_law_1_3'' α_nat_law).
Defined.

Definition monoid_α_law_2_1 : λ_ (MX ⊗ MX) · app = e #⊗ id (MX ⊗ MX) · (αinv_ MX MX MX · app #⊗ id MX · app).
Proof.
	pose (αinv_nat_law := post_comp_comm (pr2 α'inv ((I, MX), MX) ((MX, MX), MX) ((e #, id MX) #, id MX)) (app #⊗ id MX)).
	simpl in αinv_nat_law.
	unfold dom_associator_on_mor, cod_associator_on_mor in αinv_nat_law.
	simpl in αinv_nat_law.
	Definition monoid_α_law_2_1' : λ_ MX #⊗ id MX · id MX #⊗ id MX = (e #⊗ id MX) #⊗ id MX · app #⊗ id MX.
	Proof.
		repeat rewrite <- (functor_comp tensor).
		repeat rewrite binprod_precat_comp.
		repeat rewrite id_left.
		rewrite id_right.
		exact (maponpaths (λ x, # tensor x) (maponpaths (λ x, (x #, id MX)) monoid_λ_law)).
	Defined.
  repeat rewrite <- assoc in αinv_nat_law.
  force (αinv_nat_law : (# tensor (e #, # tensor (id MX #, id MX)) · (pr1 α'inv ((MX, MX), MX) · # tensor (app #, id MX)) = pr1 α'inv ((I, MX), MX) · (# tensor (# tensor (e #, id MX) #, id MX) · # tensor (app #, id MX)))).
  rewrite <- monoid_α_law_2_1' in αinv_nat_law.
  repeat rewrite assoc in αinv_nat_law.
  pose (coher := monoidal_precat_coherence_3).
  unfold αinv_ in coher.
  force (αinv_nat_law : (# tensor (e #, # tensor (id MX #, id MX)) · pr1 α'inv ((MX, MX), MX) · # tensor (app #, id MX) = pr1 α'inv ((I, MX), MX) · # tensor (λ_ MX #, id MX) · # tensor (id MX #, id MX))).
  force (coher : (pr1 α'inv ((I, MX), MX) · # tensor (λ_ MX #, id MX) = λ_ (MX ⊗ MX))).
  rewrite coher in αinv_nat_law.
  symmetry.
  rewrite <- id_on_binprod_precat_pair_of_el in αinv_nat_law.
  rewrite (functor_id tensor) in αinv_nat_law.
  rewrite id_right in αinv_nat_law.
  repeat rewrite assoc.
  exact (post_comp_comm αinv_nat_law app).
Defined.

Definition monoid_α_law_2_2 : φ #⊗ id (MX ⊗ MX) · (αinv_ MX MX MX · app #⊗ id MX · app) = st MX (MX ⊗ MX) · #Σ (αinv_ MX MX MX · (app #⊗ id MX) · app) · φ.
Proof.
  pose (st_assoc_law := post_comp_comm (st_al MX MX MX) (#Σ (app #⊗ (id MX)))).
  unfold αinv_ in st_assoc_law.
  repeat rewrite <- assoc in st_assoc_law.
  pose (st_nat_law := st_ntl (MX ⊗ MX) MX MX MX app (id MX)).
  force (st_nat_law : (st (MX ⊗ MX) MX · # Σ (# tensor (app #, id MX)) = # tensor (# Σ app #, id MX) · st MX MX)).
  force (st_assoc_law : (st MX (MX ⊗ MX) · (# Σ (pr1 α'inv ((MX, MX), MX)) · # Σ (# tensor (app #, id MX))) = pr1 α'inv ((Σ MX, MX), MX) · (# tensor (st MX MX #, id MX) · (st (MX ⊗ MX) MX · # Σ (# tensor (app #, id MX)))))).
  rewrite st_nat_law in st_assoc_law.
  pose (st_assoc_law' := post_comp_comm st_assoc_law (#Σ app · φ)).
  repeat rewrite <- assoc in st_assoc_law'.
  pose (Σ_alg_law' := Σ_alg_law).
  rewrite <- assoc in Σ_alg_law'.
  force (Σ_alg_law' : (# tensor (φ #, id MX) · app = st MX MX · (# Σ app · φ))).
  force (st_assoc_law' : (st MX (MX ⊗ MX) · (# Σ (pr1 α'inv ((MX, MX), MX)) · (# Σ (# tensor (app #, id MX)) · (# Σ app · φ))) = pr1 α'inv ((Σ MX, MX), MX) · (# tensor (st MX MX #, id MX) · (# tensor (# Σ app #, id MX) · (st MX MX · (# Σ app · φ)))))).
  rewrite <- Σ_alg_law' in st_assoc_law'.
  pose (Σ_alg_law'' := maponpaths (λ x, x #⊗ id MX) Σ_alg_law).
  simpl in Σ_alg_law''.
  rewrite <- (id_right (id MX)) in Σ_alg_law''.
  repeat rewrite <- binprod_precat_comp in Σ_alg_law''.
  repeat rewrite (functor_comp tensor) in Σ_alg_law''.
  rewrite id_right in Σ_alg_law''.
  assert (expand_Σ_alg : (st MX MX · # Σ app) #⊗ id MX = st MX MX #⊗ id MX · # Σ app #⊗ id MX) by (
    rewrite <- (id_right (id MX));
    repeat rewrite <- binprod_precat_comp;
    rewrite (functor_comp tensor);
    rewrite id_right;
    reflexivity
    ).
  force (Σ_alg_law'' : (# tensor (# tensor (φ #, id MX) #, id MX) · # tensor (app #, id MX) = # tensor (st MX MX · # Σ app #, id MX) · # tensor (φ #, id MX))).
  rewrite expand_Σ_alg in Σ_alg_law''.
  pose (Σ_alg_law''' := post_comp_comm Σ_alg_law'' app).
  repeat rewrite <- assoc in Σ_alg_law'''.
  force (st_assoc_law' : (st MX (MX ⊗ MX) · (# Σ (pr1 α'inv ((MX, MX), MX)) · (# Σ (# tensor (app #, id MX)) · (# Σ app · φ))) = pr1 α'inv ((Σ MX, MX), MX) · (# tensor (st MX MX #, id MX) · (# tensor (# Σ app #, id MX) · (# tensor (φ #, id MX) · app))))).
  force (Σ_alg_law''' : (# tensor (# tensor (φ #, id MX) #, id MX) · (# tensor (app #, id MX) · app) = # tensor (st MX MX #, id MX) · (# tensor (# Σ app #, id MX) · (# tensor (φ #, id MX) · app)))).
  rewrite <- Σ_alg_law''' in st_assoc_law'.
  repeat rewrite assoc in st_assoc_law'.
  pose (αinv_nat_law := pr2 α'inv ((Σ MX, MX), MX) ((MX, MX), MX) ((φ #, id MX) #, id MX)).
  simpl in αinv_nat_law.
  unfold dom_associator_on_mor, cod_associator_on_mor in αinv_nat_law.
  simpl in αinv_nat_law.
  fold tensor in αinv_nat_law.
  force (st_assoc_law' : (st MX (MX ⊗ MX) · # Σ (pr1 α'inv ((MX, MX), MX)) · # Σ (# tensor (app #, id MX)) · # Σ app · φ = pr1 α'inv ((Σ MX, MX), MX) · # tensor (# tensor (φ #, id MX) #, id MX) · # tensor (app #, id MX) · app)).
  force (αinv_nat_law : (# tensor (φ #, # tensor (id MX #, id MX)) · pr1 α'inv ((MX, MX), MX) = pr1 α'inv ((Σ MX, MX), MX) · # tensor (# tensor (φ #, id MX) #, id MX))).
  rewrite <- αinv_nat_law in st_assoc_law'.
  rewrite <- (functor_id tensor).
  rewrite id_on_binprod_precat_pair_of_el.
  unfold αinv_.
  symmetry.
  repeat rewrite (functor_comp Σ).
  repeat rewrite assoc.
  exact st_assoc_law'.
Defined.

Definition monoid_α_law_2_3 : α #⊗ id (MX ⊗ MX) · (αinv_ MX MX MX · app #⊗ id MX · app) = α_ X MX (MX ⊗ MX) · id X #⊗ (αinv_ MX MX MX · (app #⊗ id MX) · app) · α.
Proof.
  pose (coher := post_comp_comm monoidal_precat_coherence_4 (id X #⊗ (app #⊗ id MX))).
  unfold α_, αinv_ in coher.
  repeat rewrite <- assoc in coher.
  pose (α_nat_law := pr2 α' ((X, MX ⊗ MX), MX) ((X, MX), MX) ((id X #, app) #, id MX)).
  unfold dom_associator_on_mor, cod_associator_on_mor in α_nat_law.
  simpl in α_nat_law.
  fold tensor in α_nat_law.
  force (α_nat_law : (# tensor (# tensor (id X #, app) #, id MX) · pr1 α' ((X, MX), MX) = pr1 α' ((X, MX ⊗ MX), MX) · # tensor (id X #, # tensor (app #, id MX)))).
  force (coher : (pr1 α' ((X, MX), MX ⊗ MX) · (# tensor (id X #, pr1 α'inv ((MX, MX), MX)) · # tensor (id X #, # tensor (app #, id MX))) = pr1 α'inv ((X ⊗ MX, MX), MX) · (# tensor (pr1 α' ((X, MX), MX) #, id MX) · (pr1 α' ((X, MX ⊗ MX), MX) · # tensor (id X #, # tensor (app #, id MX)))))).
  rewrite <- α_nat_law in coher.
  pose (coher' := post_comp_comm coher (id X #⊗ app · α)).
  repeat rewrite <- assoc in coher'.
  pose (app_c_law := pr2 (pr2 app_conds)).
  fold app in app_c_law.
  unfold α_ in app_c_law.
  rewrite <- assoc in app_c_law.
  force (app_c_law : (# tensor (α #, id MX) · app = pr1 α' ((X, MX), MX) · (# tensor (id X #, app) · α))).
  force (coher' : (pr1 α' ((X, MX), MX ⊗ MX) · (# tensor (id X #, pr1 α'inv ((MX, MX), MX)) · (# tensor (id X #, # tensor (app #, id MX)) · (# tensor (id X #, app) · α))) = pr1 α'inv ((X ⊗ MX, MX), MX) · (# tensor (pr1 α' ((X, MX), MX) #, id MX) · (# tensor (# tensor (id X #, app) #, id MX) · (pr1 α' ((X, MX), MX) · (# tensor (id X #, app) · α)))))).
  rewrite <- app_c_law in coher'.
  pose (app_c_law' := maponpaths (λ x, x #⊗ id MX) app_c_law).
  simpl in app_c_law'.
  rewrite <- (id_right (id MX)) in app_c_law'.
  repeat rewrite <- binprod_precat_comp in app_c_law'.
  repeat rewrite (functor_comp tensor) in app_c_law'.
  rewrite id_right in app_c_law'.
  assert (expand_app_c : ((id X #⊗ app) · α) #⊗ id MX = (id X #⊗ app) #⊗ id MX · α #⊗ id MX) by (
    rewrite <- (id_right (id MX));
    repeat rewrite <- binprod_precat_comp;
    rewrite (functor_comp tensor);
    rewrite id_right;
    reflexivity
    ).
  force (app_c_law' : (# tensor (# tensor (α #, id MX) #, id MX) · # tensor (app #, id MX) = # tensor (pr1 α' ((X, MX), MX) #, id MX) · # tensor (# tensor (id X #, app) · α #, id MX))).
  rewrite expand_app_c in app_c_law'.
  pose (app_c_law'' := post_comp_comm app_c_law' app).
  repeat rewrite <- assoc in app_c_law''.
  force (coher' : (pr1 α' ((X, MX), MX ⊗ MX) · (# tensor (id X #, pr1 α'inv ((MX, MX), MX)) · (# tensor (id X #, # tensor (app #, id MX)) · (# tensor (id X #, app) · α))) = pr1 α'inv ((X ⊗ MX, MX), MX) · (# tensor (pr1 α' ((X, MX), MX) #, id MX) · (# tensor (# tensor (id X #, app) #, id MX) · (# tensor (α #, id MX) · app))))).
  force (app_c_law'' : (# tensor (# tensor (α #, id MX) #, id MX) · (# tensor (app #, id MX) · app) = # tensor (pr1 α' ((X, MX), MX) #, id MX) · (# tensor (# tensor (id X #, app) #, id MX) · (# tensor (α #, id MX) · app)))).
  rewrite <- app_c_law'' in coher'.
  repeat rewrite assoc in coher'.
  pose (αinv_nat_law := pr2 α'inv ((X ⊗ MX, MX), MX) ((MX, MX), MX) ((α #, id MX) #, id MX)).
  simpl in αinv_nat_law.
  unfold dom_associator_on_mor, cod_associator_on_mor in αinv_nat_law.
  simpl in αinv_nat_law.
  fold tensor in αinv_nat_law.
  force (coher' : (pr1 α' ((X, MX), MX ⊗ MX) · # tensor (id X #, pr1 α'inv ((MX, MX), MX)) · # tensor (id X #, # tensor (app #, id MX)) · # tensor (id X #, app) · α = pr1 α'inv ((X ⊗ MX, MX), MX) · # tensor (# tensor (α #, id MX) #, id MX) · # tensor (app #, id MX) · app)).
  force (αinv_nat_law : (# tensor (α #, # tensor (id MX #, id MX)) · pr1 α'inv ((MX, MX), MX) = pr1 α'inv ((X ⊗ MX, MX), MX) · # tensor (# tensor (α #, id MX) #, id MX))).
  rewrite <- αinv_nat_law in coher'.
  symmetry in coher'.
  rewrite <- id_on_binprod_precat_pair_of_el in coher'.
  rewrite (functor_id tensor) in coher'.
  assert (coher'' : # tensor (α #, id (MX ⊗ MX)) · pr1 α'inv ((MX, MX), MX) · # tensor (app #, id MX) · app = # tensor (α #, id (MX ⊗ MX)) · (αinv_ MX MX MX · # tensor (app #, id MX) · app)) by
  (unfold αinv_;
  repeat rewrite assoc;
  reflexivity).
  force (coher' : (# tensor (α #, id (MX ⊗ MX)) · pr1 α'inv ((MX, MX), MX) · # tensor (app #, id MX) · app = pr1 α' ((X, MX), MX ⊗ MX) · # tensor (id X #, pr1 α'inv ((MX, MX), MX)) · # tensor (id X #, # tensor (app #, id MX)) · # tensor (id X #, app) · α)).
  rewrite coher'' in coher'.
  assert (coher''' : # tensor (id X #, pr1 α'inv ((MX, MX), MX)) · # tensor (id X #, # tensor (app #, id MX)) · # tensor (id X #, app) = # tensor (id X #, pr1 α'inv ((MX, MX), MX) · # tensor (app #, id MX) · app)) by
  (repeat rewrite <- (functor_comp tensor);
  repeat rewrite binprod_precat_comp;
  repeat rewrite id_left;
  reflexivity).
  pose (coher'''' := maponpaths (λ x, pr1 α' ((X, MX), MX ⊗ MX) · x · α) coher'''); simpl in coher''''.
  repeat rewrite assoc in coher''''.
  force (coher' : (# tensor (α #, id (MX ⊗ MX)) · (αinv_ MX MX MX · # tensor (app #, id MX) · app) = pr1 α' ((X, MX), MX ⊗ MX) · # tensor (id X #, pr1 α'inv ((MX, MX), MX)) · # tensor (id X #, # tensor (app #, id MX)) · # tensor (id X #, app) · α)).
  force (coher'''' : (pr1 α' ((X, MX), MX ⊗ MX) · # tensor (id X #, pr1 α'inv ((MX, MX), MX)) · # tensor (id X #, # tensor (app #, id MX)) · # tensor (id X #, app) · α = pr1 α' ((X, MX), MX ⊗ MX) · # tensor (id X #, pr1 α'inv ((MX, MX), MX) · # tensor (app #, id MX) · app) · α)).
  rewrite coher'''' in coher'.
  exact coher'.
Defined.

Check @ipi.
Local Definition it3_ipi := @ipi MX (MX ⊗ MX) φ app α.
Local Definition it3 := pr1 it3_ipi.

Definition idMX_app_app_as_it3 : parameterised_initiality φ app α (id MX #⊗ app · app).
Proof.
  exists monoid_α_law_1_1.
  exists monoid_α_law_1_2.
  exact monoid_α_law_1_3.
Defined.

Definition αinv_MXMXMX_app_idMX_app_as_it3 : parameterised_initiality φ app α (αinv_ MX MX MX · app #⊗ id MX · app).
  exists monoid_α_law_2_1.
  exists monoid_α_law_2_2.
  exact monoid_α_law_2_3.
Defined.

Context (α_iso_cancel : id ((MX ⊗ MX) ⊗ MX) = α_ MX MX MX · αinv_ MX MX MX).

Definition monoid_α_law : app #⊗ id MX · app = α_ MX MX MX · id MX #⊗ app · app.
Proof.
  pose (idMX_app_app_is_it := pr2 it3_ipi (id MX #⊗ app · app,, idMX_app_app_as_it3)).
  pose (αinv_MXMXMX_app_idMX_app_is_it := pr2 it3_ipi (αinv_ MX MX MX · app #⊗ id MX · app,, αinv_MXMXMX_app_idMX_app_as_it3)).
  rewrite <- αinv_MXMXMX_app_idMX_app_is_it in idMX_app_app_is_it.
  pose (mapped := maponpaths pr1 idMX_app_app_is_it).
  simpl in mapped.
  pose (mapped' := maponpaths (λ x, α_ MX MX MX · x) mapped).
  simpl in mapped'.
  repeat rewrite assoc in mapped'.
  force (mapped' : (α_ MX MX MX · # tensor (id MX #, app) · app = α_ MX MX MX · αinv_ MX MX MX · # tensor (app #, id MX) · app)).
  rewrite <- α_iso_cancel in mapped'.
  symmetry.
  rewrite id_left in mapped'.
  exact mapped'.
Defined.

End Parameterised_Initiality.

(* We assume that X ⊗ - is ω-cocontinuous and that C has ω-colimits. *)
Context (is_ω_cocont_X_preapp : is_omega_cocont X_preapp_functor) (has_ω_colimits : ColimCocone (initChain Z Σ_I_X)).

Lemma is_ω_cocont_Σ_I_X : is_omega_cocont Σ_I_X.
Proof.
		refine (is_omega_cocont_BinCoproduct_of_functors bin_coproduct has_homsets_C _ _ _ _).
		- refine (is_omega_cocont_BinCoproduct_of_functors bin_coproduct has_homsets_C _ _ _ _).
			+ exact is_ω_cocont_Σ.
			+ exact (is_omega_cocont_constant_functor has_homsets_C _).
		- exact is_ω_cocont_X_preapp.
Defined.

(* The initial (Σ + ΔI + X ⊗)-algebra. *)
Definition MX : Initial (precategory_FunctorAlg Σ_I_X has_homsets_C).
Proof.
	apply (colimAlgInitial _ Z is_ω_cocont_Σ_I_X).
	exact has_ω_colimits.
Defined.

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