Require Import UniMath.Foundations.PartD. (* for ∑ *)
Require Import UniMath.CategoryTheory.Categories. (* for precategory *)
Require Import UniMath.CategoryTheory.functor_categories. (* for functor *)
Require Import UniMath.MetaSubstitutionSystems.Monoidal. (* for binprod_precat *)
Require Import UniMath.CategoryTheory.limits.binproducts. (* for BinProducts *)
Require Import UniMath.MetaSubstitutionSystems.CosliceMonoidal. (* for precategory_coslice *)
Require Import UniMath.MetaSubstitutionSystems.ForceTactic. (* for force_goal *)

Local Open Scope cat.

Context (Mon_V : monoidal_precat).

Let V := monoidal_precat_precat Mon_V.
Let I := monoidal_precat_unit Mon_V.
Let tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)) (at level 31).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Let α' := monoidal_precat_associator Mon_V.
Let λ' := monoidal_precat_left_unitor Mon_V.
Let ρ' := monoidal_precat_right_unitor Mon_V.

Section Actions_Definition.

(* A ⊙ I --> A *)

Section Actions_Natural_Transformations.

Context (A : precategory) (odot : functor (binprod_precat A V) A).

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (# odot (f #, g)) (at level 31).

Definition odot_I_functor : functor A A.
Proof.
    use tpair.
    - use tpair.
      exact (λ a, a ⊙ I).
      intros ? ? f.
      exact (f #⊙ (id I)).
    - split.
      + intro.
        simpl.
        rewrite binprod_id.
        rewrite (functor_id odot).
        reflexivity.
      + unfold functor_compax.
        simpl.
        intros.
        replace (id I) with (id I · id I).
        rewrite binprod_comp.
        rewrite id_left.
        rewrite (functor_comp odot).
        reflexivity.
        rewrite id_left.
        reflexivity.
Defined.

Definition action_right_unitor : UU := nat_iso odot_I_functor (functor_identity A).

Definition odot_x_odot_y_functor : (A ⊠ V) ⊠ V ⟶ A.
Proof.
  use tpair.
  - use tpair.
    exact (λ a, (a true true ⊙ a true false) ⊙ a false).
    intros ? ? f.
    exact ((f true true #⊙ f true false) #⊙ f false).
  - split.
    + intro.
      simpl.
      repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
      do 2 (rewrite binprod_id; rewrite (functor_id odot)).
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros.
      repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
      do 2 (rewrite binprod_comp; rewrite (functor_comp odot)).
      reflexivity.
Defined.

Definition odot_x_otimes_y_functor : (A ⊠ V) ⊠ V ⟶ A.
Proof.
  use tpair.
    - use tpair.
      exact (λ a, a true true ⊙ (a true false ⊗ a false)).
      intros ? ? f.
      exact (f true true #⊙ (f true false #⊗ f false)).
    - split.
      + intro.
        simpl.
        repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
        rewrite binprod_id.
        rewrite (functor_id tensor).
        rewrite binprod_id.
        rewrite (functor_id odot).
        reflexivity.
      + unfold functor_compax.
        simpl.
        intros.
        rewrite <- (functor_comp odot).
        rewrite <- binprod_comp.
        repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
        rewrite binprod_comp.
        rewrite (functor_comp tensor).
        reflexivity.
Defined.

Definition action_convertor : UU := nat_iso odot_x_odot_y_functor odot_x_otimes_y_functor.

Definition action_triangle_eq (ϱ : action_right_unitor) (χ : action_convertor) := ∏ (a : A), ∏ (x : V),
  (pr1 ϱ a) #⊙ (id x) = (pr1 χ ((a, I), x)) · (id a) #⊙ (pr1 λ' x).

Definition action_pentagon_eq (χ : action_convertor) := ∏ (a : A), ∏ (x y z : V),
(pr1 χ ((a ⊙ x, y), z)) · (pr1 χ ((a, x), y ⊗ z)) = (pr1 χ ((a, x), y)) #⊙ (id z) · (pr1 χ ((a, x ⊗ y), z)) · (id a) #⊙ (pr1 α' ((x, y), z)).

End Actions_Natural_Transformations.

(* Action *)

Definition action : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor A odot), ∑ (χ : action_convertor A odot), (action_triangle_eq A odot ϱ χ) × (action_pentagon_eq A odot χ).

Definition action_struct : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor A odot), ∑ (χ : action_convertor A odot), unit.

End Actions_Definition.

Section Strengths_Definition.

Context (actn actn' : action).

Let A := pr1 actn.
Let odot := pr1 (pr2 actn).
Let ϱ := pr1 (pr2 (pr2 actn)).
Let χ := pr1 (pr2 (pr2 (pr2 actn))).
Let A' := pr1 actn'.
Let odot' := pr1 (pr2 actn').
Let ϱ' := pr1 (pr2 (pr2 actn')).
Let χ' := pr1 (pr2 (pr2 (pr2 actn'))).

Section Strengths_Natural_Transformation.

Context (F : A ⟶ A').

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (#odot (f #, g)) (at level 31).
Notation "X ⊙' Y" := (odot' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#odot' (f #, g)) (at level 31).

Definition strength_dom : functor (binprod_precat A V) A'.
Proof.
  use tpair.
  - use tpair.
    exact (λ ax, F (ax true) ⊙' (ax false)).
    intros ? ? f.
    exact ((#F (f true)) #⊙' (f false)).
  - split.
    + intro.
      simpl.
      rewrite (functor_id F).
      rewrite <- (functor_id odot').
      rewrite <- binprod_id.
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros.
      rewrite <- (functor_comp odot').
      rewrite <- binprod_comp.
      rewrite <- (functor_comp F).
      reflexivity.
Defined.

Definition strength_codom : A ⊠ V ⟶ A'.
Proof.
use tpair.
- use tpair.
  exact (λ ax, F (ax true ⊙ ax false)).
  intros ? ? f.
  exact (#F (f true #⊙ f false)).
- split.
  + intro.
    simpl.
    rewrite <- (functor_id F).
    rewrite <- (functor_id odot).
    rewrite <- binprod_id.
    reflexivity.
  + unfold functor_compax.
    simpl.
    intros.
    rewrite <- (functor_comp F).
    rewrite <- (functor_comp odot).
    rewrite <- binprod_comp.
    reflexivity.
Defined.

Definition strength_nat : UU := nat_iso strength_dom strength_codom.

Definition strength_triangle_eq (ϛ : strength_nat) := ∏ (a : A),
(pr1 ϛ (a, I)) · (#F (pr1 ϱ a)) = pr1 ϱ' (F a).

Definition strength_pentagon_eq (ϛ : strength_nat) := ∏ (a : A), ∏ (x y : V),
  (pr1 χ' ((F a, x), y)) · pr1 ϛ (a, x ⊗ y) = (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)) · (#F (pr1 χ ((a, x), y))).

End Strengths_Natural_Transformation.

Definition strength : UU := ∏ F : A ⟶ A', ∑ (ϛ : strength_nat F),
(strength_triangle_eq F ϛ) × (strength_pentagon_eq F ϛ).

End Strengths_Definition.

Section Homogeneous_Strengths.

(* The canonical tensorial action on a monoidal category. *)
Definition tensorial_action : action.
Proof.
  exists V.
  exists tensor.
  exists ρ'.
  exists α'.
  exact (monoidal_precat_eq Mon_V).
Defined.

(* F(A) ⊗ B --> F(A ⊗ B) *)
Definition tensorial_strength := strength tensorial_action tensorial_action.

Context (bin_product : BinProducts V).

(*Definition cartesian_action : action.
Proof.
  exists V.
  Check binproduct_functor bin_product. (* needs to be our version of binary product categories *)
Admitted.

(* F(A) × B --> F(A × B) *)
Definition cartesian_strength := strength cartesian_action cartesian_action.*)

End Homogeneous_Strengths.

Section Strong_Monoidal_Functor_Action.

Context (Mon_A : monoidal_precat).

Let A := monoidal_precat_precat Mon_A.
Let I_A := monoidal_precat_unit Mon_A.
Let tensor_A := monoidal_precat_tensor Mon_A.
Notation "X ⊗_A Y" := (tensor_A (X , Y)) (at level 31).
Notation "f #⊗_A g" := (#tensor_A (f #, g)) (at level 31).
Let α_A := monoidal_precat_associator Mon_A.
Let λ_A := monoidal_precat_left_unitor Mon_A.
Let ρ_A := monoidal_precat_right_unitor Mon_A.

Context (U : strong_monoidal_functor Mon_V Mon_A).

Definition otimes_U_functor : A ⊠ V ⟶ A.
use tpair.
- use tpair.
  exact (λ av, av true ⊗_A U (av false)).
  intros ? ? f.
  exact (f true #⊗_A #U (f false)).
- split.
  + intro.
    simpl.
    rewrite (functor_id U).
    rewrite (binprod_proj_id a).
    rewrite binprod_id.
    rewrite (functor_id tensor_A).
    reflexivity.
  + unfold functor_compax.
    simpl.
    intros.
    do 2 rewrite (binprod_proj_comp f).
    rewrite (functor_comp U).
    rewrite binprod_comp.
    rewrite (functor_comp tensor_A).
    reflexivity.
Defined.

Definition U_action_struct : action_struct.
Proof.
  exists A.
  exists otimes_U_functor.
  (* K ⊗ U I_C -- (1_K ⊗ ϵ^{-1} · λ_D K) --> K *)
  use tpair; [| use tpair].
  - (* ϱ *)
    unfold action_right_unitor.
    unfold nat_iso.
    use tpair.
    + (* natural transformation *)
      unfold nat_trans.
      pose (ϵ_inv := inv_from_iso (mk_iso (pr1 (pr2 U)))).
      exists (λ x, id x #⊗_A ϵ_inv · pr1 ρ_A x). (* ϱ *)
      intros x x' f.
      pose (ρ_nat_law := pr2 (pr1 ρ_A) x x' f).
      simpl; simpl in ρ_nat_law.
      assert (ϵ_coher : id x #⊗_A ϵ_inv · f #⊗_A id I_A = f #⊗_A (#U (id I)) · id x' #⊗_A ϵ_inv).
      * do 2 rewrite <- functor_comp.
        do 2 rewrite <- binprod_comp.
        rewrite functor_id.
        do 2 (rewrite id_left; rewrite id_right).
        reflexivity.
      * rewrite assoc.
        force (ϵ_coher : (# tensor_A (id x #, ϵ_inv) · # tensor_A (f #, id I_A) = # tensor_A (f #, # U (id I)) · # tensor_A (id x' #, ϵ_inv))).
        force_goal (# tensor_A (f #, # U (id I)) · # tensor_A (id x' #, ϵ_inv) · (pr1 ρ_A) x' = # tensor_A (id x #, ϵ_inv) · (pr1 ρ_A) x · f).
        rewrite <- ϵ_coher.
        repeat rewrite <- assoc.
        force_goal (# tensor_A (id x #, ϵ_inv) · (# tensor_A (f #, id I_A) · (pr1 ρ_A) x') = # tensor_A (id x #, ϵ_inv) · (pr1 (pr1 ρ_A) x · f)).
        force (ρ_nat_law : (# (pr1 (pr2 Mon_A)) (f #, id pr1 (pr2 (pr2 Mon_A))) · pr1 (pr1 ρ_A) x' = pr1 (pr1 ρ_A) x · f)).
        rewrite <- ρ_nat_law.
        reflexivity.
    + (* is_nat_iso ϱ *)
      intro.
      simpl.
      use is_iso_comp_of_is_isos.
      use is_iso_tensor_iso.
      exact is_iso_id.
      use is_iso_inv_from_iso.
      exact (pr2 ρ_A c).
  - (* χ *)
    use tpair.
    + (* natural transformation *)
      unfold nat_trans.
      pose (μ := pr1 (pr2 (pr2 (pr1 U)))).
      use tpair.
      intro x.
      pose (k := x true true); pose (k' := x true false); pose (k'' := x false).
      exact (pr1 α_A ((k, U k'), U k'') · id k #⊗_A pr1 μ (k', k'')). (* χ *)
      intros x x' g.
      simpl.
      pose (k_1 := x true true); pose (k'_1 := x true false); pose (k''_1 := x false).
      pose (k_2 := x' true true); pose (k'_2 := x' true false); pose (k''_2 := x' false).
      pose (f := g true true); pose (f' := g true false); pose (f'' := g false).
      fold monoidal_precat_precat.
      pose (α_nat_law := pr2 (pr1 α_A) ((k_1, U k'_1), U k''_1) ((k_2, U k'_2), U k''_2) ((f #, #U f') #, #U f'')).
      assert (μ_coher : id k_1 #⊗_A (pr1 μ (k'_1, k''_1)) · (f #⊗_A #U (f' #⊗ f'')) = f #⊗_A (#U f' #⊗_A #U f'') · id k_2 #⊗_A (pr1 μ (k'_2, k''_2))).
      do 2 rewrite <- tensor_comp.
      rewrite id_left; rewrite id_right.
      assert (snd_eq : pr1 μ (k'_1, k''_1) · # U (f' #⊗ f'') = # tensor_A (# U f' #, # U f'') · pr1 μ (k'_2, k''_2)).
      symmetry.
      exact (pr2 μ (k'_1, k''_1) (k'_2, k''_2) (f' #, f'')).
      force_goal (# tensor_A (f #, pr1 μ (k'_1, k''_1) · # U (# tensor (f' #, f''))) = # tensor_A (f #, # tensor_A (# U f' #, # U f'') · pr1 μ (k'_2, k''_2))).
      rewrite <- snd_eq.
      reflexivity.
      force (α_nat_law : (# tensor_A (# tensor_A (f #, # U f') #, # U f'') · pr1 (pr1 α_A) ((k_2, U k'_2), U k''_2) = pr1 (pr1 α_A) ((k_1, U k'_1), U k''_1) · # tensor_A (f #, # tensor_A (# U f' #, # U f'')))).
      pose (α_nat_law' := maponpaths (λ p, p · id k_2 #⊗_A (pr1 μ (k'_2, k''_2))) α_nat_law).
      simpl in α_nat_law'.
      repeat rewrite <- assoc in α_nat_law'.
      force (α_nat_law' : (# tensor_A (# tensor_A (f #, # U f') #, # U f'') · (pr1 (pr1 α_A) ((k_2, U k'_2), U k''_2) · # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2))) = pr1 (pr1 α_A) ((k_1, U k'_1), U k''_1) · (# tensor_A (f #, # tensor_A (# U f' #, # U f'')) · # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2))))).
      force (μ_coher : (# tensor_A (id k_1 #, pr1 μ (k'_1, k''_1)) · # tensor_A (f #, # U (# tensor (f' #, f''))) = # tensor_A (f #, # tensor_A (# U f' #, # U f'')) · # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2)))).
      pose (common := # tensor_A (f #, # tensor_A (# U f' #, # U f'')) · # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2))).
      fold common in μ_coher.
      fold common in α_nat_law'.
      rewrite <- μ_coher in α_nat_law'.
      repeat rewrite assoc in α_nat_law'.
      repeat rewrite assoc.
      exact α_nat_law'.
    + (* is_nat_iso χ *)
      intro x.
      pose (k := x true true); pose (k' := x true false); pose (k'' := x false).
      use is_iso_comp_of_is_isos.
      exact (pr2 α_A ((k, U k'), U k'')).
      use is_iso_tensor_iso.
      use is_iso_id.
      exact (pr2 (pr2 U) (k', k'')).
  - exact tt.
Defined.

Context {U_action_tlaw : action_triangle_eq (pr1 U_action_struct) (pr1 (pr2 U_action_struct)) (pr1 (pr2 (pr2 U_action_struct))) (pr1 (pr2 (pr2 (pr2 U_action_struct))))} {U_action_plaw : action_pentagon_eq (pr1 U_action_struct) (pr1 (pr2 U_action_struct)) (pr1 (pr2 (pr2 (pr2 U_action_struct))))}.

Definition U_action : action.
  exists (pr1 U_action_struct).
  exists (pr1 (pr2 U_action_struct)).
  exists (pr1 (pr2 (pr2 U_action_struct))).
  exists (pr1 (pr2 (pr2 (pr2 U_action_struct)))).
  split.
  exact U_action_tlaw.
  exact U_action_plaw.
Defined.

End Strong_Monoidal_Functor_Action.
