Require Import UniMath.Foundations.PartD. (* for ∑ *)
Require Import UniMath.CategoryTheory.Categories. (* for precategory *)
Require Import UniMath.CategoryTheory.functor_categories. (* for functor *)
Require Import UniMath.MetaSubstitutionSystems.Monoidal2. (* for binprod_precat *)
Require Import UniMath.CategoryTheory.limits.binproducts. (* for BinProducts *)
Require Import UniMath.MetaSubstitutionSystems.CosliceMonoidal. (* for precategory_Coslice *)
Require Import UniMath.MetaSubstitutionSystems.ForceTactic. (* for force_goal *)

Local Open Scope cat.

Context (Mon : monoidal_precat).

Let V := monoidal_precat_precat Mon.
Let I := monoidal_precat_unit Mon.
Let tensor := monoidal_precat_tensor Mon.
Notation "X ⊗ Y" := (tensor (X , Y)) (at level 31).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Let α' := monoidal_precat_associator Mon.
Let λ' := monoidal_precat_left_unitor Mon.
Let ρ' := monoidal_precat_right_unitor Mon.

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

Definition action : UU := ∑ A : precategory, ∑ (odot : functor (binprod_precat A V) A), ∑ (ϱ : action_right_unitor A odot), ∑ (χ : action_convertor A odot), (action_triangle_eq A odot ϱ χ) × (action_pentagon_eq A odot χ).

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
  exact (monoidal_precat_eq Mon).
Defined.

(* F(A) ⊗ B --> F(A ⊗ B) *)
Definition tensorial_strength := strength tensorial_action tensorial_action.

Context (bin_product : BinProducts V).

Definition cartesian_action : action.
Proof.
  exists V.
  Check binproduct_functor bin_product. (* needs to be our version of binary product categories *)
Admitted.

(* F(A) × B --> F(A × B) *)
Definition cartesian_strength := strength cartesian_action cartesian_action.

End Homogeneous_Strengths.
