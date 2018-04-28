Require Import UniMath.Foundations.PartD. (* for ∑ *)
Require Import UniMath.CategoryTheory.Categories. (* for precategory *)
Require Import UniMath.CategoryTheory.functor_categories. (* for functor *)
Require Import UniMath.CategoryTheory.Monoidal. (* for binprod_precat *)
Require Import UniMath.CategoryTheory.UnderCategories. (* for UnderCategory *)

Local Open Scope cat.

Context (Mon : monoidal_precat).

Let V := monoidal_precat_to_precat Mon.
Let I := monoidal_precat_to_unit Mon.
Notation "X ⊗ Y" := ((monoidal_precat_to_tensor Mon) (X , Y)) (at level 31).
Notation "f #⊗ g" := (#(monoidal_precat_to_tensor Mon) (f #, g)) (at level 31).
Let α := monoidal_precat_to_associator Mon.
Let λ' := monoidal_precat_to_left_unitor Mon.
(* Let α := monoidal_precat_to_associator Mon.
Let λ' := monoidal_precat_to_left_unitor Mon.
Let ρ := monoidal_precat_to_right_unitor Mon. *)

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
      exact (f #⊙ (identity I)).
    - split.
      + intro.
        simpl.
        rewrite <- id_on_binprod_precat_pair_of_el.
        rewrite (functor_id odot).
        reflexivity.
      + unfold functor_compax.
        simpl.
        intros.
        replace (identity I) with (identity I · identity I).
        rewrite <- binprod_precat_comp.
        rewrite id_left.
        rewrite (functor_comp odot).
        reflexivity.
        rewrite id_left.
        reflexivity.
Defined.

Definition action_right_unitor : UU := nat_iso odot_I_functor (functor_identity A).

Definition odot_x_odot_y_functor (X Y : V) : functor A A.
Proof.
  use tpair.
  - use tpair.
    exact (λ a, (a ⊙ X) ⊙ Y).
    intros ? ? f.
    exact ((f #⊙ (identity X)) #⊙ (identity Y)).
  - split.
    + intro.
      simpl.
      repeat (rewrite <- id_on_binprod_precat_pair_of_el; rewrite (functor_id odot)).
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros.
      replace (identity X) with (identity X · identity X).
      replace (identity Y) with (identity Y · identity Y).
      rewrite <- binprod_precat_comp.
      rewrite (functor_comp odot).
      rewrite <- binprod_precat_comp.
      rewrite (functor_comp odot).
      repeat (rewrite id_left).
      reflexivity.
      all: rewrite id_left; reflexivity.
Defined.

Definition odot_x_otimes_y_functor (X Y : V) : functor A A.
Proof.
  use tpair.
    - use tpair.
      exact (λ a, a ⊙ (X ⊗ Y)).
      intros ? ? f.
      exact (f #⊙ (identity X #⊗ identity Y)).
    - split.
      + intro.
        simpl.
        rewrite <- id_on_binprod_precat_pair_of_el.
        rewrite (functor_id (monoidal_precat_to_tensor Mon)).
        rewrite <- id_on_binprod_precat_pair_of_el.
        rewrite (functor_id odot).
        reflexivity.
      + unfold functor_compax.
        simpl.
        intros.
        rewrite <- (functor_comp odot).
        rewrite binprod_precat_comp.
        rewrite <- id_on_binprod_precat_pair_of_el.
        rewrite (functor_id (monoidal_precat_to_tensor Mon)).
        rewrite id_left.
        reflexivity.
Defined.

Definition action_convertor : UU := ∏ (X Y : V), nat_iso (odot_x_odot_y_functor X Y) (odot_x_otimes_y_functor X Y).

Definition action_triangle_eq (υ : action_right_unitor) (ψ : action_convertor) := ∏ (a : A), ∏ (x : V),
  (pr1 υ a) #⊙ (identity x) = (pr1 (ψ I x) a) · (identity a) #⊙ (pr1 λ' x).

Definition action_pentagon_eq (ψ : action_convertor) := ∏ (a : A), ∏ (x y z : V),
  (pr1 (ψ x y) a) #⊙ (identity z) · (pr1 (ψ (x ⊗ y) z) a) · (identity a) #⊙ (pr1 α ((x, y), z)) = (pr1 (ψ y z) (a ⊙ x)) · (pr1 (ψ x (y ⊗ z)) a).

End Actions_Natural_Transformations.

(* Action *)

Definition action : UU := ∑ A : precategory, ∑ (odot : functor (binprod_precat A V) A), ∑ (υ : action_right_unitor A odot), ∑ (ψ : action_convertor A odot), (action_triangle_eq A odot υ ψ) × (action_pentagon_eq A odot ψ).

End Actions_Definition.

Section Strengths_Definition.

Context (actn actn' : action).

Let A := pr1 actn.
Let odot := pr1 (pr2 actn).
Let υ := pr1 (pr2 (pr2 actn)).
Let ψ := pr1 (pr2 (pr2 (pr2 actn))).
Let A' := pr1 actn'.
Let odot' := pr1 (pr2 actn').
Let υ' := pr1 (pr2 (pr2 actn')).
Let ψ' := pr1 (pr2 (pr2 (pr2 actn'))).

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
      rewrite id_on_binprod_precat_pair_of_el.
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros.
      rewrite <- (functor_comp odot').
      rewrite binprod_precat_comp.
      rewrite <- (functor_comp F).
      reflexivity.
Defined.

Definition strength_codom : functor (binprod_precat A V) A'.
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
    rewrite id_on_binprod_precat_pair_of_el.
    reflexivity.
  + unfold functor_compax.
    simpl.
    intros.
    rewrite <- (functor_comp F).
    rewrite <- (functor_comp odot).
    rewrite binprod_precat_comp.
    reflexivity.
Defined.

Definition strength_nat : UU := nat_iso strength_dom strength_codom.

Definition strength_triangle_eq (s : strength_nat) := ∏ (a : A),
(pr1 s (a, I)) · (#F (pr1 υ a)) = pr1 υ' (F a).

Definition strength_pentagon_eq (s : strength_nat) := ∏ (a : A), ∏ (x y : V),
  (pr1 s (a, x)) #⊙' (identity y) · (pr1 s (a ⊙ x, y)) · (#F (pr1 (ψ x y) a)) = (pr1 (ψ' x y) (F a)) · pr1 s (a, x ⊗ y).

End Strengths_Natural_Transformation.

Definition strength : UU := ∏ F : A ⟶ A', ∑ (s : strength_nat F),
(strength_triangle_eq F s) × (strength_pentagon_eq F s).

End Strengths_Definition.
