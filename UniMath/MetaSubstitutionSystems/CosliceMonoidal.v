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
Let ρ := monoidal_precat_to_right_unitor Mon.

Context (hs_V : has_homsets V).

Let coslice_precat := Undercategory V hs_V I.

Section Coslice_Monoidal.

(* Another useless lemma that's only necessary because Coq can't unify anything. *)
Lemma precomp_eq {C : precategory} {X Y Z : C} (f : X --> Y) (g g' : Y --> Z) (eq : g = g') : (f · g = f · g').
Proof.
  rewrite eq.
  reflexivity.
Defined.

Definition coslice_tensor : functor (binprod_precat coslice_precat coslice_precat) coslice_precat.
Proof.
  use tpair; [use tpair |].
  - intro xy. (* the map on objects and their morphisms from I *)
    pose (x := pr1 (xy true)).
    pose (y := pr1 (xy false)).
    pose (ux := pr2 (xy true)).
    pose (uy := pr2 (xy false)).
    exists (x ⊗ y).
    exact (inv_from_iso (pr1 λ' I) · ux #⊗ uy).
  - (* the map on morphisms *)
    intros xy x'y' fg.
    pose (ux := pr2 (xy true)).
    pose (uy := pr2 (xy false)).
    pose (f := pr1 (fg true)).
    pose (g := pr1 (fg false)).
    exists (f #⊗ g).
    simpl.
    rewrite <- assoc.
    assert (suffix_eq : (# (monoidal_precat_to_tensor Mon) (pr2 (xy true) #, pr2 (xy false)) · # (monoidal_precat_to_tensor Mon) (f #, g)) = # (monoidal_precat_to_tensor Mon) (pr2 (x'y' true) #, pr2 (x'y' false))).
    rewrite <- functor_comp.
    rewrite binprod_precat_comp.
    pose (eq_f := (pr2 (fg true))).
    pose (eq_g := (pr2 (fg false))).
    unfold Under_ob_mor in eq_f, eq_g.
    rewrite <- eq_f, <- eq_g.
    reflexivity.
    exact (precomp_eq (inv_from_iso (pr1 λ' I)) (# (monoidal_precat_to_tensor Mon) (pr2 (xy true) #, pr2 (xy false)) · # (monoidal_precat_to_tensor Mon) (f #, g)) (# (monoidal_precat_to_tensor Mon) (pr2 (x'y' true) #, pr2 (x'y' false))) suffix_eq).
  - (* functorality *)
    use tpair.
    + intro xy.
      (* 1_x #⊗ 1_y = 1_(x ⊗ y) *)
      admit.
    + intros xy x'y' x''y'' f g.
      rewrite binprod_precat_comp.
Admitted.

Definition coslice_associator : associator coslice_precat coslice_tensor.
Proof. Admitted.

Definition coslice_left_unitor : left_unitor coslice_precat coslice_tensor (I,, identity I).
Proof. Admitted.

Definition coslice_right_unitor : right_unitor coslice_precat coslice_tensor (I,, identity I).
Proof. Admitted.

Definition coslice_pentagon_eq : pentagon_eq coslice_precat coslice_tensor coslice_associator.
Proof. Admitted.

Definition coslice_triangle_eq : triangle_eq coslice_precat coslice_tensor (I,, identity I) coslice_associator
coslice_left_unitor coslice_right_unitor.
Proof. Admitted.

Definition coslice_monoidal_precat : monoidal_precat.
Proof.
  exists coslice_precat.
  exists coslice_tensor.
  use tpair.
  - exists I.
    exact (identity I).
  - unfold monoidal_struct.
    exists coslice_associator.
    exists coslice_left_unitor.
    exists coslice_right_unitor.
    split.
    exact coslice_pentagon_eq.
    exact coslice_triangle_eq.
Defined.

End Coslice_Monoidal.

Section Coslice_Forgetful_Functor.

Definition coslice_forgetful : functor coslice_precat V.
Proof.
  use tpair.
  - use tpair.
    exact (λ c, pr1 c).
    intros ? ? f.
    exact (pr1 f).
  - split.
    + intro.
      reflexivity.
    + intro.
      reflexivity.
Defined.

End Coslice_Forgetful_Functor.
