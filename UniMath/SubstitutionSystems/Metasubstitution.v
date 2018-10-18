Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 28).

Context (C : precategory).
Context (bin_prod : BinProducts C).
Context (bin_coprod : BinCoproducts C).

Definition dom {X Y : C} (f : X --> Y) := X.
Definition codom {X Y : C} (f : X --> Y) := Y.

Local Notation "X ⨰ Y" := (BinProductObject _ (bin_prod X Y)) (at level 31).
Local Notation "f #⨰ g" := (BinProductOfArrows C (bin_prod (codom f) (codom g)) (bin_prod (dom f) (dom g)) f g) (at level 41).

Local Notation "X ∔ Y" := (BinCoproductObject _ (bin_coprod X Y)) (at level 32).
Local Notation "f #∔ g" := (BinCoproductOfArrows C (bin_coprod (dom f) (dom g)) (bin_coprod (codom f) (codom g)) f g) (at level 41).

Section Exponentials.

Definition exponential_data (X Y : C) : UU := ∑ X_Y : C, (X_Y ⨰ Y --> X).

Definition is_exponential {X Y : C} (X_Y : exponential_data X Y) : UU :=
  ∏ (Z : C) (e : Z ⨰ Y --> X), ∃! (u : Z --> pr1 X_Y), u #⨰ (identity Y) · (pr2 X_Y) = e.

Definition exponential_ob (X Y : C) : UU :=
  ∑ (X_Y : exponential_data X Y), is_exponential X_Y.

Definition exponentials : UU :=
  ∏ (X Y : C), exponential_ob X Y.

Definition exp_ob {X Y : C} (X_Y : exponential_ob X Y) : C := pr1 (pr1 X_Y).

Definition exp_map {X Y : C} (X_Y : exponential_ob X Y) : exp_ob X_Y ⨰ Y --> X := pr2 (pr1 X_Y).

Definition exp_map' {X Y : C} (X_Y : exponential_ob X Y) : Y ⨰ exp_ob X_Y --> X := (BinProductSwap _ (bin_prod Y (exp_ob X_Y)) (bin_prod (exp_ob X_Y) Y)) · (exp_map X_Y).

End Exponentials.
