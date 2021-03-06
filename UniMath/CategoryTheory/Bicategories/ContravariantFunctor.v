(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Displayed bicategory of contravariant functors into a fixed category K.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.BicatOfCats.

Local Open Scope cat.
Local Open Scope mor_disp_scope.


Section fix_a_category.

Variable K : category.

Local Notation "∁" := bicat_of_cats.

Definition disp_presheaf_cat_ob_mor : disp_cat_ob_mor ∁.
Proof.
  use tpair.
    + exact (λ c : category, functor c^op K).
    + cbn. intros c d ty ty' f.
      exact (nat_trans ty (functor_composite (functor_opp f) ty')).
Defined.

Definition disp_presheaf_cat_data : disp_cat_data ∁.
Proof.
  exists disp_presheaf_cat_ob_mor.
  use tpair.
  + intros c f.
    set (T:= nat_trans_id (pr1 f) ).
    exact T.
  + intros c d e f g ty ty' ty''.
    intros x y.
    set (T1 := x).
    set (T2 := @pre_whisker
                 (op_cat c) (op_cat d) K
                 (functor_opp f) _ _ (y : nat_trans (ty': functor _ _ )  _  )).
    exact (@nat_trans_comp (op_cat c) K _ _ _ T1 T2 ).
Defined.

Definition disp_presheaf_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells bicat_of_cats.
Proof.
  exists disp_presheaf_cat_data.
  intros c d f g a.
  intros p p'.
  intros x y.
  cbn in *.
  exact (x = @nat_trans_comp (op_cat c) K _  _ _ y (post_whisker (op_nt a)  p')).
Defined.

Definition disp_presheaf_prebicat_ops : disp_prebicat_ops disp_presheaf_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    intro. rewrite (functor_id y). apply pathsinv0, id_right.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    intro.  rewrite (functor_id y). rewrite id_left, id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    intro. rewrite (functor_id y). apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    intro. rewrite (functor_id y). rewrite id_left, id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    intro. rewrite (functor_id y). repeat rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    intro. rewrite (functor_id z). rewrite id_right. apply pathsinv0, assoc.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    intro. rewrite (functor_id z). rewrite id_right. apply assoc.
  - intros. apply nat_trans_eq; try apply (homset_property K).
    intro.
    rewrite X. rewrite X0.
    cbn.
    pose (T:= @functor_comp (op_cat b) _ y).
    rewrite <- assoc.
    rewrite <- T.
    apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    rewrite X.
    intro. apply assoc.
  - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
    rewrite X.
    intros. cbn.
    pose (T:= nat_trans_ax gg).
    cbn in T.
    rewrite <- assoc.
    rewrite T.
    apply assoc.
Qed.

Definition disp_presheaf_prebicat_data : disp_prebicat_data ∁ := _ ,,  disp_presheaf_prebicat_ops.

Lemma disp_presheaf_prebicat_laws : disp_prebicat_laws disp_presheaf_prebicat_data.
Proof.
  repeat split; intro;
    intros;
    apply isaset_nat_trans; apply homset_property.
Qed.

Definition disp_presheaf_prebicat : disp_prebicat ∁ :=
  (disp_presheaf_prebicat_data,, disp_presheaf_prebicat_laws).

Lemma has_disp_cellset_disp_presheaf_prebicat
  : has_disp_cellset disp_presheaf_prebicat.
Proof.
  red. intros.
  unfold disp_2cells.
  cbn.
  apply isasetaprop.
  cbn in *.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition disp_presheaf_bicat : disp_bicat ∁ :=
  (disp_presheaf_prebicat,, has_disp_cellset_disp_presheaf_prebicat).

End fix_a_category.
