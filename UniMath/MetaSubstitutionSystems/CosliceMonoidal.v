Require Import UniMath.Foundations.PartD. (* for ∑ *)
Require Import UniMath.CategoryTheory.Categories. (* for precategory *)
Require Import UniMath.CategoryTheory.functor_categories. (* for functor *)
Require Import UniMath.MetaSubstitutionSystems.Monoidal. (* for binprod_precat *)
Require Import UniMath.MetaSubstitutionSystems.ForceTactic. (* for force and force_goal *)

Local Open Scope cat.

Section Coslice_Precat_Definition.

Context (C : precategory) (A : C).

Definition coslice_ob : UU := ∑ X : C, A --> X.

Notation "⌑ S" := (pr1 (S : coslice_ob)) (at level 26).
Notation "↓ S" := (pr2 (S : coslice_ob)) (at level 26).

Definition is_coslice_mor (S S' : coslice_ob) (f : ⌑S --> ⌑S') : UU :=
  ↓S · f = ↓S'.

Definition coslice_mor (S S' : coslice_ob) : UU :=
  ∑ f : ⌑S --> ⌑S', is_coslice_mor S S' f.

Notation "⊸ f" := (pr1 (f : coslice_mor _ _)) (at level 26).
Notation "△ f" := (pr2 (f : coslice_mor _ _)) (at level 26).

Definition isaset_coslice_mor (hs : has_homsets C) (S S' : coslice_ob) : isaset (coslice_mor S S').
Proof.
  apply (isofhleveltotal2 2).
  - apply hs.
  - intro f.
    apply isasetaprop.
    apply hs.
Qed.

Definition coslice_mor_eq (hs : has_homsets C) (S S' : coslice_ob) (f g : coslice_mor S S') : ⊸ f = ⊸ g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro a.
  apply hs.
Defined.

Definition coslice_mor_id (S : coslice_ob) : coslice_mor S S.
Proof.
  exists (identity _ ).
  unfold is_coslice_mor.
  rewrite id_right.
  apply idpath.
Defined.

Definition coslice_mor_comp (S S' S'' : coslice_ob) (f : coslice_mor S S') (g : coslice_mor S' S'') : coslice_mor S S''.
Proof.
  exists (⊸ f · ⊸ g).
  unfold is_coslice_mor.
  rewrite assoc.
  rewrite (△ f).
  rewrite (△ g).
  apply idpath.
Defined.

Definition precategory_coslice_ob_mor : precategory_ob_mor.
Proof.
  exists coslice_ob.
  exact coslice_mor.
Defined.

Definition precategory_coslice_data : precategory_data.
Proof.
  exists precategory_coslice_ob_mor.
  exists coslice_mor_id.
  exact coslice_mor_comp.
Defined.

Lemma is_precategory_precategory_coslice_data (hs : has_homsets C)
  : is_precategory precategory_coslice_data.
Proof.
  repeat split; intros; simpl.
  - apply coslice_mor_eq.
    + apply hs.
    + apply id_left.
  - apply coslice_mor_eq.
    + apply hs.
    + apply id_right.
  - apply coslice_mor_eq.
    + apply hs.
    + apply assoc.
Qed.

Definition precategory_Coslice (hs : has_homsets C)
  : precategory := tpair _ _ (is_precategory_precategory_coslice_data hs).

Local Notation Coslice := precategory_Coslice.

End Coslice_Precat_Definition.

Context (Mon : monoidal_precat).

Let V := monoidal_precat_precat Mon.
Let I := monoidal_precat_unit Mon.
Let tensor := monoidal_precat_tensor Mon.
Let α' := monoidal_precat_associator Mon.
Let λ' := monoidal_precat_left_unitor Mon.
Let ρ' := monoidal_precat_right_unitor Mon.
Notation "X ⊗ Y" := (tensor (X , Y)) (at level 31).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Context (hs_V : has_homsets V).

Let coslice_precat := precategory_Coslice V I hs_V.

Notation "⌑ S" := (pr1 (S : coslice_precat)) (at level 26).
Notation "↓ S" := (pr2 (S : coslice_precat)) (at level 26).
Notation "⊸ f" := (pr1 (f : coslice_mor V I _ _)) (at level 26).
Notation "△ f" := (pr2 (f : coslice_mor V I _ _)) (at level 26).

Section Coslice_Monoidal.

Definition coslice_precat_sq := coslice_precat ⊠ coslice_precat.

Definition I_to_II : I --> I ⊗ I.
Proof.
  exact (nat_iso_to_trans_inv λ' I).
Qed.

Notation "⌊ XY" := (((XY : coslice_precat_sq) true) : coslice_precat) (at level 24).
Notation "XY ⌋" := (((XY : coslice_precat_sq) false) : coslice_precat) (at level 24).
Notation "#⌊ fg" := (fg true) (at level 24).
Notation "fg ⌋#" := (fg false) (at level 24).

Definition coslice_I : coslice_precat.
Proof.
  exists I.
  exact (id I).
Defined.

Definition coslice_tensor_on_ob : ob coslice_precat_sq -> ob coslice_precat.
Proof.
  (* the map on objects and their morphisms from I *)
  intro xy.
  exists (⌑⌊xy ⊗ ⌑xy⌋).
  exact (I_to_II · ↓⌊xy #⊗ ↓xy⌋).
Defined.

Lemma precomp_eq {C : precategory} {X Y Z : C} (f : X --> Y) (g g' : Y --> Z) (eq : g = g') : (f · g = f · g').
  rewrite eq.
  reflexivity.
Defined.

Definition coslice_tensor_on_mor : ∏ xy x'y' : ob coslice_precat_sq, xy --> x'y' -> coslice_tensor_on_ob xy --> coslice_tensor_on_ob x'y'.
Proof.
  (* the map on morphisms *)
  intros xy x'y' fg.
  exists (⊸#⌊fg #⊗ ⊸fg⌋#).
  unfold is_coslice_mor.
  simpl.
  rewrite <- assoc.
  rewrite <- (tensor_comp tensor).
  rewrite <- (△#⌊fg), <- (△fg⌋#).
  reflexivity.
Defined.

Definition coslice_tensor_data : functor_data coslice_precat_sq coslice_precat :=
  functor_data_constr coslice_precat_sq coslice_precat coslice_tensor_on_ob coslice_tensor_on_mor.

Context {coslice_tensor_idax : functor_idax coslice_tensor_data} {coslice_tensor_compax : functor_compax coslice_tensor_data}.

Definition is_functor_coslice_tensor_data : is_functor coslice_tensor_data := dirprodpair coslice_tensor_idax coslice_tensor_compax.

Definition coslice_tensor : functor coslice_precat_sq coslice_precat := tpair _ coslice_tensor_data is_functor_coslice_tensor_data.

Context {coslice_left_unitor : left_unitor coslice_tensor coslice_I} {coslice_right_unitor : right_unitor coslice_tensor coslice_I} {coslice_associator : associator coslice_tensor} {coslice_triangle_eq : triangle_eq coslice_tensor coslice_I coslice_left_unitor coslice_right_unitor
coslice_associator} {coslice_pentagon_eq : pentagon_eq coslice_tensor coslice_associator}.

Definition coslice_monoidal_precat : monoidal_precat.
Proof.
  exists coslice_precat.
  exists coslice_tensor.
  exists coslice_I.
  exists coslice_left_unitor.
  exists coslice_right_unitor.
  exists coslice_associator.
  exists coslice_triangle_eq.
  exact coslice_pentagon_eq.
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
