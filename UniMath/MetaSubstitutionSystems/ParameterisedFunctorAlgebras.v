Require Import UniMath.Foundations.PartD. (* for ∑ *)
Require Import UniMath.CategoryTheory.Categories. (* for precategory *)
Require Import UniMath.CategoryTheory.functor_categories. (* for functor *)
Require Import UniMath.CategoryTheory.Monoidal. (* for binprod_precat *)
Require Import UniMath.CategoryTheory.ProductCategory. (* for has_homsets_product_precategory *)
Require Import UniMath.CategoryTheory.limits.initial. (* for Initial *)
Require Import UniMath.CategoryTheory.FunctorAlgebras. (* for FunctorAlg *)

Local Open Scope cat.

Section Parameterised_Functor_Algebra_Definition.

Context {C D : precategory} (F : functor (binprod_precat D C) C).

Definition snd (X : binprod_precat D C) : C.
Proof.
    exact (X false).
Defined.

Definition snd_mor {X Y : binprod_precat D C} (gf : X --> Y) : snd X --> snd Y.
Proof.
    exact (gf false).
Defined.

Definition parameterised_algebra_ob : UU := ∑ X : binprod_precat D C, F X --> snd X.

Definition parameterised_algebra_carrier (X : parameterised_algebra_ob) : binprod_precat D C := pr1 X.
Local Coercion parameterised_algebra_carrier : parameterised_algebra_ob >-> ob.

Definition parameterised_algebra_map (X : parameterised_algebra_ob) : F X --> snd X := pr2 X.

Definition is_parameterised_algebra_mor (X Y : parameterised_algebra_ob) (gf : parameterised_algebra_carrier X --> parameterised_algebra_carrier Y) : UU
  := parameterised_algebra_map X · (snd_mor gf) = #F gf · parameterised_algebra_map Y.

Definition parameterised_algebra_mor (X Y : parameterised_algebra_ob) : UU :=
  ∑ gf : X --> Y, is_parameterised_algebra_mor X Y gf.
Coercion mor_from_parameterised_algebra_mor (X Y : parameterised_algebra_ob) (gf : parameterised_algebra_mor X Y) : X --> Y := pr1 gf.

Definition isaset_parameterised_algebra_mor (hs_D : has_homsets D) (hs_C : has_homsets C) (X Y : parameterised_algebra_ob) : isaset (parameterised_algebra_mor X Y).
Proof.
  apply (isofhleveltotal2 2).
  - apply has_homsets_product_precategory.
    intro x.
    induction x; assumption.
  - intro f.
    apply isasetaprop.
    apply hs_C.
Qed.

Definition parameterised_algebra_mor_eq (hs : has_homsets C) {X Y : parameterised_algebra_ob} {gf g'f' : parameterised_algebra_mor X Y} : (gf : X --> Y) = g'f' ≃ gf = g'f'.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro a. apply hs.
Defined.

Lemma parameterised_algebra_mor_commutes (X Y : parameterised_algebra_ob) (gf : parameterised_algebra_mor X Y) : parameterised_algebra_map X · (snd_mor gf) = #F gf · parameterised_algebra_map Y.
Proof.
  exact (pr2 gf).
Qed.

Definition parameterised_algebra_mor_id (X : parameterised_algebra_ob) : parameterised_algebra_mor X X.
Proof.
  exists (identity _ ).
  abstract (unfold is_parameterised_algebra_mor;
            rewrite id_right ;
            rewrite functor_id;
            rewrite id_left;
            apply idpath).
Defined.

Definition parameterised_algebra_mor_comp (X Y Z : parameterised_algebra_ob) (gf : parameterised_algebra_mor X Y) (ih : parameterised_algebra_mor Y Z)
  : parameterised_algebra_mor X Z.
Proof.
  exists (gf · ih).
  unfold is_parameterised_algebra_mor.
  rewrite functor_comp.
  rewrite <- assoc.
  rewrite <- parameterised_algebra_mor_commutes.
  rewrite assoc.
  rewrite <- parameterised_algebra_mor_commutes.
  rewrite <- assoc.
  apply idpath.
Defined.

Definition precategory_parameterised_algebra_ob_mor : precategory_ob_mor.
Proof.
  exists parameterised_algebra_ob.
  exact parameterised_algebra_mor.
Defined.

Definition precategory_parameterised_algebra_data : precategory_data.
Proof.
  exists precategory_parameterised_algebra_ob_mor.
  exists parameterised_algebra_mor_id.
  exact parameterised_algebra_mor_comp.
Defined.

Lemma is_precategory_precategory_parameterised_algebra_data (hs : has_homsets C)
  : is_precategory precategory_parameterised_algebra_data.
Proof.
  repeat split; intros; simpl.
  - apply parameterised_algebra_mor_eq.
    + apply hs.
    + apply id_left.
  - apply parameterised_algebra_mor_eq.
    + apply hs.
    + apply id_right.
  - apply parameterised_algebra_mor_eq.
    + apply hs.
    + apply assoc.
Qed.

Definition precategory_ParameterisedFunctorAlg (hs : has_homsets C)
  : precategory := tpair _ _ (is_precategory_precategory_parameterised_algebra_data hs).

Lemma has_homsets_ParameterisedFunctorAlg (hs_D : has_homsets D) (hs_C : has_homsets C) : has_homsets (precategory_ParameterisedFunctorAlg hs_C).
Proof.
  intros f g.
  apply isaset_parameterised_algebra_mor; assumption.
Qed.

End Parameterised_Functor_Algebra_Definition.

Notation ParameterisedFunctorAlg := precategory_ParameterisedFunctorAlg.

Section Parameterised_InitialAlgebra_Functor.

Context {C D : precategory} (F : functor (binprod_precat D C) C).

Definition F_D (d : D) : functor C C.
Proof.
  use tpair.
  - use tpair.
    exact (λ c, F (binprod_precat_pair_of_el d c)).
    intros ? ? f.
    exact (# F (binprod_precat_pair_of_mor (identity d) f)).
  - split.
    + intro.
      simpl.
      rewrite <- id_on_binprod_precat_pair_of_el.
      apply functor_id.
    + unfold functor_compax.
      intros.
      replace (identity d) with (identity d · identity d).
      simpl.
      rewrite <- binprod_precat_comp.
      rewrite id_left.
      apply (pr2 (pr2 F)).
      rewrite id_left.
      reflexivity.
Defined.

Context (hs_C : has_homsets C).

Check ParameterisedFunctorAlg F hs_C.

(* Ideally, I'd inline this with a "transparent assert", but that doesn't exist, so... *)
Lemma μF_d'_as_F_ (d d' : D) (f : D ⟦ d, d' ⟧) (μF_ : ∏ d : D, Initial (FunctorAlg (F_D d) hs_C)) : FunctorAlg (F_D d) hs_C.
Proof.
  pose (μF_d' := InitialObject (μF_ d')).
  exists (pr1 μF_d').
  exact (#F (binprod_precat_pair_of_mor f (identity (pr1 (μF_d')))) · pr2 μF_d').
Defined.

Definition μF (μF_ : ∏ d : D, Initial (FunctorAlg (F_D d) hs_C)) : functor D C.
Proof.
  use tpair.
  - exists (λ d, pr1 (pr1 (μF_ d))).
    intros d d' f.
    exact (pr1 (pr1 ((pr2 (μF_ d)) (μF_d'_as_F_ d d' f μF_)))).
  - use tpair.
    intro d.
    unfold μF_d'_as_F_.
    simpl.
    rewrite <- id_on_binprod_precat_pair_of_el.
    rewrite (functor_id F).
    rewrite id_left.
    assert (id_eq : pr1 (pr1 (pr2 (μF_ d) (pr1 (μF_ d)))) = identity (pr1 (pr1 (μF_ d)))); [| exact id_eq].
    + pose (Y := pr2 (pr2 (μF_ d) (μF_ d)) (identity ((pr1 (μF_ d))))).
      symmetry.
      (* exact Y. *)
      admit.
    +
    unfold functor_compax.
    intros d d' d'' f g.
    simpl.
    admit.
Admitted.

End Parameterised_InitialAlgebra_Functor.
