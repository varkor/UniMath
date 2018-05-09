Require Import UniMath.Foundations.PartD. (* for ∑ *)
Require Import UniMath.CategoryTheory.Categories. (* for precategory *)
Require Import UniMath.CategoryTheory.functor_categories. (* for functor *)
Require Import UniMath.MetaSubstitutionSystems.Monoidal2. (* for binprod_precat *)
Require Import UniMath.CategoryTheory.ProductCategory. (* for has_homsets_product_precategory *)
Require Import UniMath.CategoryTheory.limits.initial. (* for Initial *)
Require Import UniMath.CategoryTheory.FunctorAlgebras. (* for FunctorAlg *)
Require Import UniMath.MetaSubstitutionSystems.ForceTactic. (* for force, force_goal *)

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
    exact (λ c, F (binprod_ob d c)).
    intros ? ? f.
    exact (# F (binprod_mor (identity d) f)).
  - split.
    + intro.
      simpl.
      rewrite binprod_id.
      apply functor_id.
    + unfold functor_compax.
      intros.
      replace (identity d) with (identity d · identity d).
      simpl.
      rewrite binprod_comp.
      rewrite id_left.
      apply (pr2 (pr2 F)).
      rewrite id_left.
      reflexivity.
Defined.

Context (hs_C : has_homsets C).

Check ParameterisedFunctorAlg F hs_C.

Context (μF_ : ∏ d : D, Initial (FunctorAlg (F_D d) hs_C)).

Definition μF_on_ob : ob D -> ob C.
Proof.
  exact (λ d, pr1 (pr1 (μF_ d))).
Defined.

(* Ideally, I'd inline this with a "transparent assert", but that doesn't exist, so... *)
Lemma μF_d'_as_F_ {d d' : D} (f : D ⟦ d, d' ⟧) : FunctorAlg (F_D d) hs_C.
Proof.
  pose (μF_d' := InitialObject (μF_ d')).
  exists (pr1 μF_d').
  (* From F(D, μF(D')) --> F(D', μF(D')) --> μF(D'). *)
  exact (#F (binprod_mor f (identity (pr1 (μF_d')))) · pr2 μF_d').
Defined.

Definition μF_on_alg_mor {d d' : D} (f : d --> d') : pr1 (μF_ d) --> μF_d'_as_F_ f.
Proof.
  exact (pr1 ((pr2 (μF_ d)) (μF_d'_as_F_ f))).
Defined.

Definition μF_on_mor : ∏ d d' : ob D, d --> d' -> μF_on_ob d --> μF_on_ob d'.
Proof.
  intros ? ? f.
  exact (pr1 (μF_on_alg_mor f)).
Defined.

Definition μF_data : functor_data D C :=
  functor_data_constr D C μF_on_ob μF_on_mor.

(* Definition dooom {d : D} : μF_d'_as_F_ (id d) = pr1 (μF_ d).
Proof.
  pose (Z := μF_d'_as_F_ (id d)).
  unfold μF_d'_as_F_ in Z.
  pose (L := pr2 (pr1 (μF_ d))).
  simpl in L.
  Check pr2 (μF_ d) .
  rewrite binprod_id in Z.
  rewrite functor_id in Z.


  rewrite binprod_id in Z.
  Check .
  Check pr1 (μF_ d).
  pose (contr := pr2 (μF_ d) (μF_d'_as_F_ (id d))).
  unfold μF_d'_as_F_.
  apply tpair.
  unfold parameterised_algebra_carrier.
  reflexivity
Admitted.

Definition μF_d'_as_F_id {d : D} (f : pr1 (μF_ d) --> μF_d'_as_F_ (identity d)) : pr1 (μF_ d) --> pr1 (μF_ d).
Proof.
  rewrite dooom.
  unfold μF_d'_as_F_ in f.
  rewrite binprod_id in f.
  rewrite functor_id in f.

Admitted.

Definition μF_idax : functor_idax μF_data.
Proof.
  intro d.
  unfold μF_data, μF_on_ob, μF_on_mor, μF_on_alg_mor, μF_d'_as_F_.
  simpl.
  (* pr1 (μF_on_alg_mor d d (identity d)) = identity (pr1 (pr1 (μF_ d))) *)
  rewrite binprod_id.
  rewrite (functor_id F).
  rewrite id_left.
  force_goal (pr1 (pr1 (pr2 (μF_ d) (pr1 (μF_ d)))) = identity (pr1 (pr1 (μF_ d)))).
  pose (Z := pr1 (pr2 (μF_ d) (pr1 (μF_ d)))).
  pose (mor_is_contr := pr2 (pr2 (μF_ d) (pr1 (μF_ d)))).
  pose (lhs := μF_d'_as_F_id (μF_on_alg_mor (identity d))).
  pose (rhs := identity (pr1 (μF_ d))).
  assert (lhs_eq_rhs : lhs = rhs) by (
    rewrite (mor_is_contr lhs);
    rewrite (mor_is_contr rhs);
    reflexivity).
  unfold lhs, rhs in lhs_eq_rhs.
  unfold μF_on_alg_mor in lhs_eq_rhs.
  exact lhs_eq_rhs.
Admitted.

Definition μF_compax : functor_compax μF_data.
Proof.
  intros d d' d'' f g.
  unfold μF_data, functor_data_constr, μF_on_mor, μF_d'_as_F_.
  cbn.
  assert (z1 : (μF_on_mor d d' f) · (μF_on_mor d' d'' g) = (μF_on_mor d d' f) · (μF_on_mor d' d'' g)) by reflexivity.
  unfold μF_on_mor, μF_d'_as_F_ in z1.
  simpl in z1.
  Check pr2 (μF_ d).
  (* rewrite <- (id_left (identity (pr1 (μF_ d'')))). *)
  (* rewrite <- id_on_binprod_precat_pair_of_el.
  rewrite <- (binprod_precat_comp).
  transitivity (#F ((#F (f true true #, f true false)  #, f false) · (#F (g true true #, g true false) #, g false))).
  - rewrite (functor_comp F).
    rewrite <- (binprod_precat_comp).
    reflexivity.
  - apply (functor_comp F). *)
Admitted.

Definition is_functor_μF_data : is_functor μF_data := dirprodpair μF_idax μF_compax.

Definition μF : functor D C := tpair _ μF_data is_functor_μF_data. *)

End Parameterised_InitialAlgebra_Functor.
