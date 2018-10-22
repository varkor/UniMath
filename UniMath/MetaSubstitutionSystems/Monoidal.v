Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.MetaSubstitutionSystems.ForceTactic.

Notation "'id' X" := (identity X) (at level 30).

Local Open Scope cat.

Section Binary_Product_Precat.

Definition binprod_precat (C D : precategory) : precategory
  := (product_precategory (λ (x : bool), if x then C else D)).

Local Notation "C ⊠ D" := (binprod_precat C D) (at level 38).

Definition binprod_ob {C D : precategory} (c : C) (d : D) : C ⊠ D.
Proof.
  intro x.
  induction x.
  exact c.
  exact d.
Defined.

Local Notation "( c , d )" := (binprod_ob c d).

Definition binprod_mor {C D : precategory} {c c' : C} {d d' : D} (f : c --> c') (g : d --> d') : (c, d) --> (c', d').
  intro x.
  induction x.
  exact f.
  exact g.
Defined.

Local Notation "( f #, g )" := (binprod_mor f g).

Definition binprod_id {C D : precategory} (c : C) (d : D) : (id c #, id d) = id (c, d).
Proof.
  apply funextsec.
  intro x.
  induction x; reflexivity.
Defined.

Definition binprod_proj_id {C D : precategory} (cd : C ⊠ D) (b : bool) : (id cd) b = id cd b.
Proof.
  reflexivity.
Defined.

Definition binprod_comp {C D : precategory} (c c' c'' : C) (d d' d'' : D) (f : c --> c') (f' : c' --> c'') (g : d --> d') (g' : d' --> d'') : (f · f' #, g · g') = (f #, g) · (f' #, g').
Proof.
  apply funextsec.
  intro x.
  induction x; reflexivity.
Defined.

Definition binprod_proj_comp {C D : precategory} {cd cd' cd'' : C ⊠ D} (f : cd --> cd') (g : cd' --> cd'') (b : bool) : (f · g) b = f b · g b.
Proof.
  reflexivity.
Defined.

Definition iso {C: precategory_data} (a b : C) := total2 (fun f : a --> b => is_iso f).

Definition mk_iso {C : precategory} {c c' : C} {f : c --> c'} (ii : is_iso f) : iso c c'.
Proof.
  exists f.
  exact ii.
Defined.

(* Proof by Anthony Bordg (https://github.com/UniMath/UniMath/pull/722/files). *)
Definition is_iso_binprod_iso {C D : precategory} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_iso f)
  (g_is_iso : is_iso g) : is_iso (f #, g).
Proof.
  apply (is_iso_qinv (f #, g) (inv_from_iso (isopair f f_is_iso) #, inv_from_iso (isopair g g_is_iso))).
  apply dirprodpair.
  - transitivity ((isopair f f_is_iso) · (inv_from_iso (isopair f f_is_iso)) #, (isopair g g_is_iso) · (inv_from_iso (isopair g g_is_iso))).
    + symmetry.
      apply binprod_comp.
    + rewrite 2 iso_inv_after_iso.
      apply binprod_id.
  - transitivity ((inv_from_iso (isopair f f_is_iso)) · (isopair f f_is_iso) #, (inv_from_iso (isopair g g_is_iso)) · (isopair g g_is_iso)).
    + symmetry.
      apply binprod_comp.
    + rewrite 2 iso_after_iso_inv.
      apply binprod_id.
Defined.

Definition is_nat_iso {C D : precategory} {F G : C ⟶ D} (μ : F ⟹ G) : UU :=
  ∏ (c : C), is_iso (μ c).

Definition is_nat_id {C D : precategory} {F : C ⟶ D} (μ : F ⟹ F) : UU :=
  ∏ (c : C), μ c = id (F c).

Definition nat_iso {C D : precategory} (F G : C ⟶ D) : UU
  := ∑ (μ : F ⟹ G), is_nat_iso μ.

Definition iso_inv_after_iso' {C : precategory} {a b : C} (f : a --> b) (f' : iso a b) (deref : pr1 f' = f) : f · inv_from_iso f' = identity _.
Proof.
  rewrite <- deref.
  exact (iso_inv_after_iso f').
Defined.

Definition iso_after_iso_inv' {C : precategory} {a b : C} (f : a --> b) (f' : iso a b) (deref : pr1 f' = f) : inv_from_iso f' · f = identity _.
Proof.
  rewrite <- deref.
  exact (iso_after_iso_inv f').
Defined.

Definition nat_iso_inv {C D : precategory} {F G : C ⟶ D} (μ : nat_iso F G) : nat_iso G F.
Proof.
  pose (iso := (λ c, mk_iso (pr2 μ c))).
  pose (inv := (λ c, inv_from_iso (iso c))).
  use tpair.
  - exists inv.
    intros c c' f.
    pose (coher := pr2 (pr1 μ) c c' f).
    pose (coher_inv := maponpaths (λ p, inv c · p · inv c') coher).
    simpl in coher_inv.
    repeat rewrite <- assoc in coher_inv.
    unfold inv in coher_inv.
    assert (deref' : pr1 (iso c') = (pr1 μ) c') by reflexivity.
    force (coher_inv : (inv_from_iso (iso c) · (# F f · ((pr1 μ) c' · inv_from_iso (iso c'))) = inv_from_iso (iso c) · (pr1 (pr1 μ) c · (# G f · inv_from_iso (iso c'))))).
    rewrite (iso_inv_after_iso' ((pr1 μ) c') (iso c') deref') in coher_inv.
    rewrite id_right in coher_inv.
    repeat rewrite assoc in coher_inv.
    assert (deref : pr1 (iso c) = (pr1 μ) c) by reflexivity.
    force (coher_inv : (inv_from_iso (iso c) · # F f = inv_from_iso (iso c) · (pr1 μ) c · # G f · inv_from_iso (iso c'))).
    rewrite (iso_after_iso_inv' ((pr1 μ) c) (iso c) deref) in coher_inv.
    rewrite id_left in coher_inv.
    unfold inv.
    symmetry.
    assumption.
  - intro c.
    exact (is_iso_inv_from_iso (iso c)).
Defined.


Definition nat_iso_to_trans {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : F ⟹ G :=
  pr1 ν.

(* ⁻¹ *)
Definition nat_iso_to_trans_inv {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : G ⟹ F :=
  pr1 (nat_iso_inv ν).

Definition is_nat_iso_id {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : UU :=
  ∏ (c : C), (nat_iso_to_trans ν c) · (nat_iso_to_trans_inv ν c) = id (F c).

End Binary_Product_Precat.

Notation "C ⊠ D" := (binprod_precat C D) (at level 38).
Notation "( c , d )" := (binprod_ob c d).
Notation "( f #, g )" := (binprod_mor f g).

Section Monoidal_Precat.

Context {C : precategory} (tensor : C ⊠ C ⟶ C) (I : C).

Notation "X ⊗⊗ Y" := (tensor (X, Y)) (at level 31).
Notation "f #⊗⊗ g" := (#tensor (f #, g)) (at level 31).

Definition tensor_id {X Y : C} : id X #⊗⊗ id Y = id (X ⊗⊗ Y).
Proof.
  rewrite binprod_id.
  rewrite (functor_id tensor).
  reflexivity.
Defined.

Definition tensor_comp {X Y Z X' Y' Z' : C} (f : X --> Y) (g : Y --> Z) (f' : X' --> Y') (g' : Y' --> Z') : (f · g) #⊗⊗ (f' · g') = f #⊗⊗ f' · g #⊗⊗ g'.
Proof.
  rewrite binprod_comp.
  rewrite (functor_comp tensor).
  reflexivity.
Defined.

Definition is_iso_tensor_iso {X Y X' Y' : C} {f : X --> Y} {g : X' --> Y'} (f_is_iso : is_iso f)
(g_is_iso : is_iso g) : is_iso (f #⊗⊗ g).
Proof.
  exact (functor_on_is_iso_is_iso (is_iso_binprod_iso f_is_iso g_is_iso)).
Defined.

(* I ⊗⊗ - *)
Definition I_pretensor : C ⟶ C.
Proof.
    use tpair.
    - use tpair.
      exact (λ c, I ⊗⊗ c).
      intros ? ? f.
      exact (id I #⊗⊗ f).
    - split.
      + intro.
        simpl.
        apply tensor_id.
      + unfold functor_compax.
        simpl.
        intros.
        replace (id I) with (id I · id I) by (
          rewrite id_left;
          reflexivity
        ).
        rewrite binprod_comp.
        rewrite id_left.
        rewrite (functor_comp tensor).
        reflexivity.
Defined.

(* λ *)
Definition left_unitor : UU :=
  nat_iso I_pretensor (functor_identity C).

(* - ⊗⊗ I *)
Definition I_posttensor : C ⟶ C.
Proof.
    use tpair.
    - use tpair.
      exact (λ c, c ⊗⊗ I).
      intros ? ? f.
      exact (f #⊗⊗ id I).
    - split.
      + intro.
        simpl.
        apply tensor_id.
      + unfold functor_compax.
        simpl.
        intros.
        replace (id I) with (id I · id I) by (
          rewrite id_left;
          reflexivity
        ).
        rewrite binprod_comp.
        rewrite id_left.
        rewrite (functor_comp tensor).
        reflexivity.
Defined.

(* ρ *)
Definition right_unitor : UU :=
  nat_iso I_posttensor (functor_identity C).

(* (- ⊗⊗ =) ⊗⊗ ≡ *)
Definition assoc_left : (C ⊠ C) ⊠ C ⟶ C.
Proof.
  use tpair.
  - use tpair.
    exact (λ c, (c true true ⊗⊗ c true false) ⊗⊗ c false).
    intros ? ? f.
    exact ((f true true #⊗⊗ f true false) #⊗⊗ f false).
  - split.
    + intro a.
      simpl.
      repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
      do 2 rewrite tensor_id.
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros a b c f g.
      repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
      do 2 rewrite tensor_comp.
      reflexivity.
Defined.

(* - ⊗⊗ (= ⊗⊗ ≡) *)
Definition assoc_right : (C ⊠ C) ⊠ C ⟶ C.
Proof.
  use tpair.
  - use tpair.
    exact (λ c, c true true ⊗⊗ (c true false ⊗⊗ c false)).
    intros ? ? f.
    exact (f true true #⊗⊗ (f true false #⊗⊗ f false)).
  - split.
    + intro a.
      simpl.
      repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
      do 2 rewrite tensor_id.
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros a b c f g.
      repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
      do 2 rewrite tensor_comp.
      reflexivity.
Defined.

(* α *)
Definition associator : UU :=
  nat_iso assoc_left assoc_right.

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  ∏ (a b : C), pr1 ρ' a #⊗⊗ id b = pr1 α' ((a, I), b) · id a #⊗⊗ pr1 λ' b.

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗⊗ b, c), d) · pr1 α' ((a, b), c ⊗⊗ d) = pr1 α' ((a, b), c) #⊗⊗ id d · pr1 α' ((a, b ⊗⊗ c), d) · id a #⊗⊗ pr1 α' ((b, c), d).

Definition is_strict (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  (is_nat_iso_id λ') × (is_nat_iso_id ρ') × (is_nat_iso_id α').

End Monoidal_Precat.

Definition monoidal_precat : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor,
  (triangle_eq tensor I λ' ρ' α') × (pentagon_eq tensor α').

Section Monoidal_Precat_Accessors.

Context (M : monoidal_precat).

Definition monoidal_precat_precat := pr1 M.

Definition monoidal_precat_tensor := pr1 (pr2 M).

Definition monoidal_precat_unit := pr1 (pr2 (pr2 M)).

Definition monoidal_precat_left_unitor := pr1 (pr2 (pr2 (pr2 M))).

Definition monoidal_precat_right_unitor := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition monoidal_precat_associator := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

Definition monoidal_precat_eq := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

End Monoidal_Precat_Accessors.

Definition strict_monoidal_precat : UU :=
  ∑ M : monoidal_precat, is_strict (monoidal_precat_tensor M) (monoidal_precat_unit M) (monoidal_precat_left_unitor M) (monoidal_precat_right_unitor M) (monoidal_precat_associator M).

Section Monoidal_Functor.

Context (Mon_C Mon_D : monoidal_precat).

Let C := monoidal_precat_precat Mon_C.
Let tensor_C := monoidal_precat_tensor Mon_C.
Notation "X ⊗⊗_C Y" := (tensor_C (X , Y)) (at level 31).
Notation "f #⊗⊗_C g" := (# tensor_C (f #, g)) (at level 31).
Let I_C := monoidal_precat_unit Mon_C.
Let α_C := monoidal_precat_associator Mon_C.
Let λ_C := monoidal_precat_left_unitor Mon_C.
Let ρ_C := monoidal_precat_right_unitor Mon_C.
Let D := monoidal_precat_precat Mon_D.
Let tensor_D := monoidal_precat_tensor Mon_D.
Notation "X ⊗⊗_D Y" := (tensor_D (X , Y)) (at level 31).
Notation "f #⊗⊗_D g" := (# tensor_D (f #, g)) (at level 31).
Let I_D := monoidal_precat_unit Mon_D.
Let α_D := monoidal_precat_associator Mon_D.
Let λ_D := monoidal_precat_left_unitor Mon_D.
Let ρ_D := monoidal_precat_right_unitor Mon_D.

Section Monoidal_Functor_Conditions.

Context (F : C ⟶ D).

Definition monoidal_functor_map_dom : C ⊠ C ⟶ D.
use tpair.
- use tpair.
  exact (λ c, F (c true) ⊗⊗_D F (c false)).
  intros ? ? f.
  exact (#F (f true) #⊗⊗_D #F (f false)).
- split.
  + intro.
    simpl.
    repeat rewrite (binprod_proj_id a).
    repeat rewrite functor_id.
    apply tensor_id.
  + unfold functor_compax.
    simpl.
    intros.
    repeat rewrite (binprod_proj_comp f).
    repeat rewrite functor_comp.
    apply tensor_comp.
Defined.

Definition monoidal_functor_map_codom : C ⊠ C ⟶ D.
use tpair.
- use tpair.
  exact (λ c, F (c true ⊗⊗_C c false)).
  intros ? ? f.
  exact (#F (f true #⊗⊗_C f false)).
- split.
  + intro.
    simpl.
    repeat rewrite (binprod_proj_id a).
    rewrite binprod_id.
    rewrite (functor_id tensor_C).
    rewrite functor_id.
    reflexivity.
  + unfold functor_compax.
    simpl.
    intros.
    repeat rewrite (binprod_proj_comp f).
    rewrite binprod_comp.
    rewrite (functor_comp tensor_C).
    rewrite functor_comp.
    reflexivity.
Defined.

Definition monoidal_functor_map :=
  monoidal_functor_map_dom ⟹ monoidal_functor_map_codom.

Definition monoidal_functor_associativity (μ : monoidal_functor_map) :=
  ∏ (x y z : C),
  pr1 μ (x, y) #⊗⊗_D id F(z) · pr1 μ (x ⊗⊗_C y, z) · #F (pr1 α_C ((x, y), z))
  =
  pr1 α_D ((F x, F y), F z) · id (F x) #⊗⊗_D pr1 μ (y, z) · pr1 μ (x, y ⊗⊗_C z).

Definition monoidal_functor_unitality (ϵ : I_D --> F I_C) (μ : monoidal_functor_map) :=
  ∏ (x : C),
  (pr1 λ_D (F x) = ϵ #⊗⊗_D (id (F x)) · pr1 μ (I_C, x) · #F (pr1 λ_C x))
  ×
  (pr1 ρ_D (F x) = (id (F x)) #⊗⊗_D ϵ · pr1 μ (x, I_C) · #F (pr1 ρ_C x)).

End Monoidal_Functor_Conditions.

Definition lax_monoidal_functor : UU :=
  ∑ F : C ⟶ D, ∑ ϵ : I_D --> F I_C, ∑ μ : monoidal_functor_map F, (monoidal_functor_associativity F μ) × (monoidal_functor_unitality F ϵ μ).

Definition strong_monoidal_functor : UU :=
  ∑ L : lax_monoidal_functor,
  (is_iso (pr1 (pr2 L))) (* ϵ is an iso *)
  ×
  (is_nat_iso (pr1 (pr2 (pr2 L)))). (* μ is an iso *)

End Monoidal_Functor.

Definition strong_monoidal_functor_functor {Mon Mon' : monoidal_precat} (U : strong_monoidal_functor Mon Mon') := pr1 (pr1 U).
Coercion strong_monoidal_functor_functor : strong_monoidal_functor >-> functor.

Section Precategory_of_Monoids.

Context (Mon : monoidal_precat).

Let C := monoidal_precat_precat Mon.
Let tensor := monoidal_precat_tensor Mon.
Notation "X ⊗⊗ Y" := (tensor (X , Y)) (at level 31).
Notation "f #⊗⊗ g" := (# tensor (f #, g)) (at level 31).
Let I := monoidal_precat_unit Mon.
Let α' := monoidal_precat_associator Mon.
Let λ' := monoidal_precat_left_unitor Mon.
Let ρ' := monoidal_precat_right_unitor Mon.

Definition monoid_ob_data : UU :=
  ∑ X : C, (X ⊗⊗ X --> X) × (I --> X).

Definition is_monoid_ob (X : C) (μ : X ⊗⊗ X --> X) (η : I --> X) : UU :=
	(μ #⊗⊗ id X · μ = pr1 α' ((X, X), X) · id X #⊗⊗ μ · μ) × (* Pentagon diagram *)
	(pr1 λ' X = η #⊗⊗ id X · μ) × (pr1 ρ' X = id X #⊗⊗ η · μ). (* Unitor diagrams *)

Definition monoid_ob : UU :=
	∑ X : monoid_ob_data, is_monoid_ob (pr1 X) (pr1 (pr2 X)) (pr2 (pr2 X)).

Definition monoid_carrier (X : monoid_ob) : C := pr1 (pr1 X).
Local Coercion monoid_carrier : monoid_ob >-> ob.

Definition monoid_mult (X : monoid_ob) := pr1 (pr2 (pr1 X)).

Definition monoid_unit (X : monoid_ob) := pr2 (pr2 (pr1 X)).

Definition is_monoid_mor (X Y : monoid_ob) (f : monoid_carrier X --> monoid_carrier Y) : UU :=
	((@monoid_mult X) · f = f #⊗⊗ f · (@monoid_mult Y)) ×
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
  rewrite tensor_id.
  rewrite id_left.
  rewrite id_right.
  split; apply idpath.
Defined.

Definition monoid_mor_comp (X Y Z : monoid_ob) (f : monoid_mor X Y) (g : monoid_mor Y Z) : monoid_mor X Z.
Proof.
	use tpair.
	- exact (f · g).
	- split.
    + rewrite assoc.
      force_goal (monoid_mult X · pr1 f · g = # tensor (f · g #, f · g) · monoid_mult Z).
      rewrite (pr1 (pr2 f)).
      rewrite <- assoc.
      rewrite binprod_comp.
      force_goal (# tensor (pr1 f #, pr1 f) · (monoid_mult Y · pr1 g) = # tensor ((f #, f) · (g #, g)) · monoid_mult Z).
      rewrite functor_comp.
      rewrite (pr1 (pr2 g)).
			rewrite assoc.
			reflexivity.
		+ rewrite assoc.
			rewrite <- (pr2 (pr2 g)).
			rewrite <- (pr2 (pr2 f)).
			apply idpath.
Defined.

Definition precategory_monoid_ob_mor : precategory_ob_mor.
Proof.
  exists monoid_ob.
  exact monoid_mor.
Defined.

Definition precategory_monoid_data : precategory_data.
Proof.
  exists precategory_monoid_ob_mor.
  exists monoid_mor_id.
  exact monoid_mor_comp.
Defined.

Lemma is_precategory_precategory_monoid_data (hs : has_homsets C)
  : is_precategory precategory_monoid_data.
Proof.
  repeat split; intros; simpl.
  - apply monoid_mor_eq.
    + apply hs.
    + apply id_left.
  - apply monoid_mor_eq.
    + apply hs.
    + apply id_right.
  - apply monoid_mor_eq.
    + apply hs.
    + apply assoc.
Qed.

Definition precategory_monoid (hs : has_homsets C)
  : precategory := tpair _ _ (is_precategory_precategory_monoid_data hs).

Local Notation monoid := precategory_monoid.

End Precategory_of_Monoids.
