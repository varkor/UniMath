Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.MetaSubstitutionSystems.ForceTactic.

Notation "'id' X" := (identity X) (at level 30).

Local Open Scope cat.

Section Binary_Product_Precat.

Definition binprod_precat (C D : precategory) : precategory
  := (product_precategory bool (λ x, if x then C else D)).

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

Definition iso {C: precategory_data}(a b : C) := total2 (fun f : a --> b => is_iso f).

Definition mk_iso {C : precategory} {c c' : C} (f : c --> c') (ii : is_iso f) : iso c c'.
Proof.
  exists f.
  exact ii.
Defined.

Definition is_nat_iso {C D : precategory} {F G : C ⟶ D} (μ : F ⟹ G) (ν : G ⟹ F) : UU :=
  ∏ (c : C), ∑ (ii : is_iso (μ c)), (ν c = inv_from_iso (mk_iso (μ c) ii)).

Definition nat_iso {C D : precategory} (F G : C ⟶ D) : UU
  := ∑ (μ : F ⟹ G), ∑ (ν : G ⟹ F), is_nat_iso μ ν.

Definition nat_iso_to_trans {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : F ⟹ G :=
  pr1 ν.

(* ⁻¹ *)
Definition nat_iso_to_trans_inv {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : G ⟹ F :=
pr1 (pr2 ν).

Definition is_nat_iso_id {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : UU :=
  ∏ (c : C), (nat_iso_to_trans ν c) · (nat_iso_to_trans_inv ν c) = id (F c).

End Binary_Product_Precat.

Notation "C ⊠ D" := (binprod_precat C D) (at level 38).
Notation "( c , d )" := (binprod_ob c d).
Notation "( f #, g )" := (binprod_mor f g).

Section Monoidal_Precat.

Context (C : precategory) (tensor : C ⊠ C ⟶ C) (I : C).

Notation "X ⊗ Y" := (tensor (X, Y)) (at level 31).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

(* I ⊗ - *)
Definition I_pretensor : C ⟶ C.
Proof.
    use tpair.
    - use tpair.
      exact (λ c, I ⊗ c).
      intros ? ? f.
      exact (id I #⊗ f).
    - split.
      + intro.
        simpl.
        rewrite binprod_id.
        rewrite (functor_id tensor).
        reflexivity.
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

(* - ⊗ I *)
Definition I_posttensor : C ⟶ C.
Proof.
    use tpair.
    - use tpair.
      exact (λ c, c ⊗ I).
      intros ? ? f.
      exact (f #⊗ id I).
    - split.
      + intro.
        simpl.
        rewrite binprod_id.
        rewrite (functor_id tensor).
        reflexivity.
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

(* (- ⊗ =) ⊗ ≡ *)
Definition assoc_left : (C ⊠ C) ⊠ C ⟶ C.
Proof.
  use tpair.
  - use tpair.
    exact (λ c, (c true true ⊗ c true false) ⊗ c false).
    intros ? ? f.
    exact ((f true true #⊗ f true false) #⊗ f false).
  - split.
    + intro a.
      simpl.
      repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
      rewrite binprod_id.
      rewrite (functor_id tensor).
      rewrite binprod_id.
      rewrite (functor_id tensor).
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros a b c f g.
      repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
      rewrite binprod_comp.
      rewrite (functor_comp tensor).
      rewrite binprod_comp.
      rewrite (functor_comp tensor).
      reflexivity.
Defined.

(* - ⊗ (= ⊗ ≡) *)
Definition assoc_right : (C ⊠ C) ⊠ C ⟶ C.
Proof.
  use tpair.
  - use tpair.
    exact (λ c, c true true ⊗ (c true false ⊗ c false)).
    intros ? ? f.
    exact (f true true #⊗ (f true false #⊗ f false)).
  - split.
    + intro a.
      simpl.
      repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
      rewrite binprod_id.
      rewrite (functor_id tensor).
      rewrite binprod_id.
      rewrite (functor_id tensor).
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros a b c f g.
      repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
      rewrite binprod_comp.
      rewrite (functor_comp tensor).
      rewrite binprod_comp.
      rewrite (functor_comp tensor).
      reflexivity.
Defined.

(* α *)
Definition associator : UU :=
  nat_iso assoc_left assoc_right.

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  ∏ (a b : C), pr1 ρ' a #⊗ id b = pr1 α' ((a, I), b) · id a #⊗ pr1 λ' b.

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗ b, c), d) · pr1 α' ((a, b), c ⊗ d) = pr1 α' ((a, b), c) #⊗ id d · pr1 α' ((a, b ⊗ c), d) · id a #⊗ pr1 α' ((b, c), d).

Definition monoidal_struct : UU :=
  ∑ (λ' : left_unitor), ∑ (ρ' : right_unitor), ∑ (α' : associator), (triangle_eq λ' ρ' α') × (pentagon_eq α').

Definition is_strict (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  (is_nat_iso_id λ') × (is_nat_iso_id ρ') × (is_nat_iso_id α').

End Monoidal_Precat.

Definition monoidal_precat : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C, monoidal_struct C tensor I.

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
  ∑ M : monoidal_precat, is_strict (monoidal_precat_precat M) (monoidal_precat_tensor M) (monoidal_precat_unit M) (monoidal_precat_left_unitor M) (monoidal_precat_right_unitor M) (monoidal_precat_associator M).

Section Monoidal_Functor.

Context (Mon_C Mon_D : monoidal_precat).

Let C := monoidal_precat_precat Mon_C.
Let tensor_C := monoidal_precat_tensor Mon_C.
Notation "X ⊗_C Y" := (tensor_C (X , Y)) (at level 31).
Notation "f #⊗_C g" := (# tensor_C (f #, g)) (at level 31).
Let I_C := monoidal_precat_unit Mon_C.
Let α_C := monoidal_precat_associator Mon_C.
Let λ_C := monoidal_precat_left_unitor Mon_C.
Let ρ_C := monoidal_precat_right_unitor Mon_C.
Let D := monoidal_precat_precat Mon_D.
Let tensor_D := monoidal_precat_tensor Mon_D.
Notation "X ⊗_D Y" := (tensor_D (X , Y)) (at level 31).
Notation "f #⊗_D g" := (# tensor_D (f #, g)) (at level 31).
Let I_D := monoidal_precat_unit Mon_D.
Let α_D := monoidal_precat_associator Mon_D.
Let λ_D := monoidal_precat_left_unitor Mon_D.
Let ρ_D := monoidal_precat_right_unitor Mon_D.

Section Monoidal_Functor_Conditions.

Context (F : C ⟶ D).

Definition monoidal_functor_map_dom : C ⊠ C ⟶ D.
use tpair.
- use tpair.
  exact (λ c, F (c true) ⊗_D F (c false)).
  intros ? ? f.
  exact (#F (f true) #⊗_D #F (f false)).
- split.
  + intro.
    simpl.
    repeat rewrite (binprod_proj_id a).
    repeat rewrite functor_id.
    rewrite binprod_id.
    rewrite (functor_id tensor_D).
    reflexivity.
  + unfold functor_compax.
    simpl.
    intros.
    repeat rewrite (binprod_proj_comp f).
    repeat rewrite functor_comp.
    rewrite binprod_comp.
    rewrite (functor_comp tensor_D).
    reflexivity.
Defined.

Definition monoidal_functor_map_codom : C ⊠ C ⟶ D.
use tpair.
- use tpair.
  exact (λ c, F (c true ⊗_C c false)).
  intros ? ? f.
  exact (#F (f true #⊗_C f false)).
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
  pr1 μ (x, y) #⊗_D id F(z) · pr1 μ (x ⊗_C y, z) · #F (pr1 α_C ((x, y), z))
  =
  pr1 α_D ((F x, F y), F z) · id (F x) #⊗_D pr1 μ (y, z) · pr1 μ (x, y ⊗_C z).

Definition monoidal_functor_unitality (ϵ : I_D --> F I_C) (μ : monoidal_functor_map) :=
  ∏ (x : C),
  (pr1 λ_D (F x) = ϵ #⊗_D (id (F x)) · pr1 μ (I_C, x) · #F (pr1 λ_C x))
  ×
  (pr1 ρ_D (F x) = (id (F x)) #⊗_D ϵ · pr1 μ (x, I_C) · #F (pr1 ρ_C x)).

End Monoidal_Functor_Conditions.

Definition lax_monoidal_functor : UU :=
  ∑ F : C ⟶ D, ∑ ϵ : I_D --> F I_C, ∑ μ : monoidal_functor_map F, (monoidal_functor_associativity F μ) × (monoidal_functor_unitality F ϵ μ).

Definition strong_monoidal_functor : UU :=
  ∑ L : lax_monoidal_functor,
  (is_iso (pr1 (pr2 L))) (* ϵ is an iso *)
  ×
  (∏ (x y : C), is_iso (pr1 (pr1 (pr2 (pr2 L))) (x, y))) (* all μ_x,y are isos *).

End Monoidal_Functor.
