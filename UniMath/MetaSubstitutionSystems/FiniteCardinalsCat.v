Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.

Local Open Scope cat.

Section Finite_Cardinals_Precategory.

Definition cardinal_ob : UU := nat.

Definition cardinal_mor (X Y : cardinal_ob) : UU :=
  nat -> nat.

Definition cardinal_mor_id (X : cardinal_ob) : cardinal_mor X X.
Proof.
  exact (λ x, x).
Defined.

Definition cardinal_mor_comp (X Y Z : cardinal_ob) (f : cardinal_mor X Y) (g : cardinal_mor Y Z) : cardinal_mor X Z.
Proof.
  exact (λ x, g (f x)).
Defined.

Definition precategory_cardinal_ob_mor : precategory_ob_mor.
Proof.
  exists cardinal_ob.
  exact cardinal_mor.
Defined.

Definition precategory_cardinal_data : precategory_data.
Proof.
  exists precategory_cardinal_ob_mor.
  exists cardinal_mor_id.
  exact cardinal_mor_comp.
Defined.

Lemma is_precategory_precategory_cardinal_data
  : is_precategory precategory_cardinal_data.
Proof.
  repeat split; intros; simpl.
Qed.

Definition precategory_cardinal : precategory :=
  tpair _ _ is_precategory_precategory_cardinal_data.

End Finite_Cardinals_Precategory.
