Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.SubstitutionSystems.LamFromBindingSig.

Local Open Scope cat.

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.

Local Open Scope cat.

(* The Coq universe as a UniMath precategory. *)

Definition precategory_coq_ob_mor : precategory_ob_mor.
Proof.
  exists UU.
  exact (λ A B, A -> B).
Defined.

Definition precategory_coq_data : precategory_data.
Proof.
  exists precategory_coq_ob_mor.
  exists (λ _, (λ a, a)).
  exact (λ _ _ _ f g, (λ a, g (f a))).
Defined.

Lemma is_precategory_coq_data : is_precategory precategory_coq_data.
Proof.
  repeat split; intros; simpl.
Qed.

Definition precategory_coq : precategory :=
  tpair _ _ is_precategory_coq_data.

(* It's not possible to make observations about the properties
   of the internal Coq types, so we have to `admit` these.
   Fortunately, they're just used for sanity-checking, rather
   than any computational content, so this doesn't prevent us
   constructing anything. *)
Definition has_homsets_coq : has_homsets precategory_coq.
Proof. Admitted.

Check inl.

(* We need these definitions to get around issues in Coq's inference algorithm. *)
Definition pr1' {A B : precategory_coq} : (A × B : precategory_coq) --> A := pr1.
Definition pr2' {A B : precategory_coq} : (A × B : precategory_coq) --> B := pr2.
Definition inl' {A B : precategory_coq} : A --> (A ⨿ B) := inl.
Definition inr' {A B : precategory_coq} : B --> (A ⨿ B) := inr.

(* We can't prove properties about the class of Coq's functions, so we have to assert them instead. These are not used computationally, so using `Admitted` here does not affect the result. *)
Definition product_map_uniq (A B C: precategory_coq) (f: C --> A) (g: C --> B) : (∏ t : ∑ fg : precategory_coq ⟦ C, A × B ⟧, fg · pr1' = f × fg · pr2' = g,
t = (λ c : C, dirprodf f g (dirprodpair c c)),, idpath f,, idpath g).
Proof. Admitted.

Definition coproduct_map_uniq (A B C: precategory_coq) (f: A --> C) (g: B --> C) : (∏ t : ∑ fg : A ⨿ B -> C, inl' · fg = f × inr' · fg = g,
t = coprod_rect (λ _ : A ⨿ B, C) f g,, idpath f,, idpath g).
Proof. Admitted.

Definition unit_map_uniq (A : precategory_coq) (f : A -> unit) : (f = tounit).
Proof. Admitted.

Definition empty_map_uniq (A : precategory_coq) (f : ∅ -> A) : (f = fromempty).
  Proof. Admitted.

Definition bin_products_coq : BinProducts precategory_coq.
Proof.
  intros A B.
  use tpair.
  - exists (A × B).
    exact (pr1,, pr2).
  - unfold isBinProduct.
    intros C f g.
    use tpair.
    + use tpair.
      exact (λ c : C, dirprodf f g (dirprodpair c c)).
      split; auto.
    + simpl.
      apply product_map_uniq.
Defined.

Definition terminal_coq : Terminal precategory_coq.
Proof.
  exists unit.
  intro A.
  exists tounit.
  apply unit_map_uniq.
Defined.

Definition bin_coproducts_coq : BinCoproducts precategory_coq.
Proof.
  intros A B.
  use tpair.
  - exists (A ⨿ B).
    exact (ii1,, ii2).
  - unfold isBinCoproduct.
    intros ? f g.
    use tpair.
    + exists (coprod_rect _ f g).
      split; auto.
    + simpl.
      apply coproduct_map_uniq.
Defined.

Definition initial_coq : Initial precategory_coq.
Proof.
  exists empty.
  intro A.
  exists fromempty.
  simpl.
  apply empty_map_uniq.
Defined.

(* An axiom allowing us to use native Coq inductive definitions as HSETS. *)
Definition Coq_types_are_sets (X : UU) : isaset X. Admitted.

Definition type_as_hset (X : UU) : HSET := (X,, Coq_types_are_sets X).

Definition hset_as_type (S : HSET) : UU := pr1 S.

Print TerminalHSET.

Compute hset_as_type TerminalHSET.

Local Notation "'HSET2'":= [HSET, HSET, has_homsets_HSET].

Local Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
  apply functor_category_has_homsets.
Defined.




Check InitialHSS.

(* should be able to construct a `Signature` from an inductive type, rather than going through `BindingSigToSignature`, and then use `InitialHSS` and friends to actually construct the monad *)

Check Signature HSET has_homsets_HSET HSET has_homsets_HSET.

(* Definition bracket (T : algebra_ob Id_H) : UU := ∏ (Z : Ptd) (f : Z --> ptd_from_alg T), bracket_at T f. *)
(* Definition hss : UU := ∑ T, bracket T. *)
(* Lemma InitialHSS : Initial (hss_precategory CP H). *)

(* So, we want to construct an `Initial (hss_precategory CP H)` as an inductive type, rather than using InitialHSS. *)

Check hss_precategory BinCoproductsHSET LamSignature.

Inductive Pointed (T : UU) :=
  | Space : T -> Pointed T
  | Point : Pointed T
  .
Inductive Σ (T : UU -> UU) (Γ : UU) :=
  | Abs : T (Pointed Γ) -> Σ T Γ
  | App : T Γ -> T Γ -> Σ T Γ
  .
Inductive Term (V : UU -> UU) (Γ : UU) :=
  | Var : V Γ -> Term V Γ
  | Sig : Σ (Term V) Γ -> Term V Γ
  .
Definition Var_Id := (λ x : UU, x).
Definition Term_Id (Γ : UU) : UU := Term Var_Id Γ.
Definition Term_Id_HSET (Γ : HSET) : HSET := type_as_hset (Term_Id (hset_as_type Γ)).

Definition InductiveSignature : Initial (hss_precategory BinCoproductsHSET LamSignature).
Proof.
  (* initial object *)
  use tpair.
  (* object of category *)
  - use tpair.
    (* algebra object *)
    + use tpair.
      (* functor *)
      * use tpair.
        (* data *)
        -- use tpair.
          (* action on objects *)
          ++ exact Term_Id_HSET.
          (* action on maps *)
          ++ intros a b c. (* term_map *)
            admit.
          (* is a functor *)
        -- admit.
      * (* alg map *)
        admit.
    + (* ??? *) admit.
  - (* is initial *)
    admit.
Admitted.








Definition BindingSigToMonad
  (TC : Terminal HSET) (IC : Initial HSET) (CLC : Colims_of_shape nat_graph HSET)
  (HF : ∏ (F : HSET), is_omega_cocont (constprod_functor1 BinProductsHSET F))
  (sig : BindingSig)
  (CC : Coproducts (BindingSigIndex sig) HSET) :
  Monad HSET.
Proof.
use Monad_from_hss.
- apply (BindingSigToSignature TC sig CC).
- apply (SignatureToHSS IC CLC).
  apply (is_omega_cocont_BindingSigToSignature TC CLC HF _ _).
Defined.

Definition InductiveTypeToMonad : Monad HSET.
Proof.
  use (BindingSigToMonad _ _ _ _ _ _ _ _).
  - apply has_homsets_HSET.
  - apply BinProductsHSET.
  - apply BinCoproductsHSET.
  - apply TerminalHSET.
  - apply InitialHSET.
  - apply ColimsHSET_of_shape.
  - intros F.
    apply (is_omega_cocont_constprod_functor1 _ has_homsets_HSET2).
    apply Exponentials_functor_HSET, has_homsets_HSET.
  - admit.
  - apply CoproductsHSET.
    apply BindingSigIsaset.
Admitted.
