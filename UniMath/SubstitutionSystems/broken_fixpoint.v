Require Import Coq.Init.Notations.
Require Import Coq.Init.Datatypes.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Inductive Wrapper (T : Type) :=
  | Wrap : T -> Wrapper T
  .
Inductive Unwrapper :=
  | Empty : Unwrapper
  | Unwrap : Wrapper Unwrapper -> Unwrapper
  .

Definition Wrapper_size (T : Type) (w : Wrapper T) (sz : T -> nat) : nat :=
  match w with
  | Wrap _ t => sz t
  end.

Fixpoint Unwrapper_size (u : Unwrapper) : nat :=
  match u with
  | Empty => O
  | Unwrap w => Wrapper_size Unwrapper w Unwrapper_size
  end.