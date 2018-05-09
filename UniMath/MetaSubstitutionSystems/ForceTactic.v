(* This tactic should probably not be necessary, but with all the coercions going on, I find it easier to assert that a term has a certain type, rather than try to figure out why Coq doesn't agree with me about something. *)

Require Import UniMath.MoreFoundations.Foundations.

Tactic Notation "force" "(" ident(name) ":" constr(type) ")" :=
  assert (name' : type) by (exact name);
  clear name;
  rename name' into name.

Tactic Notation "force_goal" constr(type) :=
  assert (goal' : type); [| exact goal'].
