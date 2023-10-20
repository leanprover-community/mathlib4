import Mathlib.Data.Polynomial.Eval
import Mathlib.Tactic.RewriteSearch

open Polynomial

-- set_option trace.rw_search true

/--
info: Try this: rw [@sub_eq_add_neg, ← @C_neg, @natDegree_add_C]
-/
#guard_msgs in
example {R : Type*} [Ring R] {p : Polynomial R} {a : R} :
    natDegree (p - C a) = natDegree p := by
  rw_search [-Polynomial.natDegree_sub_C]
