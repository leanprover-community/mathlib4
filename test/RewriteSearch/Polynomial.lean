import Mathlib.Data.Polynomial.Eval
import Mathlib.Tactic.RewriteSearch

set_option maxHeartbeats 400000

open Polynomial

-- It would be nice if we found:
-- rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.natDegree_add_C]

-- Instead, requiring 400000 heartbeats, we find:

/--
info: Try this: rw [← @neg_sub, @natDegree_neg, @sub_eq_neg_add, @natDegree_add_C, @natDegree_neg]
-/
#guard_msgs in
example {R : Type*} [Ring R] {p : Polynomial R} {a : R} :
    natDegree (p - C a) = natDegree p := by
  rw_search
