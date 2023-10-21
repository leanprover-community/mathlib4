import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Inductions
import Mathlib.Tactic.RewriteSearch

set_option autoImplicit true

open Polynomial

/--
info: Try this: rw [@sub_eq_add_neg, ← @C_neg, @natDegree_add_C]
-/
#guard_msgs in
example {R : Type*} [Ring R] {p : Polynomial R} {a : R} :
    natDegree (p - C a) = natDegree p := by
  rw_search [-Polynomial.natDegree_sub_C]


-- This one works, but is very slow:

-- /--
-- info: Try this: rw [@X_mul, @eq_sub_iff_add_eq, @divX_mul_X_add]
-- -/
-- #guard_msgs in
-- set_option maxHeartbeats 5000000 in
-- theorem Polynomial.X_mul_divX [Field F] (p : Polynomial F) :
--     Polynomial.X * Polynomial.divX p = p - Polynomial.C (Polynomial.coeff p 0) := by
--   -- Manual proof: rw [eq_sub_iff_add_eq, Polynomial.X_mul_divX_add]
--   rw_search
