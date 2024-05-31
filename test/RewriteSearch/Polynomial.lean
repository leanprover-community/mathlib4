import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Init.Core
import Mathlib.Tactic.RewriteSearch

set_option autoImplicit true

open Polynomial

-- Fails, but used to work prior to `rw?` moving to `lean4`.
-- -- info: Try this: rw [@natDegree_sub, @sub_eq_neg_add, @natDegree_add_C, @natDegree_neg]
-- #guard_msgs(drop info) in
-- example {R : Type*} [Ring R] {p : Polynomial R} {a : R} :
--     natDegree (p - C a) = natDegree p := by
--   rw_search [-Polynomial.natDegree_sub_C, -sub_eq_neg_add]


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


-- All rewrite-only lemmas from `Mathlib.Algebra.Polynomial.Degree.Definitions`,
-- whose statements are equalities.
-- TODO: `rw_search` should handle `iff` as well.

universe u v

open
  Finset
  Finsupp
  Polynomial

-- Polynomial.degree_of_subsingleton.{u}
#guard_msgs(drop info) in
example {R : Type u} [Semiring R] {p : Polynomial R} [Subsingleton R] :
    Polynomial.degree p = ⊥ := by
  rw_search [-Polynomial.degree_of_subsingleton]
  -- Mathlib proof:
  -- rw [Subsingleton.elim p 0, degree_zero]
  done

-- Fails:
-- -- Polynomial.natDegree_of_subsingleton.{u}
-- example {R : Type u} [Semiring R] {p : Polynomial R}
--     [Subsingleton R] : Polynomial.natDegree p = 0 := by
--   rw_search [-Polynomial.natDegree_of_subsingleton]
--   -- Mathlib proof:
--   -- rw [Subsingleton.elim p 0, natDegree_zero]
--   done

-- Polynomial.degree_C_mul_X_pow.{u}
#guard_msgs(drop info) in
example {R : Type u} {a : R} [Semiring R] (n : ℕ) (ha : a ≠ 0) :
    Polynomial.degree (Polynomial.C a * Polynomial.X ^ n) = n := by
  rw_search [-Polynomial.degree_C_mul_X_pow]
  -- Mathlib proof:
  -- rw [C_mul_X_pow_eq_monomial, degree_monomial n ha]
  done

-- Fails:
-- -- Polynomial.Monic.eq_X_add_C.{u}
-- example {R : Type u} [Semiring R] {p : Polynomial R} (hm : Polynomial.Monic p)
--     (hnd : Polynomial.natDegree p = 1) : p = Polynomial.X + Polynomial.C (Polynomial.coeff p 0) := by
--   rw_search [-Polynomial.Monic.eq_X_add_C]
--   -- Mathlib proof:
--   -- rw [← one_mul X, ← C_1, ← hm.coeff_natDegree, hnd, ← eq_X_add_C_of_natDegree_le_one hnd.le]
--   done

-- Fails:
-- -- Polynomial.natDegree_intCast.{u}
-- example {R : Type u} [Ring R] (n : ℤ) : Polynomial.natDegree (n : R[X]) = 0 := by
--   rw_search [-Polynomial.natDegree_intCast]
--   -- Mathlib proof:
--   -- rw [← C_eq_intCast, natDegree_C]
--   done

-- Fails:
-- -- Polynomial.leadingCoeff_neg.{u}
-- example {R : Type u} [Ring R] (p : Polynomial R) :
--     Polynomial.leadingCoeff (-p) = -Polynomial.leadingCoeff p := by
--   rw_search [-Polynomial.leadingCoeff_neg]
--   -- Mathlib proof:
--   -- rw [leadingCoeff, leadingCoeff, natDegree_neg, coeff_neg]
--   done

-- Polynomial.degree_add_eq_right_of_degree_lt.{u}
#guard_msgs(drop info) in
example {R : Type u} [Semiring R] {p q : Polynomial R}
    (h : Polynomial.degree p < Polynomial.degree q) : Polynomial.degree (p + q) = Polynomial.degree q := by
  rw_search [-Polynomial.degree_add_eq_right_of_degree_lt]
  -- Mathlib proof:
  -- rw [add_comm, degree_add_eq_left_of_degree_lt h]
  done

-- Polynomial.leadingCoeff_C_mul_X_pow.{u}
#guard_msgs(drop info) in
example {R : Type u} [Semiring R] (a : R) (n : ℕ) :
    Polynomial.leadingCoeff (Polynomial.C a * Polynomial.X ^ n) = a := by
  rw_search [-Polynomial.leadingCoeff_C_mul_X_pow]
  -- Mathlib proof:
  -- rw [C_mul_X_pow_eq_monomial, leadingCoeff_monomial]
  done

-- Polynomial.C_mul_X_pow_eq_self.{u}
#guard_msgs(drop info) in
example {R : Type u} [Semiring R] {p : Polynomial R}
    (h : Finset.card (Polynomial.support p) ≤ 1) :
    Polynomial.C (Polynomial.leadingCoeff p) * Polynomial.X ^ Polynomial.natDegree p = p := by
  rw_search [-Polynomial.C_mul_X_pow_eq_self]
  -- Mathlib proof:
  -- rw [C_mul_X_pow_eq_monomial, monomial_natDegree_leadingCoeff_eq_self h]
  done

-- Fails:
-- -- Polynomial.degree_linear.{u}
-- example {R : Type u} {a b : R} [Semiring R] (ha : a ≠ 0) :
--     Polynomial.degree (Polynomial.C a * Polynomial.X + Polynomial.C b) = 1 := by
--   rw_search [-Polynomial.degree_linear]
--   -- Mathlib proof:
--   -- rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha, degree_C_mul_X ha]
--   done

-- Polynomial.natDegree_linear.{u}
#guard_msgs(drop info) in
example {R : Type u} {a b : R} [Semiring R] (ha : a ≠ 0) :
    Polynomial.natDegree (Polynomial.C a * Polynomial.X + Polynomial.C b) = 1 := by
  rw_search [-Polynomial.natDegree_linear]
  -- Mathlib proof:
  -- rw [natDegree_add_C, natDegree_C_mul_X a ha]
  done

-- Fails:
-- -- Polynomial.degree_X_pow.{u}
-- example {R : Type u} [Semiring R] [Nontrivial R] (n : ℕ) :
--     Polynomial.degree (Polynomial.X ^ n : R[X]) = n := by
--   rw_search [-Polynomial.degree_X_pow]
--   -- Mathlib proof:
--   -- rw [X_pow_eq_monomial, degree_monomial _ (one_ne_zero' R)]
--   done

-- Fails:
-- -- Polynomial.degree_X_sub_C.{u}
-- #guard_msgs(drop info) in
-- example {R : Type u} [Ring R] [Nontrivial R] (a : R) :
--     Polynomial.degree (Polynomial.X - Polynomial.C a) = 1 := by
--   rw_search [-Polynomial.degree_X_sub_C]
--   -- Mathlib proof:
--   -- rw [sub_eq_add_neg, ← map_neg C a, degree_X_add_C]
--   done

-- Polynomial.natDegree_X_sub_C.{u}
#guard_msgs(drop info) in
example {R : Type u} [Ring R] [Nontrivial R] (x : R) :
    Polynomial.natDegree (Polynomial.X - Polynomial.C x) = 1 := by
  rw_search [-Polynomial.natDegree_X_sub_C]
  -- Mathlib proof:
  -- rw [natDegree_sub_C, natDegree_X]
  done

-- Polynomial.nextCoeff_X_sub_C.{v}
#guard_msgs(drop info) in
example {S : Type v} [Ring S] (c : S) :
    Polynomial.nextCoeff (Polynomial.X - Polynomial.C c) = -c := by
  rw_search [-Polynomial.nextCoeff_X_sub_C]
  -- Mathlib proof:
  -- rw [sub_eq_add_neg, ← map_neg C c, nextCoeff_X_add_C]
  done

-- Polynomial.degree_X_pow_sub_C.{u}
#guard_msgs(drop info) in
example {R : Type u} [Ring R] [Nontrivial R] {n : ℕ} (hn : 0 < n) (a : R) :
    Polynomial.degree (Polynomial.X ^ n - Polynomial.C a) = n := by
  rw_search [-Polynomial.degree_X_pow_sub_C]
  -- Mathlib proof:
  -- rw [sub_eq_add_neg, ← map_neg C a, degree_X_pow_add_C hn]
  done

-- Polynomial.natDegree_X_pow_sub_C.{u}
#guard_msgs(drop info) in
example {R : Type u} [Ring R] [Nontrivial R] {n : ℕ} {r : R} :
    Polynomial.natDegree (Polynomial.X ^ n - Polynomial.C r) = n := by
  rw_search [-Polynomial.natDegree_X_pow_sub_C]
  -- Mathlib proof:
  -- rw [sub_eq_add_neg, ← map_neg C r, natDegree_X_pow_add_C]
  done

-- Fails:
-- -- Polynomial.leadingCoeff_X_sub_C.{v}
-- example {S : Type v} [Ring S] (r : S) :
--     Polynomial.leadingCoeff (Polynomial.X - Polynomial.C r) = 1 := by
--   rw_search [-Polynomial.leadingCoeff_X_sub_C]
--   -- Mathlib proof:
--   -- rw [sub_eq_add_neg, ← map_neg C r, leadingCoeff_X_add_C]
--   done
