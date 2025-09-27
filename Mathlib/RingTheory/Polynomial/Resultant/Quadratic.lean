/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

- `discrim a b c`: the discriminant of a quadratic `a * (x * x) + b * x + c` is `b * b - 4 * a * c`.

## Main statements

- `quadratic_eq_zero_iff`: roots of a quadratic can be written as
  `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`, where `s` is a square root of the discriminant.
- `quadratic_ne_zero_of_discrim_ne_sq`: if the discriminant has no square root,
  then the corresponding quadratic has no root.
- `discrim_le_zero`: if a quadratic is always non-negative, then its discriminant is non-positive.
- `discrim_le_zero_of_nonpos`, `discrim_lt_zero`, `discrim_lt_zero_of_neg`: versions of this
  statement with other inequalities.

## Tags

polynomial, quadratic, discriminant, root
-/

--assert_not_exists Finite Finset

open Filter

namespace Polynomial

section Ring

variable {R : Type*}

variable [CommRing R] {p : R[X]}

@[simp] lemma discrim_neg (hp : p.degree = 2) : (-p).disc = p.disc := by
  have e0 : (-p).degree = 2 := by
    simp [hp]
  rw [p.disc_of_degree_eq_two hp, (-p).disc_of_degree_eq_two e0]
  simp

-- c.f. discrim_eq_sq_of_quadratic_eq_zero
lemma discrim_eq_sq_of_quadratic_of_isRoot {x : R} (hp : p.degree = 2) (h : IsRoot p x) :
    p.disc = (2 * (p.coeff 2) * x + (p.coeff 1)) ^ 2 := by
  rw [p.disc_of_degree_eq_two hp]
  rw [p.eq_quadratic_of_degree_le_two (le_of_eq hp)] at h
  simp at h
  linear_combination -4 * (p.coeff 2) * h

/-- A quadratic has roots if and only if its discriminant equals some square.
c.f. quadratic_eq_zero_iff_discrim_eq_sq
-/
theorem quadratic_isRoot_iff_discrim_eq_sq [NeZero (2 : R)] [NoZeroDivisors R]
    (hp : p.degree = 2) (x : R) : IsRoot p x ↔ p.disc = (2 * (p.coeff 2) * x + p.coeff 1) ^ 2 := by
  refine ⟨Polynomial.discrim_eq_sq_of_quadratic_of_isRoot hp, fun h ↦ ?_⟩
  rw [p.disc_of_degree_eq_two hp] at h
  have ha : 2 * 2 * (p.coeff 2) ≠ 0 := mul_ne_zero (mul_ne_zero (NeZero.ne _) (NeZero.ne _))
    (coeff_ne_zero_of_eq_degree hp)
  rw [p.eq_quadratic_of_degree_le_two (le_of_eq hp)]
  simp
  apply mul_left_cancel₀ ha --(coeff_ne_zero_of_eq_degree hp)
  linear_combination -h

/-- A quadratic has no root if its discriminant has no square root.
c.f. quadratic_ne_zero_of_discrim_ne_sq
-/
theorem quadratic_not_isRoot_of_discrim_ne_sq (hp : p.degree = 2) (h : ∀ s : R, p.disc ≠ s^2)
    (x : R) : ¬ IsRoot p x :=
  mt (Polynomial.discrim_eq_sq_of_quadratic_of_isRoot hp) (h _)

end Ring

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)] {p : K[X]}

/-- Roots of a quadratic equation.
c.f. quadratic_eq_zero_iff
-/
theorem quadratic_isRoot_iff (hp : p.degree = 2) {s : K} (h : p.disc = s * s) (x : K) :
    IsRoot p x ↔ x = (-(p.coeff 1) + s) / (2 * (p.coeff 2)) ∨
      x = (-(p.coeff 1) - s) / (2 * (p.coeff 2)) := by
  rw [quadratic_isRoot_iff_discrim_eq_sq hp _, h, sq, mul_self_eq_mul_self_iff]
  have ha : (p.coeff 2) ≠ 0 := coeff_ne_zero_of_eq_degree hp
  field_simp
  grind

/-- A quadratic has roots if its discriminant has square roots
c.f. exists_quadratic_eq_zero
-/
theorem exists_quadratic_isRoot (hp : p.degree = 2) (h : ∃ s, p.disc = s * s) :
    ∃ x, IsRoot p x := by
  rcases h with ⟨s, hs⟩
  use (-(p.coeff 1) + s) / (2 * (p.coeff 2))
  rw [quadratic_isRoot_iff hp hs]
  simp

/-- Root of a quadratic when its discriminant equals zero
c.f. quadratic_eq_zero_iff_of_discrim_eq_zero
-/
theorem quadratic_isRoot_iff_of_discrim_eq_zero (hp : p.degree = 2) (h : p.disc = 0) (x : K) :
    IsRoot p x ↔ x = -(p.coeff 1) / (2 * (p.coeff 2)) := by
  have : p.disc = 0 * 0 := by rw [h, mul_zero]
  rw [quadratic_isRoot_iff hp this, add_zero, sub_zero, or_self_iff]

theorem discrim_eq_zero_of_existsUnique (hp : p.degree = 2) (h : ∃! x, IsRoot p x) :
    p.disc = 0 := by
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  simp_rw [quadratic_isRoot_iff_discrim_eq_sq hp] at h
  generalize p.disc = d at h
  obtain ⟨x, rfl, hx⟩ := h
  specialize hx (-(x + b / a))
  have hx' :
      (fun x₁ ↦ (2 * a * x + b) ^ 2 = (2 * a * x₁ + b) ^ 2) (-(x + b / a)) → -(x + b / a) = x := hx
  have ha : a ≠ 0 := coeff_ne_zero_of_eq_degree hp
  suffices (2 * a * x + b) ^ 2 = 0 by exact this
  grind

theorem discrim_eq_zero_iff (hp : p.degree = 2) :
    p.disc  = 0 ↔ (∃! x, IsRoot p x) := by
  refine ⟨fun hd => ?_, discrim_eq_zero_of_existsUnique hp⟩
  simp_rw [quadratic_isRoot_iff_of_discrim_eq_zero hp hd, existsUnique_eq]

end Field

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {p : K[X]}

/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive -/
theorem discrim_le_zero (hp : p.degree = 2) (h : ∀ x : K, 0 ≤ p.eval x) : p.disc ≤ 0 := by
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  rw [p.disc_of_degree_eq_two hp, sq]
  rw [p.eq_quadratic_of_degree_le_two (le_of_eq hp)] at h
  simp at h
  obtain ha | ha : a < 0 ∨ 0 < a := lt_or_gt_of_ne (coeff_ne_zero_of_eq_degree hp)
  -- if a < 0
  · have : Tendsto (fun x => (a * x + b) * x + c) atTop atBot :=
      tendsto_atBot_add_const_right _ c <|
        (tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop₀
          tendsto_id
    rcases (this.eventually (eventually_lt_atBot 0)).exists with ⟨x, hx⟩
    grind
  -- if a > 0
  · have ha' : 0 ≤ 4 * a := mul_nonneg zero_le_four ha.le
    convert neg_nonpos.2 (mul_nonneg ha' (h (-b / (2 * a)))) using 1
    have hz : a ≠ 0 := coeff_ne_zero_of_eq_degree hp
    field_simp
    ring

lemma discrim_le_zero_of_nonpos (hp : p.degree = 2) (h : ∀ x : K, p.eval x ≤ 0) : p.disc ≤ 0 := by
  rw [← discrim_neg hp]
  apply discrim_le_zero
  · simp [hp]
  intro x
  simp only [eval_neg, Left.nonneg_neg_iff]
  exact h x
  --(discrim_neg hp) ▸ discrim_le_zero hp <| by simpa [neg_mul, ← neg_add, neg_nonneg]

/-- If a polynomial of degree 2 is always positive, then its discriminant is negative,
at least when the coefficient of the quadratic term is nonzero.
-/
theorem discrim_lt_zero (hp : p.degree = 2) (h : ∀ x : K, 0 < p.eval x) :
    p.disc < 0 := by
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  have : ∀ x : K, 0 ≤ p.eval x := fun x => le_of_lt (h x)
  refine lt_of_le_of_ne (discrim_le_zero hp this) fun h' ↦ ?_
  have := h (-b / (2 * a))
  have hr : IsRoot p (-b / (2 * a)) := by
    rw [quadratic_isRoot_iff_of_discrim_eq_zero hp h' (-b / (2 * a))]
  rw [IsRoot.def] at hr
  linarith

lemma discrim_lt_zero_of_neg (hp : p.degree = 2) (h : ∀ x : K, p.eval x < 0) :
    p.disc < 0 := by
  rw [← discrim_neg hp]
  apply discrim_lt_zero
  · simp [hp]
  intro x
  simp only [eval_neg]
  exact Left.neg_pos_iff.mpr (h x)
--  discrim_neg p ▸ discrim_lt_zero (neg_ne_zero.2 ha) <| by
--    simpa only [neg_mul, ← neg_add, neg_pos]

end LinearOrderedField

end Polynomial
