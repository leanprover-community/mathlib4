/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Complex.Norm

/-!
# The partial order on the complex numbers

This order is defined by `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`.

This is a natural order on `ℂ` because, as is well-known, there does not exist an order on `ℂ`
making it into a linearly ordered field. However, the order described above is the canonical order
stemming from the structure of `ℂ` as a ⋆-ring (i.e., it becomes a `StarOrderedRing`). Moreover,
with this order `ℂ` satisfies `IsStrictOrderedRing` and the coercion `(↑) : ℝ → ℂ` is an order
embedding.

This file only provides `Complex.partialOrder` and lemmas about it. Further structural classes are
provided in `Mathlib/Analysis/RCLike/Basic.lean` as

* `RCLike.toStrictOrderedCommRing`
* `RCLike.toStarOrderedRing`
* `RCLike.toOrderedSMul`

These are all only available with `open scoped ComplexOrder`.
-/

@[expose] public section

namespace Complex

/-- We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
@[instance_reducible]
protected def partialOrder : PartialOrder ℂ where
  le z w := z.re ≤ w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_ge z w := by
    rw [lt_iff_le_not_ge]
    tauto
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2

namespace _root_.ComplexOrder

scoped[ComplexOrder] attribute [instance] Complex.partialOrder

end _root_.ComplexOrder

open ComplexOrder

theorem le_def {z w : ℂ} : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im :=
  Iff.rfl

theorem lt_def {z w : ℂ} : z < w ↔ z.re < w.re ∧ z.im = w.im :=
  Iff.rfl

theorem nonneg_iff {z : ℂ} : 0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im :=
  le_def

theorem pos_iff {z : ℂ} : 0 < z ↔ 0 < z.re ∧ 0 = z.im :=
  lt_def

theorem nonpos_iff {z : ℂ} : z ≤ 0 ↔ z.re ≤ 0 ∧ z.im = 0 :=
  le_def

theorem neg_iff {z : ℂ} : z < 0 ↔ z.re < 0 ∧ z.im = 0 :=
  lt_def

theorem sq_nonneg_iff {z : ℂ} : 0 ≤ z ^ 2 ↔ z.im = 0 := by
  rw [nonneg_iff, pow_two, mul_re, mul_im, mul_comm z.im z.re, ← mul_two, eq_comm,
    mul_eq_zero_iff_right two_ne_zero, ← pow_two, ← pow_two, mul_eq_zero]
  exact ⟨by aesop, fun h ↦ by simpa [h] using sq_nonneg z.re⟩

theorem sq_nonpos_iff {z : ℂ} : z ^ 2 ≤ 0 ↔ z.re = 0 := by
  rw [nonpos_iff, pow_two, mul_re, mul_im, mul_comm z.im z.re, ← mul_two, mul_eq_zero_iff_right
    two_ne_zero, ← pow_two, ← pow_two, mul_eq_zero]
  exact ⟨by aesop, fun h ↦ by simpa [h] using sq_nonneg z.im⟩

@[simp, norm_cast]
theorem real_le_real {x y : ℝ} : (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y := by simp [le_def, ofReal]

@[simp, norm_cast]
theorem real_lt_real {x y : ℝ} : (x : ℂ) < (y : ℂ) ↔ x < y := by simp [lt_def, ofReal]

@[simp, norm_cast]
theorem zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x :=
  real_le_real

@[simp, norm_cast]
theorem zero_lt_real {x : ℝ} : (0 : ℂ) < (x : ℂ) ↔ 0 < x :=
  real_lt_real

theorem not_le_iff {z w : ℂ} : ¬z ≤ w ↔ w.re < z.re ∨ z.im ≠ w.im := by
  rw [le_def, not_and_or, not_le]

theorem not_lt_iff {z w : ℂ} : ¬z < w ↔ w.re ≤ z.re ∨ z.im ≠ w.im := by
  rw [lt_def, not_and_or, not_lt]

theorem not_le_zero_iff {z : ℂ} : ¬z ≤ 0 ↔ 0 < z.re ∨ z.im ≠ 0 :=
  not_le_iff

theorem not_lt_zero_iff {z : ℂ} : ¬z < 0 ↔ 0 ≤ z.re ∨ z.im ≠ 0 :=
  not_lt_iff

theorem eq_re_of_ofReal_le {r : ℝ} {z : ℂ} (hz : (r : ℂ) ≤ z) : z = z.re := by
  rw [eq_comm, ← conj_eq_iff_re, conj_eq_iff_im, ← (Complex.le_def.1 hz).2, Complex.ofReal_im]

@[simp]
lemma re_eq_norm {z : ℂ} : z.re = ‖z‖ ↔ 0 ≤ z :=
  have : 0 ≤ ‖z‖ := norm_nonneg z
  ⟨fun h ↦ ⟨h.symm ▸ this, (abs_re_eq_norm.1 <| h.symm ▸ abs_of_nonneg this).symm⟩,
    fun ⟨h₁, h₂⟩ ↦ by rw [← abs_re_eq_norm.2 h₂.symm, abs_of_nonneg h₁]⟩

@[simp]
lemma neg_re_eq_norm {z : ℂ} : -z.re = ‖z‖ ↔ z ≤ 0 := by
  rw [← neg_re, ← norm_neg z, re_eq_norm]
  exact neg_nonneg.and <| eq_comm.trans neg_eq_zero

@[simp]
lemma re_eq_neg_norm {z : ℂ} : z.re = -‖z‖ ↔ z ≤ 0 := by rw [← neg_eq_iff_eq_neg, neg_re_eq_norm]

lemma monotone_ofReal : Monotone ofReal := by
  intro x y hxy
  simp only [real_le_real, hxy]

end Complex

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Complex
open scoped ComplexOrder

alias ⟨_, ofReal_pos⟩ := zero_lt_real
alias ⟨_, ofReal_nonneg⟩ := zero_le_real
alias ⟨_, ofReal_ne_zero_of_ne_zero⟩ := ofReal_ne_zero

/-- Extension for the `positivity` tactic: `Complex.ofReal` is positive/nonnegative/nonzero if its
input is. -/
@[positivity Complex.ofReal _, Complex.ofReal _]
meta def evalComplexOfReal : PositivityExt where eval {u α} _ pα? e := do
  match u, α, e with
  | 0, ~q(ℂ), ~q(Complex.ofReal $a) =>
    let some _ := pα? | pure .none
    assumeInstancesCommute
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa => return .positive q(ofReal_pos $pa)
    | .nonnegative pa => return .nonnegative q(ofReal_nonneg $pa)
    | .nonzero pa => return .nonzero q(ofReal_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _ => throwError "not Complex.ofReal"

example (x : ℝ) (hx : 0 < x) : 0 < (x : ℂ) := by positivity
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (x : ℂ) := by positivity
example (x : ℝ) (hx : x ≠ 0) : (x : ℂ) ≠ 0 := by positivity

end Mathlib.Meta.Positivity
