/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Complex.Abs

/-!
# The partial order on the complex numbers

This order is defined by `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`.

This is a natural order on `ℂ` because, as is well-known, there does not exist an order on `ℂ`
making it into a `LinearOrderedField`. However, the order described above is the canonical order
stemming from the structure of `ℂ` as a ⋆-ring (i.e., it becomes a `StarOrderedRing`). Moreover,
with this order `ℂ` is a `StrictOrderedCommRing` and the coercion `(↑) : ℝ → ℂ` is an order
embedding.

This file only provides `Complex.partialOrder` and lemmas about it. Further structural classes are
provided by `Mathlib/Data/RCLike/Basic.lean` as

* `RCLike.toStrictOrderedCommRing`
* `RCLike.toStarOrderedRing`
* `RCLike.toOrderedSMul`

These are all only available with `open scoped ComplexOrder`.
-/

namespace Complex

/-- We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
protected def partialOrder : PartialOrder ℂ where
  le z w := z.re ≤ w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_le z w := by
    dsimp
    rw [lt_iff_le_not_le]
    tauto
  le_refl x := ⟨le_rfl, rfl⟩
  le_trans x y z h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm z w h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2
#align complex.partial_order Complex.partialOrder

namespace _root_.ComplexOrder

-- Porting note: made section into namespace to allow scoping
scoped[ComplexOrder] attribute [instance] Complex.partialOrder

end _root_.ComplexOrder

open ComplexOrder

theorem le_def {z w : ℂ} : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im :=
  Iff.rfl
#align complex.le_def Complex.le_def

theorem lt_def {z w : ℂ} : z < w ↔ z.re < w.re ∧ z.im = w.im :=
  Iff.rfl
#align complex.lt_def Complex.lt_def

theorem nonneg_iff {z : ℂ} : 0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im :=
  le_def

theorem pos_iff {z : ℂ} : 0 < z ↔ 0 < z.re ∧ 0 = z.im :=
  lt_def

@[simp, norm_cast]
theorem real_le_real {x y : ℝ} : (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y := by simp [le_def, ofReal']
#align complex.real_le_real Complex.real_le_real

@[simp, norm_cast]
theorem real_lt_real {x y : ℝ} : (x : ℂ) < (y : ℂ) ↔ x < y := by simp [lt_def, ofReal']
#align complex.real_lt_real Complex.real_lt_real

@[simp, norm_cast]
theorem zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x :=
  real_le_real
#align complex.zero_le_real Complex.zero_le_real

@[simp, norm_cast]
theorem zero_lt_real {x : ℝ} : (0 : ℂ) < (x : ℂ) ↔ 0 < x :=
  real_lt_real
#align complex.zero_lt_real Complex.zero_lt_real

theorem not_le_iff {z w : ℂ} : ¬z ≤ w ↔ w.re < z.re ∨ z.im ≠ w.im := by
  rw [le_def, not_and_or, not_le]
#align complex.not_le_iff Complex.not_le_iff

theorem not_lt_iff {z w : ℂ} : ¬z < w ↔ w.re ≤ z.re ∨ z.im ≠ w.im := by
  rw [lt_def, not_and_or, not_lt]
#align complex.not_lt_iff Complex.not_lt_iff

theorem not_le_zero_iff {z : ℂ} : ¬z ≤ 0 ↔ 0 < z.re ∨ z.im ≠ 0 :=
  not_le_iff
#align complex.not_le_zero_iff Complex.not_le_zero_iff

theorem not_lt_zero_iff {z : ℂ} : ¬z < 0 ↔ 0 ≤ z.re ∨ z.im ≠ 0 :=
  not_lt_iff
#align complex.not_lt_zero_iff Complex.not_lt_zero_iff

theorem eq_re_of_ofReal_le {r : ℝ} {z : ℂ} (hz : (r : ℂ) ≤ z) : z = z.re := by
  rw [eq_comm, ← conj_eq_iff_re, conj_eq_iff_im, ← (Complex.le_def.1 hz).2, Complex.ofReal_im]
#align complex.eq_re_of_real_le Complex.eq_re_of_ofReal_le

@[simp]
lemma re_eq_abs {z : ℂ} : z.re = abs z ↔ 0 ≤ z :=
  have : 0 ≤ abs z := apply_nonneg abs z
  ⟨fun h ↦ ⟨h.symm ▸ this, (abs_re_eq_abs.1 <| h.symm ▸ _root_.abs_of_nonneg this).symm⟩,
    fun ⟨h₁, h₂⟩ ↦ by rw [← abs_re_eq_abs.2 h₂.symm, _root_.abs_of_nonneg h₁]⟩

@[simp]
lemma neg_re_eq_abs {z : ℂ} : -z.re = abs z ↔ z ≤ 0 := by
  rw [← neg_re, ← abs.map_neg, re_eq_abs]
  exact neg_nonneg.and <| eq_comm.trans neg_eq_zero

@[simp]
lemma re_eq_neg_abs {z : ℂ} : z.re = -abs z ↔ z ≤ 0 := by rw [← neg_eq_iff_eq_neg, neg_re_eq_abs]

lemma monotone_ofReal : Monotone ofReal' := by
  intro x y hxy
  simp only [ofReal_eq_coe, real_le_real, hxy]

end Complex

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Complex
open scoped ComplexOrder

private alias ⟨_, ofReal_pos⟩ := zero_lt_real
private alias ⟨_, ofReal_nonneg⟩ := zero_le_real
private alias ⟨_, ofReal_ne_zero_of_ne_zero⟩ := ofReal_ne_zero

/-- Extension for the `positivity` tactic: `Complex.ofReal` is positive/nonnegative/nonzero if its
input is. -/
@[positivity Complex.ofReal' _, Complex.ofReal _]
def evalComplexOfReal : PositivityExt where eval {u α} _ _ e := do
  -- TODO: Can we avoid duplicating the code?
  match u, α, e with
  | 0, ~q(ℂ), ~q(Complex.ofReal' $a) =>
    assumeInstancesCommute
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa => return .positive q(ofReal_pos $pa)
    | .nonnegative pa => return .nonnegative q(ofReal_nonneg $pa)
    | .nonzero pa => return .nonzero q(ofReal_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | 0, ~q(ℂ), ~q(Complex.ofReal $a) =>
    assumeInstancesCommute
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa => return .positive q(ofReal_pos $pa)
    | .nonnegative pa => return .nonnegative q(ofReal_nonneg $pa)
    | .nonzero pa => return .nonzero q(ofReal_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _ => throwError "not Complex.ofReal'"

example (x : ℝ) (hx : 0 < x) : 0 < (x : ℂ) := by positivity
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (x : ℂ) := by positivity
example (x : ℝ) (hx : x ≠ 0) : (x : ℂ) ≠ 0 := by positivity

end Mathlib.Meta.Positivity
