/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
import Mathlib.Algebra.Star.Order
import Mathlib.Topology.Instances.NNReal
import Mathlib.Topology.Order.MonotoneContinuity

#align_import data.real.sqrt from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Square root of a real number

In this file we define

* `NNReal.sqrt` to be the square root of a nonnegative real number.
* `Real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `NNReal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `NNReal.sqrt x` exists. As a side
effect, `NNReal.sqrt` is a bundled `OrderIso`, so for `NNReal` numbers we get continuity as well as
theorems like `NNReal.sqrt x ≤ y ↔ x ≤ y * y` for free.

Then we define `Real.sqrt x` to be `NNReal.sqrt (Real.toNNReal x)`.

## Tags

square root
-/

open Set Filter
open scoped Filter NNReal Topology

namespace NNReal

variable {x y : ℝ≥0}

/-- Square root of a nonnegative real number. -/
-- Porting note: was @[pp_nodot]
noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
  OrderIso.symm <| powOrderIso 2 two_ne_zero
#align nnreal.sqrt NNReal.sqrt

@[simp] lemma sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _
#align nnreal.sq_sqrt NNReal.sq_sqrt

@[simp] lemma sqrt_sq (x : ℝ≥0) : sqrt (x ^ 2) = x := sqrt.apply_symm_apply _
#align nnreal.sqrt_sq NNReal.sqrt_sq

@[simp] lemma mul_self_sqrt (x : ℝ≥0) : sqrt x * sqrt x = x := by rw [← sq, sq_sqrt]
#align nnreal.mul_self_sqrt NNReal.mul_self_sqrt

@[simp] lemma sqrt_mul_self (x : ℝ≥0) : sqrt (x * x) = x := by rw [← sq, sqrt_sq]
#align nnreal.sqrt_mul_self NNReal.sqrt_mul_self

lemma sqrt_le_sqrt : sqrt x ≤ sqrt y ↔ x ≤ y := sqrt.le_iff_le
#align nnreal.sqrt_le_sqrt_iff NNReal.sqrt_le_sqrt

lemma sqrt_lt_sqrt : sqrt x < sqrt y ↔ x < y := sqrt.lt_iff_lt
#align nnreal.sqrt_lt_sqrt_iff NNReal.sqrt_lt_sqrt

lemma sqrt_eq_iff_eq_sq : sqrt x = y ↔ x = y ^ 2 := sqrt.toEquiv.apply_eq_iff_eq_symm_apply
#align nnreal.sqrt_eq_iff_sq_eq NNReal.sqrt_eq_iff_eq_sq

lemma sqrt_le_iff_le_sq : sqrt x ≤ y ↔ x ≤ y ^ 2 := sqrt.to_galoisConnection _ _
#align nnreal.sqrt_le_iff NNReal.sqrt_le_iff_le_sq

lemma le_sqrt_iff_sq_le : x ≤ sqrt y ↔ x ^ 2 ≤ y := (sqrt.symm.to_galoisConnection _ _).symm
#align nnreal.le_sqrt_iff NNReal.le_sqrt_iff_sq_le

-- 2024-02-14
@[deprecated] alias sqrt_le_sqrt_iff := sqrt_le_sqrt
@[deprecated] alias sqrt_lt_sqrt_iff := sqrt_lt_sqrt
@[deprecated] alias sqrt_le_iff := sqrt_le_iff_le_sq
@[deprecated] alias le_sqrt_iff := le_sqrt_iff_sq_le
@[deprecated] alias sqrt_eq_iff_sq_eq := sqrt_eq_iff_eq_sq

@[simp] lemma sqrt_eq_zero : sqrt x = 0 ↔ x = 0 := by simp [sqrt_eq_iff_eq_sq]
#align nnreal.sqrt_eq_zero NNReal.sqrt_eq_zero

@[simp] lemma sqrt_eq_one : sqrt x = 1 ↔ x = 1 := by simp [sqrt_eq_iff_eq_sq]

@[simp] lemma sqrt_zero : sqrt 0 = 0 := by simp
#align nnreal.sqrt_zero NNReal.sqrt_zero

@[simp] lemma sqrt_one : sqrt 1 = 1 := by simp
#align nnreal.sqrt_one NNReal.sqrt_one

@[simp] lemma sqrt_le_one : sqrt x ≤ 1 ↔ x ≤ 1 := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]
@[simp] lemma one_le_sqrt : 1 ≤ sqrt x ↔ 1 ≤ x := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]

theorem sqrt_mul (x y : ℝ≥0) : sqrt (x * y) = sqrt x * sqrt y := by
  rw [sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt, sq_sqrt]
#align nnreal.sqrt_mul NNReal.sqrt_mul

/-- `NNReal.sqrt` as a `MonoidWithZeroHom`. -/
noncomputable def sqrtHom : ℝ≥0 →*₀ ℝ≥0 :=
  ⟨⟨sqrt, sqrt_zero⟩, sqrt_one, sqrt_mul⟩
#align nnreal.sqrt_hom NNReal.sqrtHom

theorem sqrt_inv (x : ℝ≥0) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
  map_inv₀ sqrtHom x
#align nnreal.sqrt_inv NNReal.sqrt_inv

theorem sqrt_div (x y : ℝ≥0) : sqrt (x / y) = sqrt x / sqrt y :=
  map_div₀ sqrtHom x y
#align nnreal.sqrt_div NNReal.sqrt_div

@[continuity, fun_prop]
theorem continuous_sqrt : Continuous sqrt := sqrt.continuous
#align nnreal.continuous_sqrt NNReal.continuous_sqrt

@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x := by simp [pos_iff_ne_zero]

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

end NNReal

namespace Real

/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
#align real.sqrt Real.sqrt

-- TODO: replace this with a typeclass
@[inherit_doc]
prefix:max "√" => Real.sqrt

/- quotient.lift_on x
  (λ f, mk ⟨sqrt_aux f, (sqrt_aux_converges f).fst⟩)
  (λ f g e, begin
    rcases sqrt_aux_converges f with ⟨hf, x, x0, xf, xs⟩,
    rcases sqrt_aux_converges g with ⟨hg, y, y0, yg, ys⟩,
    refine xs.trans (eq.trans _ ys.symm),
    rw [← @mul_self_inj_of_nonneg ℝ _ x y x0 y0, xf, yg],
    congr' 1, exact quotient.sound e
  end)-/
variable {x y : ℝ}

@[simp, norm_cast]
theorem coe_sqrt {x : ℝ≥0} : (NNReal.sqrt x : ℝ) = √(x : ℝ) := by
  rw [Real.sqrt, Real.toNNReal_coe]
#align real.coe_sqrt Real.coe_sqrt

@[continuity]
theorem continuous_sqrt : Continuous (√· : ℝ → ℝ) :=
  NNReal.continuous_coe.comp <| NNReal.continuous_sqrt.comp continuous_real_toNNReal
#align real.continuous_sqrt Real.continuous_sqrt

theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : sqrt x = 0 := by simp [sqrt, Real.toNNReal_eq_zero.2 h]
#align real.sqrt_eq_zero_of_nonpos Real.sqrt_eq_zero_of_nonpos

theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x :=
  NNReal.coe_nonneg _
#align real.sqrt_nonneg Real.sqrt_nonneg

@[simp]
theorem mul_self_sqrt (h : 0 ≤ x) : √x * √x = x := by
  rw [Real.sqrt, ← NNReal.coe_mul, NNReal.mul_self_sqrt, Real.coe_toNNReal _ h]
#align real.mul_self_sqrt Real.mul_self_sqrt

@[simp]
theorem sqrt_mul_self (h : 0 ≤ x) : √(x * x) = x :=
  (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))
#align real.sqrt_mul_self Real.sqrt_mul_self

theorem sqrt_eq_cases : √x = y ↔ y * y = x ∧ 0 ≤ y ∨ x < 0 ∧ y = 0 := by
  constructor
  · rintro rfl
    rcases le_or_lt 0 x with hle | hlt
    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
    · exact Or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le]
#align real.sqrt_eq_cases Real.sqrt_eq_cases

theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ y * y = x :=
  ⟨fun h => by rw [← h, mul_self_sqrt hx], fun h => by rw [← h, sqrt_mul_self hy]⟩
#align real.sqrt_eq_iff_mul_self_eq Real.sqrt_eq_iff_mul_self_eq

theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) : √x = y ↔ y * y = x := by
  simp [sqrt_eq_cases, h.ne', h.le]
#align real.sqrt_eq_iff_mul_self_eq_of_pos Real.sqrt_eq_iff_mul_self_eq_of_pos

@[simp]
theorem sqrt_eq_one : √x = 1 ↔ x = 1 :=
  calc
    √x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
    _ ↔ x = 1 := by rw [eq_comm, mul_one]
#align real.sqrt_eq_one Real.sqrt_eq_one

@[simp]
theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]
#align real.sq_sqrt Real.sq_sqrt

@[simp]
theorem sqrt_sq (h : 0 ≤ x) : √(x ^ 2) = x := by rw [sq, sqrt_mul_self h]
#align real.sqrt_sq Real.sqrt_sq

theorem sqrt_eq_iff_sq_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ y ^ 2 = x := by
  rw [sq, sqrt_eq_iff_mul_self_eq hx hy]
#align real.sqrt_eq_iff_sq_eq Real.sqrt_eq_iff_sq_eq

theorem sqrt_mul_self_eq_abs (x : ℝ) : √(x * x) = |x| := by
  rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]
#align real.sqrt_mul_self_eq_abs Real.sqrt_mul_self_eq_abs

theorem sqrt_sq_eq_abs (x : ℝ) : √(x ^ 2) = |x| := by rw [sq, sqrt_mul_self_eq_abs]
#align real.sqrt_sq_eq_abs Real.sqrt_sq_eq_abs

@[simp]
theorem sqrt_zero : √0 = 0 := by simp [Real.sqrt]
#align real.sqrt_zero Real.sqrt_zero

@[simp]
theorem sqrt_one : √1 = 1 := by simp [Real.sqrt]
#align real.sqrt_one Real.sqrt_one

@[simp]
theorem sqrt_le_sqrt_iff (hy : 0 ≤ y) : √x ≤ √y ↔ x ≤ y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt, toNNReal_le_toNNReal_iff hy]
#align real.sqrt_le_sqrt_iff Real.sqrt_le_sqrt_iff

@[simp]
theorem sqrt_lt_sqrt_iff (hx : 0 ≤ x) : √x < √y ↔ x < y :=
  lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)
#align real.sqrt_lt_sqrt_iff Real.sqrt_lt_sqrt_iff

theorem sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : √x < √y ↔ x < y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_lt_coe, NNReal.sqrt_lt_sqrt, toNNReal_lt_toNNReal_iff hy]
#align real.sqrt_lt_sqrt_iff_of_pos Real.sqrt_lt_sqrt_iff_of_pos

@[gcongr]
theorem sqrt_le_sqrt (h : x ≤ y) : √x ≤ √y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt]
  exact toNNReal_le_toNNReal h
#align real.sqrt_le_sqrt Real.sqrt_le_sqrt

@[gcongr]
theorem sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y) : √x < √y :=
  (sqrt_lt_sqrt_iff hx).2 h
#align real.sqrt_lt_sqrt Real.sqrt_lt_sqrt

theorem sqrt_le_left (hy : 0 ≤ y) : √x ≤ y ↔ x ≤ y ^ 2 := by
  rw [sqrt, ← Real.le_toNNReal_iff_coe_le hy, NNReal.sqrt_le_iff_le_sq, sq, ← Real.toNNReal_mul hy,
    Real.toNNReal_le_toNNReal_iff (mul_self_nonneg y), sq]
#align real.sqrt_le_left Real.sqrt_le_left

theorem sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2 := by
  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h, and_congr_right_iff]
  exact sqrt_le_left
#align real.sqrt_le_iff Real.sqrt_le_iff

theorem sqrt_lt (hx : 0 ≤ x) (hy : 0 ≤ y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff hx, sqrt_sq hy]
#align real.sqrt_lt Real.sqrt_lt

theorem sqrt_lt' (hy : 0 < y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff_of_pos (pow_pos hy _), sqrt_sq hy.le]
#align real.sqrt_lt' Real.sqrt_lt'

/-- Note: if you want to conclude `x ≤ √y`, then use `Real.le_sqrt_of_sq_le`.
If you have `x > 0`, consider using `Real.le_sqrt'` -/
theorem le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ √y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt hy hx
#align real.le_sqrt Real.le_sqrt

theorem le_sqrt' (hx : 0 < x) : x ≤ √y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt' hx
#align real.le_sqrt' Real.le_sqrt'

theorem abs_le_sqrt (h : x ^ 2 ≤ y) : |x| ≤ √y := by
  rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h
#align real.abs_le_sqrt Real.abs_le_sqrt

theorem sq_le (h : 0 ≤ y) : x ^ 2 ≤ y ↔ -√y ≤ x ∧ x ≤ √y := by
  constructor
  · simpa only [abs_le] using abs_le_sqrt
  · rw [← abs_le, ← sq_abs]
    exact (le_sqrt (abs_nonneg x) h).mp
#align real.sq_le Real.sq_le

theorem neg_sqrt_le_of_sq_le (h : x ^ 2 ≤ y) : -√y ≤ x :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).1
#align real.neg_sqrt_le_of_sq_le Real.neg_sqrt_le_of_sq_le

theorem le_sqrt_of_sq_le (h : x ^ 2 ≤ y) : x ≤ √y :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).2
#align real.le_sqrt_of_sq_le Real.le_sqrt_of_sq_le

@[simp]
theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = √y ↔ x = y := by
  simp [le_antisymm_iff, hx, hy]
#align real.sqrt_inj Real.sqrt_inj

@[simp]
theorem sqrt_eq_zero (h : 0 ≤ x) : √x = 0 ↔ x = 0 := by simpa using sqrt_inj h le_rfl
#align real.sqrt_eq_zero Real.sqrt_eq_zero

theorem sqrt_eq_zero' : √x = 0 ↔ x ≤ 0 := by
  rw [sqrt, NNReal.coe_eq_zero, NNReal.sqrt_eq_zero, Real.toNNReal_eq_zero]
#align real.sqrt_eq_zero' Real.sqrt_eq_zero'

theorem sqrt_ne_zero (h : 0 ≤ x) : √x ≠ 0 ↔ x ≠ 0 := by rw [not_iff_not, sqrt_eq_zero h]
#align real.sqrt_ne_zero Real.sqrt_ne_zero

theorem sqrt_ne_zero' : √x ≠ 0 ↔ 0 < x := by rw [← not_le, not_iff_not, sqrt_eq_zero']
#align real.sqrt_ne_zero' Real.sqrt_ne_zero'

@[simp]
theorem sqrt_pos : 0 < √x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le (Iff.trans (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')
#align real.sqrt_pos Real.sqrt_pos

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos
#align real.sqrt_pos_of_pos Real.sqrt_pos_of_pos

lemma sqrt_le_sqrt_iff' (hx : 0 < x) : √x ≤ √y ↔ x ≤ y := by
  obtain hy | hy := le_total y 0
  · exact iff_of_false ((sqrt_eq_zero_of_nonpos hy).trans_lt $ sqrt_pos.2 hx).not_le
      (hy.trans_lt hx).not_le
  · exact sqrt_le_sqrt_iff hy

@[simp] lemma one_le_sqrt : 1 ≤ √x ↔ 1 ≤ x := by
  rw [← sqrt_one, sqrt_le_sqrt_iff' zero_lt_one, sqrt_one]

@[simp] lemma sqrt_le_one : √x ≤ 1 ↔ x ≤ 1 := by
  rw [← sqrt_one, sqrt_le_sqrt_iff zero_le_one, sqrt_one]

end Real

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: a square root of a strictly positive nonnegative real is
positive. -/
@[positivity NNReal.sqrt _]
def evalNNRealSqrt : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $a) =>
    let ra ← core  q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(NNReal.sqrt_pos_of_pos $pa))
    | _ => failure -- this case is dealt with by generic nonnegativity of nnreals
  | _, _, _ => throwError "not NNReal.sqrt"

/-- Extension for the `positivity` tactic: a square root is nonnegative, and is strictly positive if
its input is. -/
@[positivity √ _]
def evalSqrt : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(√$a) =>
    let ra ← catchNone <| core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(Real.sqrt_pos_of_pos $pa))
    | _ => pure (.nonnegative q(Real.sqrt_nonneg $a))
  | _, _, _ => throwError "not Real.sqrt"

end Mathlib.Meta.Positivity

namespace Real

variable {x y : ℝ}

@[simp]
theorem sqrt_mul {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : √(x * y) = √x * √y := by
  simp_rw [Real.sqrt, ← NNReal.coe_mul, NNReal.coe_inj, Real.toNNReal_mul hx, NNReal.sqrt_mul]
#align real.sqrt_mul Real.sqrt_mul

@[simp]
theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : √(x * y) = √x * √y := by
  rw [mul_comm, sqrt_mul hy, mul_comm]
#align real.sqrt_mul' Real.sqrt_mul'

@[simp]
theorem sqrt_inv (x : ℝ) : √x⁻¹ = (√x)⁻¹ := by
  rw [Real.sqrt, Real.toNNReal_inv, NNReal.sqrt_inv, NNReal.coe_inv, Real.sqrt]
#align real.sqrt_inv Real.sqrt_inv

@[simp]
theorem sqrt_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : √(x / y) = √x / √y := by
  rw [division_def, sqrt_mul hx, sqrt_inv, division_def]
#align real.sqrt_div Real.sqrt_div

@[simp]
theorem sqrt_div' (x) {y : ℝ} (hy : 0 ≤ y) : √(x / y) = √x / √y := by
  rw [division_def, sqrt_mul' x (inv_nonneg.2 hy), sqrt_inv, division_def]
#align real.sqrt_div' Real.sqrt_div'

variable {x y : ℝ}

@[simp]
theorem div_sqrt : x / √x = √x := by
  rcases le_or_lt x 0 with h | h
  · rw [sqrt_eq_zero'.mpr h, div_zero]
  · rw [div_eq_iff (sqrt_ne_zero'.mpr h), mul_self_sqrt h.le]
#align real.div_sqrt Real.div_sqrt

theorem sqrt_div_self' : √x / x = 1 / √x := by rw [← div_sqrt, one_div_div, div_sqrt]
#align real.sqrt_div_self' Real.sqrt_div_self'

theorem sqrt_div_self : √x / x = (√x)⁻¹ := by rw [sqrt_div_self', one_div]
#align real.sqrt_div_self Real.sqrt_div_self

theorem lt_sqrt (hx : 0 ≤ x) : x < √y ↔ x ^ 2 < y := by
  rw [← sqrt_lt_sqrt_iff (sq_nonneg _), sqrt_sq hx]
#align real.lt_sqrt Real.lt_sqrt

theorem sq_lt : x ^ 2 < y ↔ -√y < x ∧ x < √y := by
  rw [← abs_lt, ← sq_abs, lt_sqrt (abs_nonneg _)]
#align real.sq_lt Real.sq_lt

theorem neg_sqrt_lt_of_sq_lt (h : x ^ 2 < y) : -√y < x :=
  (sq_lt.mp h).1
#align real.neg_sqrt_lt_of_sq_lt Real.neg_sqrt_lt_of_sq_lt

theorem lt_sqrt_of_sq_lt (h : x ^ 2 < y) : x < √y :=
  (sq_lt.mp h).2
#align real.lt_sqrt_of_sq_lt Real.lt_sqrt_of_sq_lt

theorem lt_sq_of_sqrt_lt (h : √x < y) : x < y ^ 2 := by
  have hy := x.sqrt_nonneg.trans_lt h
  rwa [← sqrt_lt_sqrt_iff_of_pos (sq_pos_of_pos hy), sqrt_sq hy.le]
#align real.lt_sq_of_sqrt_lt Real.lt_sq_of_sqrt_lt

/-- The natural square root is at most the real square root -/
theorem nat_sqrt_le_real_sqrt {a : ℕ} : ↑(Nat.sqrt a) ≤ √(a : ℝ) := by
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  norm_cast
  exact Nat.sqrt_le' a
#align real.nat_sqrt_le_real_sqrt Real.nat_sqrt_le_real_sqrt

/-- The real square root is less than the natural square root plus one -/
theorem real_sqrt_lt_nat_sqrt_succ {a : ℕ} : √(a : ℝ) < Nat.sqrt a + 1 := by
  rw [sqrt_lt (by simp)] <;> norm_cast
  · exact Nat.lt_succ_sqrt' a
  · exact Nat.le_add_left 0 (Nat.sqrt a + 1)

/-- The real square root is at most the natural square root plus one -/
theorem real_sqrt_le_nat_sqrt_succ {a : ℕ} : √(a : ℝ) ≤ Nat.sqrt a + 1 :=
  real_sqrt_lt_nat_sqrt_succ.le
#align real.real_sqrt_le_nat_sqrt_succ Real.real_sqrt_le_nat_sqrt_succ

/-- The floor of the real square root is the same as the natural square root. -/
@[simp]
theorem floor_real_sqrt_eq_nat_sqrt {a : ℕ} : ⌊√(a : ℝ)⌋ = Nat.sqrt a := by
  rw [Int.floor_eq_iff]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

/-- The natural floor of the real square root is the same as the natural square root. -/
@[simp]
theorem nat_floor_real_sqrt_eq_nat_sqrt {a : ℕ} : ⌊√(a : ℝ)⌋₊ = Nat.sqrt a := by
  rw [Nat.floor_eq_iff (sqrt_nonneg a)]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

/-- Bernoulli's inequality for exponent `1 / 2`, stated using `sqrt`. -/
theorem sqrt_one_add_le (h : -1 ≤ x) : √(1 + x) ≤ 1 + x / 2 := by
  refine sqrt_le_iff.mpr ⟨by linarith, ?_⟩
  calc 1 + x
    _ ≤ 1 + x + (x / 2) ^ 2 := le_add_of_nonneg_right <| sq_nonneg _
    _ = _ := by ring

/-- Although the instance `RCLike.toStarOrderedRing` exists, it is locked behind the
`ComplexOrder` scope because currently the order on `ℂ` is not enabled globally. But we
want `StarOrderedRing ℝ` to be available globally, so we include this instance separately.
In addition, providing this instance here makes it available earlier in the import
hierarchy; otherwise in order to access it we would need to import `Mathlib.Analysis.RCLike.Basic`.
-/
instance : StarOrderedRing ℝ :=
  StarOrderedRing.of_nonneg_iff' add_le_add_left fun r => by
    refine ⟨fun hr => ⟨√r, (mul_self_sqrt hr).symm⟩, ?_⟩
    rintro ⟨s, rfl⟩
    exact mul_self_nonneg s

end Real

instance NNReal.instStarOrderedRing : StarOrderedRing ℝ≥0 := by
  refine .of_le_iff fun x y ↦ ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h
    refine ⟨sqrt d, ?_⟩
    simp only [star_trivial, mul_self_sqrt]
  · rintro ⟨p, -, rfl⟩
    exact le_self_add

open Real

variable {α : Type*}

theorem Filter.Tendsto.sqrt {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) :
    Tendsto (fun x => √(f x)) l (𝓝 (√x)) :=
  (continuous_sqrt.tendsto _).comp h
#align filter.tendsto.sqrt Filter.Tendsto.sqrt

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

nonrec theorem ContinuousWithinAt.sqrt (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => √(f x)) s x :=
  h.sqrt
#align continuous_within_at.sqrt ContinuousWithinAt.sqrt

@[fun_prop]
nonrec theorem ContinuousAt.sqrt (h : ContinuousAt f x) : ContinuousAt (fun x => √(f x)) x :=
  h.sqrt
#align continuous_at.sqrt ContinuousAt.sqrt

@[fun_prop]
theorem ContinuousOn.sqrt (h : ContinuousOn f s) : ContinuousOn (fun x => √(f x)) s :=
  fun x hx => (h x hx).sqrt
#align continuous_on.sqrt ContinuousOn.sqrt

@[continuity, fun_prop]
theorem Continuous.sqrt (h : Continuous f) : Continuous fun x => √(f x) :=
  continuous_sqrt.comp h
#align continuous.sqrt Continuous.sqrt

namespace NNReal
variable {ι : Type*}
open Finset

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ≥0`. -/
lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι → ℝ≥0) :
    ∑ i ∈ s, f i * g i ≤ sqrt (∑ i ∈ s, f i ^ 2) * sqrt (∑ i ∈ s, g i ^ 2) :=
  (le_sqrt_iff_sq_le.2 $ sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq <| sqrt_mul _ _

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ≥0`. -/
lemma sum_sqrt_mul_sqrt_le (s : Finset ι) (f g : ι → ℝ≥0) :
    ∑ i ∈ s, sqrt (f i) * sqrt (g i) ≤ sqrt (∑ i ∈ s, f i) * sqrt (∑ i ∈ s, g i) := by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x ↦ sqrt (f x)) (fun x ↦ sqrt (g x))

end NNReal

namespace Real
variable {ι : Type*} {f g : ι → ℝ}
open Finset

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ`. -/
lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, f i * g i ≤ √(∑ i ∈ s, f i ^ 2) * √(∑ i ∈ s, g i ^ 2) :=
  (le_sqrt_of_sq_le <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq <| sqrt_mul
    (sum_nonneg fun _ _ ↦ by positivity) _

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ`. -/
lemma sum_sqrt_mul_sqrt_le (s : Finset ι) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, √(f i) * √(g i) ≤ √(∑ i ∈ s, f i) * √(∑ i ∈ s, g i) := by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x ↦ √(f x)) (fun x ↦ √(g x))

end Real
