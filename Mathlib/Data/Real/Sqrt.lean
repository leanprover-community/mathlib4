/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Map
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Attribute
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Continuous
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.MonotoneContinuity

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

@[expose] public section

open Set Filter
open scoped Filter NNReal Topology

namespace NNReal

variable {x y : ℝ≥0}

/-- Square root of a nonnegative real number. -/
@[pp_nodot]
noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
  OrderIso.symm <| powOrderIso 2 two_ne_zero

@[simp] lemma sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _

@[simp] lemma sqrt_sq (x : ℝ≥0) : sqrt (x ^ 2) = x := sqrt.apply_symm_apply _

@[simp] lemma mul_self_sqrt (x : ℝ≥0) : sqrt x * sqrt x = x := by rw [← sq, sq_sqrt]

@[simp] lemma sqrt_mul_self (x : ℝ≥0) : sqrt (x * x) = x := by rw [← sq, sqrt_sq]

lemma sqrt_le_sqrt : sqrt x ≤ sqrt y ↔ x ≤ y := sqrt.le_iff_le

lemma sqrt_lt_sqrt : sqrt x < sqrt y ↔ x < y := sqrt.lt_iff_lt

lemma sqrt_eq_iff_eq_sq : sqrt x = y ↔ x = y ^ 2 := sqrt.toEquiv.apply_eq_iff_eq_symm_apply

lemma sqrt_le_iff_le_sq : sqrt x ≤ y ↔ x ≤ y ^ 2 := sqrt.to_galoisConnection _ _

lemma le_sqrt_iff_sq_le : x ≤ sqrt y ↔ x ^ 2 ≤ y := (sqrt.symm.to_galoisConnection _ _).symm

@[simp] lemma sqrt_eq_zero : sqrt x = 0 ↔ x = 0 := by simp [sqrt_eq_iff_eq_sq]

@[simp] lemma sqrt_eq_one : sqrt x = 1 ↔ x = 1 := by simp [sqrt_eq_iff_eq_sq]

@[simp] lemma sqrt_zero : sqrt 0 = 0 := by simp

@[simp] lemma sqrt_one : sqrt 1 = 1 := by simp

@[simp] lemma sqrt_le_one : sqrt x ≤ 1 ↔ x ≤ 1 := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]
@[simp] lemma one_le_sqrt : 1 ≤ sqrt x ↔ 1 ≤ x := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]

lemma sqrt_mul_le_max : sqrt (x * y) ≤ max x y := by
  rw [sqrt_le_iff_le_sq, sq]; gcongr <;> simp

theorem sqrt_mul (x y : ℝ≥0) : sqrt (x * y) = sqrt x * sqrt y := by
  rw [sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt, sq_sqrt]

/-- `NNReal.sqrt` as a `MonoidWithZeroHom`. -/
noncomputable def sqrtHom : ℝ≥0 →*₀ ℝ≥0 :=
  ⟨⟨sqrt, sqrt_zero⟩, sqrt_one, sqrt_mul⟩

theorem sqrt_inv (x : ℝ≥0) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
  map_inv₀ sqrtHom x

theorem sqrt_div (x y : ℝ≥0) : sqrt (x / y) = sqrt x / sqrt y :=
  map_div₀ sqrtHom x y

@[continuity, fun_prop]
theorem continuous_sqrt : Continuous sqrt := sqrt.continuous

@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x := by simp [pos_iff_ne_zero]

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

attribute [bound] sqrt_pos_of_pos

@[simp] theorem isSquare (x : ℝ≥0) : IsSquare x := ⟨_, mul_self_sqrt _ |>.symm⟩

end NNReal

namespace Real

/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)

-- TODO: replace this with a typeclass
@[inherit_doc]
prefix:max "√" => Real.sqrt

variable {x y : ℝ}

@[simp, norm_cast]
theorem coe_sqrt {x : ℝ≥0} : (NNReal.sqrt x : ℝ) = √(x : ℝ) := by
  rw [Real.sqrt, Real.toNNReal_coe]

@[continuity, fun_prop]
theorem continuous_sqrt : Continuous (√· : ℝ → ℝ) := by unfold sqrt; fun_prop

@[simp]
lemma map_sqrt_atTop : map (√·) atTop = atTop := by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← map_map]

@[simp]
lemma comap_sqrt_atTop : comap (√·) atTop = atTop := by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← comap_comap]

lemma tendsto_sqrt_atTop : Tendsto (√·) atTop atTop := map_sqrt_atTop.le

theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : √x = 0 := by simp [sqrt, Real.toNNReal_eq_zero.2 h]

@[simp] theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x := by
  unfold sqrt
  exact NNReal.coe_nonneg _

@[simp]
theorem mul_self_sqrt (h : 0 ≤ x) : √x * √x = x := by
  rw [Real.sqrt, ← NNReal.coe_mul, NNReal.mul_self_sqrt, Real.coe_toNNReal _ h]

@[simp]
theorem sqrt_mul_self (h : 0 ≤ x) : √(x * x) = x :=
  (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

theorem sqrt_eq_cases : √x = y ↔ y * y = x ∧ 0 ≤ y ∨ x < 0 ∧ y = 0 := by
  constructor
  · rintro rfl
    rcases le_or_gt 0 x with hle | hlt
    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
    · exact Or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le]

theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y * y :=
  ⟨fun h => by rw [← h, mul_self_sqrt hx], fun h => by rw [h, sqrt_mul_self hy]⟩

theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) : √x = y ↔ y * y = x := by
  simp [sqrt_eq_cases, h.ne', h.le]

@[simp]
theorem sqrt_eq_one : √x = 1 ↔ x = 1 :=
  calc
    √x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
    _ ↔ x = 1 := by rw [eq_comm, mul_one]

@[simp]
theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]

@[simp]
theorem sqrt_sq (h : 0 ≤ x) : √(x ^ 2) = x := by rw [sq, sqrt_mul_self h]

theorem sqrt_eq_iff_eq_sq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y ^ 2 := by
  rw [sq, sqrt_eq_iff_mul_self_eq hx hy]

theorem sqrt_mul_self_eq_abs (x : ℝ) : √(x * x) = |x| := by
  rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]

theorem sqrt_sq_eq_abs (x : ℝ) : √(x ^ 2) = |x| := by rw [sq, sqrt_mul_self_eq_abs]

@[simp, grind =]
theorem sqrt_zero : √0 = 0 := by simp [Real.sqrt]

@[simp, grind =]
theorem sqrt_one : √1 = 1 := by simp [Real.sqrt]

@[simp]
theorem sqrt_le_sqrt_iff (hy : 0 ≤ y) : √x ≤ √y ↔ x ≤ y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt, toNNReal_le_toNNReal_iff hy]

@[simp]
theorem sqrt_lt_sqrt_iff (hx : 0 ≤ x) : √x < √y ↔ x < y :=
  lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)

theorem sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : √x < √y ↔ x < y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_lt_coe, NNReal.sqrt_lt_sqrt, toNNReal_lt_toNNReal_iff hy]

@[bound]
theorem sqrt_le_sqrt (h : x ≤ y) : √x ≤ √y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt]
  exact toNNReal_le_toNNReal h

@[gcongr]
theorem sqrt_monotone : Monotone Real.sqrt :=
  fun _ _ ↦ sqrt_le_sqrt

theorem strictMonoOn_sqrt : StrictMonoOn sqrt (Ici 0) :=
  fun _ ha _ _ h => (sqrt_lt_sqrt_iff ha).mpr h

@[gcongr, bound]
theorem sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y) : √x < √y :=
  (sqrt_lt_sqrt_iff hx).2 h

theorem sqrt_le_left (hy : 0 ≤ y) : √x ≤ y ↔ x ≤ y ^ 2 := by
  rw [sqrt, ← Real.le_toNNReal_iff_coe_le hy, NNReal.sqrt_le_iff_le_sq, sq, ← Real.toNNReal_mul hy,
    Real.toNNReal_le_toNNReal_iff (mul_self_nonneg y), sq]

theorem sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2 := by
  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h, and_congr_right_iff]
  exact sqrt_le_left

theorem sqrt_lt (hx : 0 ≤ x) (hy : 0 ≤ y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff hx, sqrt_sq hy]

theorem sqrt_lt' (hy : 0 < y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff_of_pos (pow_pos hy _), sqrt_sq hy.le]

/-- Note: if you want to conclude `x ≤ √y`, then use `Real.le_sqrt_of_sq_le`.
If you have `x > 0`, consider using `Real.le_sqrt'` -/
theorem le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ √y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt hy hx

theorem le_sqrt' (hx : 0 < x) : x ≤ √y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt' hx

theorem abs_le_sqrt (h : x ^ 2 ≤ y) : |x| ≤ √y := by
  rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h

theorem sq_le (h : 0 ≤ y) : x ^ 2 ≤ y ↔ -√y ≤ x ∧ x ≤ √y := by
  constructor
  · simpa only [abs_le] using abs_le_sqrt
  · rw [← abs_le, ← sq_abs]
    exact (le_sqrt (abs_nonneg x) h).mp

theorem neg_sqrt_le_of_sq_le (h : x ^ 2 ≤ y) : -√y ≤ x :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).1

theorem le_sqrt_of_sq_le (h : x ^ 2 ≤ y) : x ≤ √y :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).2

@[simp]
theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = √y ↔ x = y := by
  simp [le_antisymm_iff, hx, hy]

@[simp]
theorem sqrt_eq_zero (h : 0 ≤ x) : √x = 0 ↔ x = 0 := by simpa using sqrt_inj h le_rfl

theorem sqrt_eq_zero' : √x = 0 ↔ x ≤ 0 := by
  rw [sqrt, NNReal.coe_eq_zero, NNReal.sqrt_eq_zero, Real.toNNReal_eq_zero]

theorem sqrt_ne_zero (h : 0 ≤ x) : √x ≠ 0 ↔ x ≠ 0 := by rw [not_iff_not, sqrt_eq_zero h]

theorem sqrt_ne_zero' : √x ≠ 0 ↔ 0 < x := by rw [← not_le, not_iff_not, sqrt_eq_zero']

/-- Variant of `sq_sqrt` without a non-negativity assumption on `x`. -/
theorem sq_sqrt' : √x ^ 2 = max x 0 := by
  rcases lt_trichotomy x 0 with _ | _ | _ <;> grind [sqrt_eq_zero', sq_sqrt]

-- Add the rule for `√x ^ 2` to the grind whiteboard whenever we see a real square root.
grind_pattern sq_sqrt' => √x

-- Check that `grind` can discharge non-zero goals for square roots of positive numerals.
example : √7 ≠ 0 := by grind

@[simp]
theorem sqrt_pos : 0 < √x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le (Iff.trans (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

lemma sqrt_le_sqrt_iff' (hx : 0 < x) : √x ≤ √y ↔ x ≤ y := by
  obtain hy | hy := le_total y 0
  · exact iff_of_false ((sqrt_eq_zero_of_nonpos hy).trans_lt <| sqrt_pos.2 hx).not_ge
      (hy.trans_lt hx).not_ge
  · exact sqrt_le_sqrt_iff hy

@[simp] lemma one_le_sqrt : 1 ≤ √x ↔ 1 ≤ x := by
  rw [← sqrt_one, sqrt_le_sqrt_iff' zero_lt_one, sqrt_one]

@[simp] lemma sqrt_le_one : √x ≤ 1 ↔ x ≤ 1 := by
  rw [← sqrt_one, sqrt_le_sqrt_iff zero_le_one, sqrt_one]

@[simp] lemma isSquare_iff : IsSquare x ↔ 0 ≤ x :=
  ⟨(·.nonneg), (⟨√x, mul_self_sqrt · |>.symm⟩)⟩

end Real

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: a square root of a strictly positive nonnegative real is
positive. -/
@[positivity NNReal.sqrt _]
meta def evalNNRealSqrt : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(NNReal.sqrt_pos_of_pos $pa))
    | _ => failure -- this case is dealt with by generic nonnegativity of nnreals
  | _, _, _ => throwError "not NNReal.sqrt"

/-- Extension for the `positivity` tactic: a square root is nonnegative, and is strictly positive if
its input is. -/
@[positivity √_]
meta def evalSqrt : PositivityExt where eval {u α} _zα _pα e := do
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

lemma one_lt_sqrt_two : 1 < √2 := by rw [← Real.sqrt_one]; gcongr; simp

lemma sqrt_two_lt_three_halves : √2 < 3 / 2 := by
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  grind

lemma inv_sqrt_two_sub_one : (√2 - 1)⁻¹ = √2 + 1 := by
  grind

@[simp]
theorem sqrt_mul {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : √(x * y) = √x * √y := by
  simp_rw [Real.sqrt, ← NNReal.coe_mul, NNReal.coe_inj, Real.toNNReal_mul hx, NNReal.sqrt_mul]

@[simp]
theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : √(x * y) = √x * √y := by
  rw [mul_comm, sqrt_mul hy, mul_comm]

@[simp]
theorem sqrt_inv (x : ℝ) : √x⁻¹ = (√x)⁻¹ := by
  rw [Real.sqrt, Real.toNNReal_inv, NNReal.sqrt_inv, NNReal.coe_inv, Real.sqrt]

@[simp]
theorem sqrt_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : √(x / y) = √x / √y := by
  rw [division_def, sqrt_mul hx, sqrt_inv, division_def]

@[simp]
theorem sqrt_div' (x) {y : ℝ} (hy : 0 ≤ y) : √(x / y) = √x / √y := by
  rw [division_def, sqrt_mul' x (inv_nonneg.2 hy), sqrt_inv, division_def]

variable {x y : ℝ}

@[simp]
theorem div_sqrt : x / √x = √x := by
  grind

theorem sqrt_div_self' : √x / x = 1 / √x := by rw [← div_sqrt, one_div_div, div_sqrt]

theorem sqrt_div_self : √x / x = (√x)⁻¹ := by rw [sqrt_div_self', one_div]

theorem lt_sqrt (hx : 0 ≤ x) : x < √y ↔ x ^ 2 < y := by
  rw [← sqrt_lt_sqrt_iff (sq_nonneg _), sqrt_sq hx]

theorem sq_lt : x ^ 2 < y ↔ -√y < x ∧ x < √y := by
  rw [← abs_lt, ← sq_abs, lt_sqrt (abs_nonneg _)]

theorem neg_sqrt_lt_of_sq_lt (h : x ^ 2 < y) : -√y < x :=
  (sq_lt.mp h).1

theorem lt_sqrt_of_sq_lt (h : x ^ 2 < y) : x < √y :=
  (sq_lt.mp h).2

theorem lt_sq_of_sqrt_lt (h : √x < y) : x < y ^ 2 := by
  have hy := x.sqrt_nonneg.trans_lt h
  rwa [← sqrt_lt_sqrt_iff_of_pos (sq_pos_of_pos hy), sqrt_sq hy.le]

/-- The natural square root is at most the real square root -/
theorem nat_sqrt_le_real_sqrt {a : ℕ} : ↑(Nat.sqrt a) ≤ √(a : ℝ) := by
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  norm_cast
  exact Nat.sqrt_le' a

/-- The real square root is less than the natural square root plus one -/
theorem real_sqrt_lt_nat_sqrt_succ {a : ℕ} : √(a : ℝ) < Nat.sqrt a + 1 := by
  rw [sqrt_lt (by simp)] <;> norm_cast
  · exact Nat.lt_succ_sqrt' a
  · exact Nat.le_add_left 0 (Nat.sqrt a + 1)

/-- The real square root is at most the natural square root plus one -/
theorem real_sqrt_le_nat_sqrt_succ {a : ℕ} : √(a : ℝ) ≤ Nat.sqrt a + 1 :=
  real_sqrt_lt_nat_sqrt_succ.le

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

theorem sqrt_prod {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ i ∈ s, 0 ≤ x i) :
    √(∏ i ∈ s, x i) = ∏ i ∈ s, √(x i) := by
  convert congr_arg NNReal.toReal <| map_prod NNReal.sqrtHom (Real.toNNReal ∘ x) s <;>
    simp +contextual [-map_prod, NNReal.sqrtHom, hx]

end Real

open Real

variable {α : Type*}

theorem Filter.Tendsto.sqrt {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) :
    Tendsto (fun x => √(f x)) l (𝓝 (√x)) :=
  (continuous_sqrt.tendsto _).comp h

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

nonrec theorem ContinuousWithinAt.sqrt (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => √(f x)) s x :=
  h.sqrt

@[fun_prop]
nonrec theorem ContinuousAt.sqrt (h : ContinuousAt f x) : ContinuousAt (fun x => √(f x)) x :=
  h.sqrt

@[fun_prop]
theorem ContinuousOn.sqrt (h : ContinuousOn f s) : ContinuousOn (fun x => √(f x)) s :=
  fun x hx => (h x hx).sqrt

@[continuity, fun_prop]
theorem Continuous.sqrt (h : Continuous f) : Continuous fun x => √(f x) :=
  continuous_sqrt.comp h

namespace NNReal
variable {ι : Type*}
open Finset

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ≥0`. -/
lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι → ℝ≥0) :
    ∑ i ∈ s, f i * g i ≤ sqrt (∑ i ∈ s, f i ^ 2) * sqrt (∑ i ∈ s, g i ^ 2) :=
  (le_sqrt_iff_sq_le.2 <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq <| sqrt_mul _ _

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
