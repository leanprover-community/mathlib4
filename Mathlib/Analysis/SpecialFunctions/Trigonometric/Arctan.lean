/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

#align_import analysis.special_functions.trigonometric.arctan from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# The `arctan` function.

Inequalities, identities and `Real.tan` as a `PartialHomeomorph` between `(-(π / 2), π / 2)`
and the whole line.

The result of `arctan x + arctan y` is given by `arctan_add`, `arctan_add_eq_add_pi` or
`arctan_add_eq_sub_pi` depending on whether `x * y < 1` and `0 < x`. As an application of
`arctan_add` we give four Machin-like formulas (linear combinations of arctangents equal to
`π / 4 = arctan 1`), including John Machin's original one at
`four_mul_arctan_inv_5_sub_arctan_inv_239`.
-/


noncomputable section

namespace Real

open Set Filter

open scoped Topology Real

theorem tan_add {x y : ℝ}
    (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) ∨
      (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using
    @Complex.tan_add (x : ℂ) (y : ℂ) (by convert h <;> norm_cast)
#align real.tan_add Real.tan_add

theorem tan_add' {x y : ℝ}
    (h : (∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)
#align real.tan_add' Real.tan_add'

theorem tan_two_mul {x : ℝ} : tan (2 * x) = 2 * tan x / (1 - tan x ^ 2) := by
  have := @Complex.tan_two_mul x
  norm_cast at *
#align real.tan_two_mul Real.tan_two_mul

theorem tan_int_mul_pi_div_two (n : ℤ) : tan (n * π / 2) = 0 :=
  tan_eq_zero_iff.mpr (by use n)
#align real.tan_int_mul_pi_div_two Real.tan_int_mul_pi_div_two

theorem continuousOn_tan : ContinuousOn tan {x | cos x ≠ 0} := by
  suffices ContinuousOn (fun x => sin x / cos x) {x | cos x ≠ 0} by
    have h_eq : (fun x => sin x / cos x) = tan := by ext1 x; rw [tan_eq_sin_div_cos]
    rwa [h_eq] at this
  exact continuousOn_sin.div continuousOn_cos fun x => id
#align real.continuous_on_tan Real.continuousOn_tan

@[continuity]
theorem continuous_tan : Continuous fun x : {x | cos x ≠ 0} => tan x :=
  continuousOn_iff_continuous_restrict.1 continuousOn_tan
#align real.continuous_tan Real.continuous_tan

theorem continuousOn_tan_Ioo : ContinuousOn tan (Ioo (-(π / 2)) (π / 2)) := by
  refine ContinuousOn.mono continuousOn_tan fun x => ?_
  simp only [and_imp, mem_Ioo, mem_setOf_eq, Ne]
  rw [cos_eq_zero_iff]
  rintro hx_gt hx_lt ⟨r, hxr_eq⟩
  rcases le_or_lt 0 r with h | h
  · rw [lt_iff_not_ge] at hx_lt
    refine hx_lt ?_
    rw [hxr_eq, ← one_mul (π / 2), mul_div_assoc, ge_iff_le, mul_le_mul_right (half_pos pi_pos)]
    simp [h]
  · rw [lt_iff_not_ge] at hx_gt
    refine hx_gt ?_
    rw [hxr_eq, ← one_mul (π / 2), mul_div_assoc, ge_iff_le, neg_mul_eq_neg_mul,
      mul_le_mul_right (half_pos pi_pos)]
    have hr_le : r ≤ -1 := by rwa [Int.lt_iff_add_one_le, ← le_neg_iff_add_nonpos_right] at h
    rw [← le_sub_iff_add_le, mul_comm, ← le_div_iff]
    · set_option tactic.skipAssignedInstances false in norm_num
      rw [← Int.cast_one, ← Int.cast_neg]; norm_cast
    · exact zero_lt_two
#align real.continuous_on_tan_Ioo Real.continuousOn_tan_Ioo

theorem surjOn_tan : SurjOn tan (Ioo (-(π / 2)) (π / 2)) univ :=
  have := neg_lt_self pi_div_two_pos
  continuousOn_tan_Ioo.surjOn_of_tendsto (nonempty_Ioo.2 this)
    (by rw [tendsto_comp_coe_Ioo_atBot this]; exact tendsto_tan_neg_pi_div_two)
    (by rw [tendsto_comp_coe_Ioo_atTop this]; exact tendsto_tan_pi_div_two)
#align real.surj_on_tan Real.surjOn_tan

theorem tan_surjective : Function.Surjective tan := fun _ => surjOn_tan.subset_range trivial
#align real.tan_surjective Real.tan_surjective

theorem image_tan_Ioo : tan '' Ioo (-(π / 2)) (π / 2) = univ :=
  univ_subset_iff.1 surjOn_tan
#align real.image_tan_Ioo Real.image_tan_Ioo

/-- `Real.tan` as an `OrderIso` between `(-(π / 2), π / 2)` and `ℝ`. -/
def tanOrderIso : Ioo (-(π / 2)) (π / 2) ≃o ℝ :=
  (strictMonoOn_tan.orderIso _ _).trans <|
    (OrderIso.setCongr _ _ image_tan_Ioo).trans OrderIso.Set.univ
#align real.tan_order_iso Real.tanOrderIso

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and
`arctan x < π / 2` -/
-- @[pp_nodot] -- Porting note: removed
noncomputable def arctan (x : ℝ) : ℝ :=
  tanOrderIso.symm x
#align real.arctan Real.arctan

@[simp]
theorem tan_arctan (x : ℝ) : tan (arctan x) = x :=
  tanOrderIso.apply_symm_apply x
#align real.tan_arctan Real.tan_arctan

theorem arctan_mem_Ioo (x : ℝ) : arctan x ∈ Ioo (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _
#align real.arctan_mem_Ioo Real.arctan_mem_Ioo

@[simp]
theorem range_arctan : range arctan = Ioo (-(π / 2)) (π / 2) :=
  ((EquivLike.surjective _).range_comp _).trans Subtype.range_coe
#align real.range_arctan Real.range_arctan

theorem arctan_tan {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : arctan (tan x) = x :=
  Subtype.ext_iff.1 <| tanOrderIso.symm_apply_apply ⟨x, hx₁, hx₂⟩
#align real.arctan_tan Real.arctan_tan

theorem cos_arctan_pos (x : ℝ) : 0 < cos (arctan x) :=
  cos_pos_of_mem_Ioo <| arctan_mem_Ioo x
#align real.cos_arctan_pos Real.cos_arctan_pos

theorem cos_sq_arctan (x : ℝ) : cos (arctan x) ^ 2 = 1 / (1 + x ^ 2) := by
  rw_mod_cast [one_div, ← inv_one_add_tan_sq (cos_arctan_pos x).ne', tan_arctan]
#align real.cos_sq_arctan Real.cos_sq_arctan

theorem sin_arctan (x : ℝ) : sin (arctan x) = x / √(1 + x ^ 2) := by
  rw_mod_cast [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]
#align real.sin_arctan Real.sin_arctan

theorem cos_arctan (x : ℝ) : cos (arctan x) = 1 / √(1 + x ^ 2) := by
  rw_mod_cast [one_div, ← inv_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]
#align real.cos_arctan Real.cos_arctan

theorem arctan_lt_pi_div_two (x : ℝ) : arctan x < π / 2 :=
  (arctan_mem_Ioo x).2
#align real.arctan_lt_pi_div_two Real.arctan_lt_pi_div_two

theorem neg_pi_div_two_lt_arctan (x : ℝ) : -(π / 2) < arctan x :=
  (arctan_mem_Ioo x).1
#align real.neg_pi_div_two_lt_arctan Real.neg_pi_div_two_lt_arctan

theorem arctan_eq_arcsin (x : ℝ) : arctan x = arcsin (x / √(1 + x ^ 2)) :=
  Eq.symm <| arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo <| arctan_mem_Ioo x)
#align real.arctan_eq_arcsin Real.arctan_eq_arcsin

theorem arcsin_eq_arctan {x : ℝ} (h : x ∈ Ioo (-(1 : ℝ)) 1) :
    arcsin x = arctan (x / √(1 - x ^ 2)) := by
  rw_mod_cast [arctan_eq_arcsin, div_pow, sq_sqrt, one_add_div, div_div, ← sqrt_mul,
    mul_div_cancel₀, sub_add_cancel, sqrt_one, div_one] <;> simp at h <;> nlinarith [h.1, h.2]
#align real.arcsin_eq_arctan Real.arcsin_eq_arctan

@[simp]
theorem arctan_zero : arctan 0 = 0 := by simp [arctan_eq_arcsin]
#align real.arctan_zero Real.arctan_zero

@[mono]
theorem arctan_strictMono : StrictMono arctan := tanOrderIso.symm.strictMono

theorem arctan_injective : arctan.Injective := arctan_strictMono.injective

@[simp]
theorem arctan_eq_zero_iff {x : ℝ} : arctan x = 0 ↔ x = 0 :=
  .trans (by rw [arctan_zero]) arctan_injective.eq_iff

theorem tendsto_arctan_atTop : Tendsto arctan atTop (𝓝[<] (π / 2)) :=
  tendsto_Ioo_atTop.mp tanOrderIso.symm.tendsto_atTop

theorem tendsto_arctan_atBot : Tendsto arctan atBot (𝓝[>] (-(π / 2))) :=
  tendsto_Ioo_atBot.mp tanOrderIso.symm.tendsto_atBot

theorem arctan_eq_of_tan_eq {x y : ℝ} (h : tan x = y) (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    arctan y = x :=
  injOn_tan (arctan_mem_Ioo _) hx (by rw [tan_arctan, h])
#align real.arctan_eq_of_tan_eq Real.arctan_eq_of_tan_eq

@[simp]
theorem arctan_one : arctan 1 = π / 4 :=
  arctan_eq_of_tan_eq tan_pi_div_four <| by constructor <;> linarith [pi_pos]
#align real.arctan_one Real.arctan_one

@[simp]
theorem arctan_neg (x : ℝ) : arctan (-x) = -arctan x := by simp [arctan_eq_arcsin, neg_div]
#align real.arctan_neg Real.arctan_neg

theorem arctan_eq_arccos {x : ℝ} (h : 0 ≤ x) : arctan x = arccos (√(1 + x ^ 2))⁻¹ := by
  rw [arctan_eq_arcsin, arccos_eq_arcsin]; swap; · exact inv_nonneg.2 (sqrt_nonneg _)
  congr 1
  rw_mod_cast [← sqrt_inv, sq_sqrt, ← one_div, one_sub_div, add_sub_cancel_left, sqrt_div,
    sqrt_sq h]
  all_goals positivity
#align real.arctan_eq_arccos Real.arctan_eq_arccos

-- The junk values for `arccos` and `sqrt` make this true even for `1 < x`.
theorem arccos_eq_arctan {x : ℝ} (h : 0 < x) : arccos x = arctan (√(1 - x ^ 2) / x) := by
  rw [arccos, eq_comm]
  refine arctan_eq_of_tan_eq ?_ ⟨?_, ?_⟩
  · rw_mod_cast [tan_pi_div_two_sub, tan_arcsin, inv_div]
  · linarith only [arcsin_le_pi_div_two x, pi_pos]
  · linarith only [arcsin_pos.2 h]
#align real.arccos_eq_arctan Real.arccos_eq_arctan

theorem arctan_inv_of_pos {x : ℝ} (h : 0 < x) : arctan x⁻¹ = π / 2 - arctan x := by
  rw [← arctan_tan (x := _ - _), tan_pi_div_two_sub, tan_arctan]
  · norm_num
    exact (arctan_lt_pi_div_two x).trans (half_lt_self_iff.mpr pi_pos)
  · rw [sub_lt_self_iff, ← arctan_zero]
    exact tanOrderIso.symm.strictMono h

theorem arctan_inv_of_neg {x : ℝ} (h : x < 0) : arctan x⁻¹ = -(π / 2) - arctan x := by
  have := arctan_inv_of_pos (neg_pos.mpr h)
  rwa [inv_neg, arctan_neg, neg_eq_iff_eq_neg, neg_sub', arctan_neg, neg_neg] at this

section ArctanAdd

lemma arctan_ne_mul_pi_div_two {x : ℝ} : ∀ (k : ℤ), arctan x ≠ (2 * k + 1) * π / 2 := by
  by_contra!
  obtain ⟨k, h⟩ := this
  obtain ⟨lb, ub⟩ := arctan_mem_Ioo x
  rw [h, neg_eq_neg_one_mul, mul_div_assoc, mul_lt_mul_right (by positivity)] at lb
  rw [h, ← one_mul (π / 2), mul_div_assoc, mul_lt_mul_right (by positivity)] at ub
  norm_cast at lb ub; change -1 < _ at lb; omega

lemma arctan_add_arctan_lt_pi_div_two {x y : ℝ} (h : x * y < 1) : arctan x + arctan y < π / 2 := by
  cases' le_or_lt y 0 with hy hy
  · rw [← add_zero (π / 2), ← arctan_zero]
    exact add_lt_add_of_lt_of_le (arctan_lt_pi_div_two _) (tanOrderIso.symm.monotone hy)
  · rw [← lt_div_iff hy, ← inv_eq_one_div] at h
    replace h : arctan x < arctan y⁻¹ := tanOrderIso.symm.strictMono h
    rwa [arctan_inv_of_pos hy, lt_tsub_iff_right] at h

theorem arctan_add {x y : ℝ} (h : x * y < 1) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) := by
  rw [← arctan_tan (x := _ + _)]
  · congr
    conv_rhs => rw [← tan_arctan x, ← tan_arctan y]
    exact tan_add' ⟨arctan_ne_mul_pi_div_two, arctan_ne_mul_pi_div_two⟩
  · rw [neg_lt, neg_add, ← arctan_neg, ← arctan_neg]
    rw [← neg_mul_neg] at h
    exact arctan_add_arctan_lt_pi_div_two h
  · exact arctan_add_arctan_lt_pi_div_two h

theorem arctan_add_eq_add_pi {x y : ℝ} (h : 1 < x * y) (hx : 0 < x) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) + π := by
  have hy : 0 < y := by
    have := mul_pos_iff.mp (zero_lt_one.trans h)
    simpa [hx, hx.asymm]
  have k := arctan_add (mul_inv x y ▸ inv_lt_one h)
  rw [arctan_inv_of_pos hx, arctan_inv_of_pos hy, show _ + _ = π - (arctan x + arctan y) by ring,
    sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', sub_eq_add_neg, ← arctan_neg, add_comm] at k
  convert k.symm using 3
  field_simp
  rw [show -x + -y = -(x + y) by ring, show x * y - 1 = -(1 - x * y) by ring, neg_div_neg_eq]

theorem arctan_add_eq_sub_pi {x y : ℝ} (h : 1 < x * y) (hx : x < 0) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) - π := by
  rw [← neg_mul_neg] at h
  have k := arctan_add_eq_add_pi h (neg_pos.mpr hx)
  rw [show _ / _ = -((x + y) / (1 - x * y)) by ring, ← neg_inj] at k
  simp only [arctan_neg, neg_add, neg_neg, ← sub_eq_add_neg _ π] at k
  exact k

theorem two_mul_arctan {x : ℝ} (h₁ : -1 < x) (h₂ : x < 1) :
    2 * arctan x = arctan (2 * x / (1 - x ^ 2)) := by
  rw [two_mul, arctan_add (by nlinarith)]; congr 1; ring

theorem two_mul_arctan_add_pi {x : ℝ} (h : 1 < x) :
    2 * arctan x = arctan (2 * x / (1 - x ^ 2)) + π := by
  rw [two_mul, arctan_add_eq_add_pi (by nlinarith) (by linarith)]; congr 2; ring

theorem two_mul_arctan_sub_pi {x : ℝ} (h : x < -1) :
    2 * arctan x = arctan (2 * x / (1 - x ^ 2)) - π := by
  rw [two_mul, arctan_add_eq_sub_pi (by nlinarith) (by linarith)]; congr 2; ring

theorem arctan_inv_2_add_arctan_inv_3 : arctan 2⁻¹ + arctan 3⁻¹ = π / 4 := by
  rw [arctan_add] <;> norm_num

theorem two_mul_arctan_inv_2_sub_arctan_inv_7 : 2 * arctan 2⁻¹ - arctan 7⁻¹ = π / 4 := by
  rw [two_mul_arctan, ← arctan_one, sub_eq_iff_eq_add, arctan_add] <;> norm_num

theorem two_mul_arctan_inv_3_add_arctan_inv_7 : 2 * arctan 3⁻¹ + arctan 7⁻¹ = π / 4 := by
  rw [two_mul_arctan, arctan_add] <;> norm_num

/-- **John Machin's 1706 formula**, which he used to compute π to 100 decimal places. -/
theorem four_mul_arctan_inv_5_sub_arctan_inv_239 : 4 * arctan 5⁻¹ - arctan 239⁻¹ = π / 4 := by
  rw [show 4 * arctan _ = 2 * (2 * _) by ring, two_mul_arctan, two_mul_arctan, ← arctan_one,
    sub_eq_iff_eq_add, arctan_add] <;> norm_num

end ArctanAdd

@[continuity]
theorem continuous_arctan : Continuous arctan :=
  continuous_subtype_val.comp tanOrderIso.toHomeomorph.continuous_invFun
#align real.continuous_arctan Real.continuous_arctan

theorem continuousAt_arctan {x : ℝ} : ContinuousAt arctan x :=
  continuous_arctan.continuousAt
#align real.continuous_at_arctan Real.continuousAt_arctan

/-- `Real.tan` as a `PartialHomeomorph` between `(-(π / 2), π / 2)` and the whole line. -/
def tanPartialHomeomorph : PartialHomeomorph ℝ ℝ where
  toFun := tan
  invFun := arctan
  source := Ioo (-(π / 2)) (π / 2)
  target := univ
  map_source' := mapsTo_univ _ _
  map_target' y _ := arctan_mem_Ioo y
  left_inv' _ hx := arctan_tan hx.1 hx.2
  right_inv' y _ := tan_arctan y
  open_source := isOpen_Ioo
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_tan_Ioo
  continuousOn_invFun := continuous_arctan.continuousOn
#align real.tan_local_homeomorph Real.tanPartialHomeomorph

@[simp]
theorem coe_tanPartialHomeomorph : ⇑tanPartialHomeomorph = tan :=
  rfl
#align real.coe_tan_local_homeomorph Real.coe_tanPartialHomeomorph

@[simp]
theorem coe_tanPartialHomeomorph_symm : ⇑tanPartialHomeomorph.symm = arctan :=
  rfl
#align real.coe_tan_local_homeomorph_symm Real.coe_tanPartialHomeomorph_symm

end Real
