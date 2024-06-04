/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.ProjIcc

#align_import analysis.special_functions.trigonometric.inverse from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Inverse trigonometric functions.

See also `Analysis.SpecialFunctions.Trigonometric.Arctan` for the inverse tan function.
(This is delayed as it is easier to set up after developing complex trigonometric functions.)

Basic inequalities on trigonometric functions.
-/


noncomputable section

open scoped Classical
open Topology Filter

open Set Filter

open Real

namespace Real
variable {x y : ℝ}

/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ π / 2`.
It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`. -/
-- @[pp_nodot] Porting note: not implemented
noncomputable def arcsin : ℝ → ℝ :=
  Subtype.val ∘ IccExtend (neg_le_self zero_le_one) sinOrderIso.symm
#align real.arcsin Real.arcsin

theorem arcsin_mem_Icc (x : ℝ) : arcsin x ∈ Icc (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _
#align real.arcsin_mem_Icc Real.arcsin_mem_Icc

@[simp]
theorem range_arcsin : range arcsin = Icc (-(π / 2)) (π / 2) := by
  rw [arcsin, range_comp Subtype.val]
  simp [Icc]
#align real.range_arcsin Real.range_arcsin

theorem arcsin_le_pi_div_two (x : ℝ) : arcsin x ≤ π / 2 :=
  (arcsin_mem_Icc x).2
#align real.arcsin_le_pi_div_two Real.arcsin_le_pi_div_two

theorem neg_pi_div_two_le_arcsin (x : ℝ) : -(π / 2) ≤ arcsin x :=
  (arcsin_mem_Icc x).1
#align real.neg_pi_div_two_le_arcsin Real.neg_pi_div_two_le_arcsin

theorem arcsin_projIcc (x : ℝ) :
    arcsin (projIcc (-1) 1 (neg_le_self zero_le_one) x) = arcsin x := by
  rw [arcsin, Function.comp_apply, IccExtend_val, Function.comp_apply, IccExtend,
        Function.comp_apply]
#align real.arcsin_proj_Icc Real.arcsin_projIcc

theorem sin_arcsin' {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : sin (arcsin x) = x := by
  simpa [arcsin, IccExtend_of_mem _ _ hx, -OrderIso.apply_symm_apply] using
    Subtype.ext_iff.1 (sinOrderIso.apply_symm_apply ⟨x, hx⟩)
#align real.sin_arcsin' Real.sin_arcsin'

theorem sin_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arcsin x) = x :=
  sin_arcsin' ⟨hx₁, hx₂⟩
#align real.sin_arcsin Real.sin_arcsin

theorem arcsin_sin' {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : arcsin (sin x) = x :=
  injOn_sin (arcsin_mem_Icc _) hx <| by rw [sin_arcsin (neg_one_le_sin _) (sin_le_one _)]
#align real.arcsin_sin' Real.arcsin_sin'

theorem arcsin_sin {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : arcsin (sin x) = x :=
  arcsin_sin' ⟨hx₁, hx₂⟩
#align real.arcsin_sin Real.arcsin_sin

theorem strictMonoOn_arcsin : StrictMonoOn arcsin (Icc (-1) 1) :=
  (Subtype.strictMono_coe _).comp_strictMonoOn <|
    sinOrderIso.symm.strictMono.strictMonoOn_IccExtend _
#align real.strict_mono_on_arcsin Real.strictMonoOn_arcsin

theorem monotone_arcsin : Monotone arcsin :=
  (Subtype.mono_coe _).comp <| sinOrderIso.symm.monotone.IccExtend _
#align real.monotone_arcsin Real.monotone_arcsin

theorem injOn_arcsin : InjOn arcsin (Icc (-1) 1) :=
  strictMonoOn_arcsin.injOn
#align real.inj_on_arcsin Real.injOn_arcsin

theorem arcsin_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
    arcsin x = arcsin y ↔ x = y :=
  injOn_arcsin.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
#align real.arcsin_inj Real.arcsin_inj

@[continuity]
theorem continuous_arcsin : Continuous arcsin :=
  continuous_subtype_val.comp sinOrderIso.symm.continuous.Icc_extend'
#align real.continuous_arcsin Real.continuous_arcsin

theorem continuousAt_arcsin {x : ℝ} : ContinuousAt arcsin x :=
  continuous_arcsin.continuousAt
#align real.continuous_at_arcsin Real.continuousAt_arcsin

theorem arcsin_eq_of_sin_eq {x y : ℝ} (h₁ : sin x = y) (h₂ : x ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin y = x := by
  subst y
  exact injOn_sin (arcsin_mem_Icc _) h₂ (sin_arcsin' (sin_mem_Icc x))
#align real.arcsin_eq_of_sin_eq Real.arcsin_eq_of_sin_eq

@[simp]
theorem arcsin_zero : arcsin 0 = 0 :=
  arcsin_eq_of_sin_eq sin_zero ⟨neg_nonpos.2 pi_div_two_pos.le, pi_div_two_pos.le⟩
#align real.arcsin_zero Real.arcsin_zero

@[simp]
theorem arcsin_one : arcsin 1 = π / 2 :=
  arcsin_eq_of_sin_eq sin_pi_div_two <| right_mem_Icc.2 (neg_le_self pi_div_two_pos.le)
#align real.arcsin_one Real.arcsin_one

theorem arcsin_of_one_le {x : ℝ} (hx : 1 ≤ x) : arcsin x = π / 2 := by
  rw [← arcsin_projIcc, projIcc_of_right_le _ hx, Subtype.coe_mk, arcsin_one]
#align real.arcsin_of_one_le Real.arcsin_of_one_le

theorem arcsin_neg_one : arcsin (-1) = -(π / 2) :=
  arcsin_eq_of_sin_eq (by rw [sin_neg, sin_pi_div_two]) <|
    left_mem_Icc.2 (neg_le_self pi_div_two_pos.le)
#align real.arcsin_neg_one Real.arcsin_neg_one

theorem arcsin_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arcsin x = -(π / 2) := by
  rw [← arcsin_projIcc, projIcc_of_le_left _ hx, Subtype.coe_mk, arcsin_neg_one]
#align real.arcsin_of_le_neg_one Real.arcsin_of_le_neg_one

@[simp]
theorem arcsin_neg (x : ℝ) : arcsin (-x) = -arcsin x := by
  rcases le_total x (-1) with hx₁ | hx₁
  · rw [arcsin_of_le_neg_one hx₁, neg_neg, arcsin_of_one_le (le_neg.2 hx₁)]
  rcases le_total 1 x with hx₂ | hx₂
  · rw [arcsin_of_one_le hx₂, arcsin_of_le_neg_one (neg_le_neg hx₂)]
  refine arcsin_eq_of_sin_eq ?_ ?_
  · rw [sin_neg, sin_arcsin hx₁ hx₂]
  · exact ⟨neg_le_neg (arcsin_le_pi_div_two _), neg_le.2 (neg_pi_div_two_le_arcsin _)⟩
#align real.arcsin_neg Real.arcsin_neg

theorem arcsin_le_iff_le_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin x ≤ y ↔ x ≤ sin y := by
  rw [← arcsin_sin' hy, strictMonoOn_arcsin.le_iff_le hx (sin_mem_Icc _), arcsin_sin' hy]
#align real.arcsin_le_iff_le_sin Real.arcsin_le_iff_le_sin

theorem arcsin_le_iff_le_sin' {x y : ℝ} (hy : y ∈ Ico (-(π / 2)) (π / 2)) :
    arcsin x ≤ y ↔ x ≤ sin y := by
  rcases le_total x (-1) with hx₁ | hx₁
  · simp [arcsin_of_le_neg_one hx₁, hy.1, hx₁.trans (neg_one_le_sin _)]
  cases' lt_or_le 1 x with hx₂ hx₂
  · simp [arcsin_of_one_le hx₂.le, hy.2.not_le, (sin_le_one y).trans_lt hx₂]
  exact arcsin_le_iff_le_sin ⟨hx₁, hx₂⟩ (mem_Icc_of_Ico hy)
#align real.arcsin_le_iff_le_sin' Real.arcsin_le_iff_le_sin'

theorem le_arcsin_iff_sin_le {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    x ≤ arcsin y ↔ sin x ≤ y := by
  rw [← neg_le_neg_iff, ← arcsin_neg,
    arcsin_le_iff_le_sin ⟨neg_le_neg hy.2, neg_le.2 hy.1⟩ ⟨neg_le_neg hx.2, neg_le.2 hx.1⟩, sin_neg,
    neg_le_neg_iff]
#align real.le_arcsin_iff_sin_le Real.le_arcsin_iff_sin_le

theorem le_arcsin_iff_sin_le' {x y : ℝ} (hx : x ∈ Ioc (-(π / 2)) (π / 2)) :
    x ≤ arcsin y ↔ sin x ≤ y := by
  rw [← neg_le_neg_iff, ← arcsin_neg, arcsin_le_iff_le_sin' ⟨neg_le_neg hx.2, neg_lt.2 hx.1⟩,
    sin_neg, neg_le_neg_iff]
#align real.le_arcsin_iff_sin_le' Real.le_arcsin_iff_sin_le'

theorem arcsin_lt_iff_lt_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
  not_le.symm.trans <| (not_congr <| le_arcsin_iff_sin_le hy hx).trans not_le
#align real.arcsin_lt_iff_lt_sin Real.arcsin_lt_iff_lt_sin

theorem arcsin_lt_iff_lt_sin' {x y : ℝ} (hy : y ∈ Ioc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
  not_le.symm.trans <| (not_congr <| le_arcsin_iff_sin_le' hy).trans not_le
#align real.arcsin_lt_iff_lt_sin' Real.arcsin_lt_iff_lt_sin'

theorem lt_arcsin_iff_sin_lt {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    x < arcsin y ↔ sin x < y :=
  not_le.symm.trans <| (not_congr <| arcsin_le_iff_le_sin hy hx).trans not_le
#align real.lt_arcsin_iff_sin_lt Real.lt_arcsin_iff_sin_lt

theorem lt_arcsin_iff_sin_lt' {x y : ℝ} (hx : x ∈ Ico (-(π / 2)) (π / 2)) :
    x < arcsin y ↔ sin x < y :=
  not_le.symm.trans <| (not_congr <| arcsin_le_iff_le_sin' hx).trans not_le
#align real.lt_arcsin_iff_sin_lt' Real.lt_arcsin_iff_sin_lt'

theorem arcsin_eq_iff_eq_sin {x y : ℝ} (hy : y ∈ Ioo (-(π / 2)) (π / 2)) :
    arcsin x = y ↔ x = sin y := by
  simp only [le_antisymm_iff, arcsin_le_iff_le_sin' (mem_Ico_of_Ioo hy),
    le_arcsin_iff_sin_le' (mem_Ioc_of_Ioo hy)]
#align real.arcsin_eq_iff_eq_sin Real.arcsin_eq_iff_eq_sin

@[simp]
theorem arcsin_nonneg {x : ℝ} : 0 ≤ arcsin x ↔ 0 ≤ x :=
  (le_arcsin_iff_sin_le' ⟨neg_lt_zero.2 pi_div_two_pos, pi_div_two_pos.le⟩).trans <| by
    rw [sin_zero]
#align real.arcsin_nonneg Real.arcsin_nonneg

@[simp]
theorem arcsin_nonpos {x : ℝ} : arcsin x ≤ 0 ↔ x ≤ 0 :=
  neg_nonneg.symm.trans <| arcsin_neg x ▸ arcsin_nonneg.trans neg_nonneg
#align real.arcsin_nonpos Real.arcsin_nonpos

@[simp]
theorem arcsin_eq_zero_iff {x : ℝ} : arcsin x = 0 ↔ x = 0 := by simp [le_antisymm_iff]
#align real.arcsin_eq_zero_iff Real.arcsin_eq_zero_iff

@[simp]
theorem zero_eq_arcsin_iff {x} : 0 = arcsin x ↔ x = 0 :=
  eq_comm.trans arcsin_eq_zero_iff
#align real.zero_eq_arcsin_iff Real.zero_eq_arcsin_iff

@[simp]
theorem arcsin_pos {x : ℝ} : 0 < arcsin x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arcsin_nonpos
#align real.arcsin_pos Real.arcsin_pos

@[simp]
theorem arcsin_lt_zero {x : ℝ} : arcsin x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arcsin_nonneg
#align real.arcsin_lt_zero Real.arcsin_lt_zero

@[simp]
theorem arcsin_lt_pi_div_two {x : ℝ} : arcsin x < π / 2 ↔ x < 1 :=
  (arcsin_lt_iff_lt_sin' (right_mem_Ioc.2 <| neg_lt_self pi_div_two_pos)).trans <| by
    rw [sin_pi_div_two]
#align real.arcsin_lt_pi_div_two Real.arcsin_lt_pi_div_two

@[simp]
theorem neg_pi_div_two_lt_arcsin {x : ℝ} : -(π / 2) < arcsin x ↔ -1 < x :=
  (lt_arcsin_iff_sin_lt' <| left_mem_Ico.2 <| neg_lt_self pi_div_two_pos).trans <| by
    rw [sin_neg, sin_pi_div_two]
#align real.neg_pi_div_two_lt_arcsin Real.neg_pi_div_two_lt_arcsin

@[simp]
theorem arcsin_eq_pi_div_two {x : ℝ} : arcsin x = π / 2 ↔ 1 ≤ x :=
  ⟨fun h => not_lt.1 fun h' => (arcsin_lt_pi_div_two.2 h').ne h, arcsin_of_one_le⟩
#align real.arcsin_eq_pi_div_two Real.arcsin_eq_pi_div_two

@[simp]
theorem pi_div_two_eq_arcsin {x} : π / 2 = arcsin x ↔ 1 ≤ x :=
  eq_comm.trans arcsin_eq_pi_div_two
#align real.pi_div_two_eq_arcsin Real.pi_div_two_eq_arcsin

@[simp]
theorem pi_div_two_le_arcsin {x} : π / 2 ≤ arcsin x ↔ 1 ≤ x :=
  (arcsin_le_pi_div_two x).le_iff_eq.trans pi_div_two_eq_arcsin
#align real.pi_div_two_le_arcsin Real.pi_div_two_le_arcsin

@[simp]
theorem arcsin_eq_neg_pi_div_two {x : ℝ} : arcsin x = -(π / 2) ↔ x ≤ -1 :=
  ⟨fun h => not_lt.1 fun h' => (neg_pi_div_two_lt_arcsin.2 h').ne' h, arcsin_of_le_neg_one⟩
#align real.arcsin_eq_neg_pi_div_two Real.arcsin_eq_neg_pi_div_two

@[simp]
theorem neg_pi_div_two_eq_arcsin {x} : -(π / 2) = arcsin x ↔ x ≤ -1 :=
  eq_comm.trans arcsin_eq_neg_pi_div_two
#align real.neg_pi_div_two_eq_arcsin Real.neg_pi_div_two_eq_arcsin

@[simp]
theorem arcsin_le_neg_pi_div_two {x} : arcsin x ≤ -(π / 2) ↔ x ≤ -1 :=
  (neg_pi_div_two_le_arcsin x).le_iff_eq.trans arcsin_eq_neg_pi_div_two
#align real.arcsin_le_neg_pi_div_two Real.arcsin_le_neg_pi_div_two

@[simp]
theorem pi_div_four_le_arcsin {x} : π / 4 ≤ arcsin x ↔ √2 / 2 ≤ x := by
  rw [← sin_pi_div_four, le_arcsin_iff_sin_le']
  have := pi_pos
  constructor <;> linarith
#align real.pi_div_four_le_arcsin Real.pi_div_four_le_arcsin

theorem mapsTo_sin_Ioo : MapsTo sin (Ioo (-(π / 2)) (π / 2)) (Ioo (-1) 1) := fun x h => by
  rwa [mem_Ioo, ← arcsin_lt_pi_div_two, ← neg_pi_div_two_lt_arcsin, arcsin_sin h.1.le h.2.le]
#align real.maps_to_sin_Ioo Real.mapsTo_sin_Ioo

/-- `Real.sin` as a `PartialHomeomorph` between `(-π / 2, π / 2)` and `(-1, 1)`. -/
@[simp]
def sinPartialHomeomorph : PartialHomeomorph ℝ ℝ where
  toFun := sin
  invFun := arcsin
  source := Ioo (-(π / 2)) (π / 2)
  target := Ioo (-1) 1
  map_source' := mapsTo_sin_Ioo
  map_target' _ hy := ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩
  left_inv' _ hx := arcsin_sin hx.1.le hx.2.le
  right_inv' _ hy := sin_arcsin hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_sin.continuousOn
  continuousOn_invFun := continuous_arcsin.continuousOn
#align real.sin_local_homeomorph Real.sinPartialHomeomorph

theorem cos_arcsin_nonneg (x : ℝ) : 0 ≤ cos (arcsin x) :=
  cos_nonneg_of_mem_Icc ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩
#align real.cos_arcsin_nonneg Real.cos_arcsin_nonneg

-- The junk values for `arcsin` and `sqrt` make this true even outside `[-1, 1]`.
theorem cos_arcsin (x : ℝ) : cos (arcsin x) = √(1 - x ^ 2) := by
  by_cases hx₁ : -1 ≤ x; swap
  · rw [not_le] at hx₁
    rw [arcsin_of_le_neg_one hx₁.le, cos_neg, cos_pi_div_two, sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x ≤ 1; swap
  · rw [not_le] at hx₂
    rw [arcsin_of_one_le hx₂.le, cos_pi_div_two, sqrt_eq_zero_of_nonpos]
    nlinarith
  have : sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x)
  rw [← eq_sub_iff_add_eq', ← sqrt_inj (sq_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x))), sq,
    sqrt_mul_self (cos_arcsin_nonneg _)] at this
  rw [this, sin_arcsin hx₁ hx₂]
#align real.cos_arcsin Real.cos_arcsin

-- The junk values for `arcsin` and `sqrt` make this true even outside `[-1, 1]`.
theorem tan_arcsin (x : ℝ) : tan (arcsin x) = x / √(1 - x ^ 2) := by
  rw [tan_eq_sin_div_cos, cos_arcsin]
  by_cases hx₁ : -1 ≤ x; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  by_cases hx₂ : x ≤ 1; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  rw [sin_arcsin hx₁ hx₂]
#align real.tan_arcsin Real.tan_arcsin

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  It defaults to `π` on `(-∞, -1)` and to `0` to `(1, ∞)`. -/
-- @[pp_nodot] Porting note: not implemented
noncomputable def arccos (x : ℝ) : ℝ :=
  π / 2 - arcsin x
#align real.arccos Real.arccos

theorem arccos_eq_pi_div_two_sub_arcsin (x : ℝ) : arccos x = π / 2 - arcsin x :=
  rfl
#align real.arccos_eq_pi_div_two_sub_arcsin Real.arccos_eq_pi_div_two_sub_arcsin

theorem arcsin_eq_pi_div_two_sub_arccos (x : ℝ) : arcsin x = π / 2 - arccos x := by simp [arccos]
#align real.arcsin_eq_pi_div_two_sub_arccos Real.arcsin_eq_pi_div_two_sub_arccos

theorem arccos_le_pi (x : ℝ) : arccos x ≤ π := by
  unfold arccos; linarith [neg_pi_div_two_le_arcsin x]
#align real.arccos_le_pi Real.arccos_le_pi

theorem arccos_nonneg (x : ℝ) : 0 ≤ arccos x := by
  unfold arccos; linarith [arcsin_le_pi_div_two x]
#align real.arccos_nonneg Real.arccos_nonneg

@[simp]
theorem arccos_pos {x : ℝ} : 0 < arccos x ↔ x < 1 := by simp [arccos]
#align real.arccos_pos Real.arccos_pos

theorem cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x := by
  rw [arccos, cos_pi_div_two_sub, sin_arcsin hx₁ hx₂]
#align real.cos_arccos Real.cos_arccos

theorem arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x := by
  rw [arccos, ← sin_pi_div_two_sub, arcsin_sin] <;> simp [sub_eq_add_neg] <;> linarith
#align real.arccos_cos Real.arccos_cos

lemma arccos_eq_of_eq_cos (hy₀ : 0 ≤ y) (hy₁ : y ≤ π) (hxy : x = cos y) : arccos x = y := by
  rw [hxy, arccos_cos hy₀ hy₁]

theorem strictAntiOn_arccos : StrictAntiOn arccos (Icc (-1) 1) := fun _ hx _ hy h =>
  sub_lt_sub_left (strictMonoOn_arcsin hx hy h) _
#align real.strict_anti_on_arccos Real.strictAntiOn_arccos

theorem arccos_injOn : InjOn arccos (Icc (-1) 1) :=
  strictAntiOn_arccos.injOn
#align real.arccos_inj_on Real.arccos_injOn

theorem arccos_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
    arccos x = arccos y ↔ x = y :=
  arccos_injOn.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
#align real.arccos_inj Real.arccos_inj

@[simp]
theorem arccos_zero : arccos 0 = π / 2 := by simp [arccos]
#align real.arccos_zero Real.arccos_zero

@[simp]
theorem arccos_one : arccos 1 = 0 := by simp [arccos]
#align real.arccos_one Real.arccos_one

@[simp]
theorem arccos_neg_one : arccos (-1) = π := by simp [arccos, add_halves]
#align real.arccos_neg_one Real.arccos_neg_one

@[simp]
theorem arccos_eq_zero {x} : arccos x = 0 ↔ 1 ≤ x := by simp [arccos, sub_eq_zero]
#align real.arccos_eq_zero Real.arccos_eq_zero

@[simp]
theorem arccos_eq_pi_div_two {x} : arccos x = π / 2 ↔ x = 0 := by simp [arccos]
#align real.arccos_eq_pi_div_two Real.arccos_eq_pi_div_two

@[simp]
theorem arccos_eq_pi {x} : arccos x = π ↔ x ≤ -1 := by
  rw [arccos, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', div_two_sub_self, neg_pi_div_two_eq_arcsin]
#align real.arccos_eq_pi Real.arccos_eq_pi

theorem arccos_neg (x : ℝ) : arccos (-x) = π - arccos x := by
  rw [← add_halves π, arccos, arcsin_neg, arccos, add_sub_assoc, sub_sub_self, sub_neg_eq_add]
#align real.arccos_neg Real.arccos_neg

theorem arccos_of_one_le {x : ℝ} (hx : 1 ≤ x) : arccos x = 0 := by
  rw [arccos, arcsin_of_one_le hx, sub_self]
#align real.arccos_of_one_le Real.arccos_of_one_le

theorem arccos_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arccos x = π := by
  rw [arccos, arcsin_of_le_neg_one hx, sub_neg_eq_add, add_halves']
#align real.arccos_of_le_neg_one Real.arccos_of_le_neg_one

-- The junk values for `arccos` and `sqrt` make this true even outside `[-1, 1]`.
theorem sin_arccos (x : ℝ) : sin (arccos x) = √(1 - x ^ 2) := by
  by_cases hx₁ : -1 ≤ x; swap
  · rw [not_le] at hx₁
    rw [arccos_of_le_neg_one hx₁.le, sin_pi, sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x ≤ 1; swap
  · rw [not_le] at hx₂
    rw [arccos_of_one_le hx₂.le, sin_zero, sqrt_eq_zero_of_nonpos]
    nlinarith
  rw [arccos_eq_pi_div_two_sub_arcsin, sin_pi_div_two_sub, cos_arcsin]
#align real.sin_arccos Real.sin_arccos

@[simp]
theorem arccos_le_pi_div_two {x} : arccos x ≤ π / 2 ↔ 0 ≤ x := by simp [arccos]
#align real.arccos_le_pi_div_two Real.arccos_le_pi_div_two

@[simp]
theorem arccos_lt_pi_div_two {x : ℝ} : arccos x < π / 2 ↔ 0 < x := by simp [arccos]
#align real.arccos_lt_pi_div_two Real.arccos_lt_pi_div_two

@[simp]
theorem arccos_le_pi_div_four {x} : arccos x ≤ π / 4 ↔ √2 / 2 ≤ x := by
  rw [arccos, ← pi_div_four_le_arcsin]
  constructor <;>
    · intro
      linarith
#align real.arccos_le_pi_div_four Real.arccos_le_pi_div_four

@[continuity]
theorem continuous_arccos : Continuous arccos :=
  continuous_const.sub continuous_arcsin
#align real.continuous_arccos Real.continuous_arccos

-- The junk values for `arccos` and `sqrt` make this true even outside `[-1, 1]`.
theorem tan_arccos (x : ℝ) : tan (arccos x) = √(1 - x ^ 2) / x := by
  rw [arccos, tan_pi_div_two_sub, tan_arcsin, inv_div]
#align real.tan_arccos Real.tan_arccos

-- The junk values for `arccos` and `sqrt` make this true even for `1 < x`.
theorem arccos_eq_arcsin {x : ℝ} (h : 0 ≤ x) : arccos x = arcsin (√(1 - x ^ 2)) :=
  (arcsin_eq_of_sin_eq (sin_arccos _)
      ⟨(Left.neg_nonpos_iff.2 (div_nonneg pi_pos.le (by norm_num))).trans (arccos_nonneg _),
        arccos_le_pi_div_two.2 h⟩).symm
#align real.arccos_eq_arcsin Real.arccos_eq_arcsin

-- The junk values for `arcsin` and `sqrt` make this true even for `1 < x`.
theorem arcsin_eq_arccos {x : ℝ} (h : 0 ≤ x) : arcsin x = arccos (√(1 - x ^ 2)) := by
  rw [eq_comm, ← cos_arcsin]
  exact
    arccos_cos (arcsin_nonneg.2 h)
      ((arcsin_le_pi_div_two _).trans (div_le_self pi_pos.le one_le_two))
#align real.arcsin_eq_arccos Real.arcsin_eq_arccos

end Real
