/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the tanh function

In this file we define an inverse of tanh as a function from ℝ to (-1, 1).

## Main definitions

- `Real.artanh`: An inverse function of `Real.tanh` as a function from ℝ to (-1, 1).

- `Real.tanhPartialEquiv`: `Real.tanh` and `Real.artanh` bundled as a `PartialEquiv`
  from ℝ to (-1, 1).

## Main Results

- `Real.tanh_artanh`, `Real.artanh_tanh`: tanh and artanh are inverse in the appropriate domains.

- `Real.tanh_bijOn`, `Real.tanh_injective`, `Real.tanh_surjOn`: `Real.tanh` is
  bijective, injective and surjective as a function from ℝ to (-1, 1)

- `Real.artanh_bijOn`, `Real.artanh_injOn`, `Real.artanh_surjOn`: `Real.artanh` is bijective,
  injective and surjective as a function from (-1, 1) to ℝ

## Tags

artanh, arctanh, argtanh, atanh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `artanh` is defined using a logarithm, `artanh x = log √((1 + x) / (1 - x))`. -/
@[pp_nodot]
def artanh (x : ℝ) :=
  log √((1 + x) / (1 - x))

theorem artanh_eq_half_log {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    artanh x = 1 / 2 * log ((1 + x) / (1 - x)) := by
  rw [artanh, log_sqrt <| div_nonneg (by grind) (by grind), one_div_mul_eq_div]

theorem exp_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : exp (artanh x) = √((1 + x) / (1 - x)) :=
  exp_log <| sqrt_pos_of_pos <| div_pos (by grind) (by grind)

@[simp]
theorem artanh_zero : artanh 0 = 0 := by simp [artanh]

theorem sinh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : sinh (artanh x) = x / √(1 - x ^ 2) := by
  have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  rw [← one_pow, sq_sub_sq 1 x, sqrt_mul]
    <;> grind [artanh, sinh_eq, exp_neg, exp_log, sqrt_div]

theorem cosh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : cosh (artanh x) = 1 / √(1 - x ^ 2) := by
  have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  rw [← one_pow, sq_sub_sq 1 x, sqrt_mul]
    <;> grind [artanh, cosh_eq, exp_neg, exp_log, sqrt_div]

/-- `artanh` is the right inverse of `tanh` over (-1, 1). -/
theorem tanh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : tanh (artanh x) = x := by
  have := sq_sub_sq 1 x
  grind [tanh_eq_sinh_div_cosh, sinh_artanh, cosh_artanh, sqrt_ne_zero', mul_pos]

/-- `artanh` is the left inverse of `tanh`. -/
theorem artanh_tanh (x : ℝ) : artanh (tanh x) = x := by
  have h : 0 < (1 + tanh x) / (1 - tanh x) :=
    div_pos (by grind [neg_one_lt_tanh]) (by grind [tanh_lt_one])
  rw [artanh, ← exp_eq_exp, exp_log (sqrt_pos_of_pos h),
    ← sq_eq_sq₀ (le_of_lt <| sqrt_pos_of_pos h) (exp_nonneg x),
    sq_sqrt (le_of_lt h), tanh_eq, exp_neg]
  field

theorem strictMonoOn_one_add_div_one_sub :
    StrictMonoOn (fun (x : ℝ) => (1 + x) / (1 - x)) (Ioo (-1) 1) := by
  intro x hx y hy h
  field_simp [show 0 < 1 - x by grind, show 0 < 1 - y by grind]
  grind

theorem strictMonoOn_artanh : StrictMonoOn artanh (Ioo (-1) 1) := by
  apply strictMonoOn_log.comp ?_ fun x hx ↦ sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  apply strictMonoOn_sqrt.comp strictMonoOn_one_add_div_one_sub
    fun x hx ↦ show 0 ≤ (1 + x) / (1 - x) by exact div_nonneg (by grind) (by grind)

theorem artanh_le_artanh_iff {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    artanh x ≤ artanh y ↔ x ≤ y :=
  strictMonoOn_artanh.le_iff_le hx hy

theorem artanh_lt_artanh_iff {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    artanh x < artanh y ↔ x < y :=
  strictMonoOn_artanh.lt_iff_lt hx hy

theorem artanh_le_artanh {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hxy : x ≤ y) :
    artanh x ≤ artanh y :=
  (artanh_le_artanh_iff (by grind) (by grind)).mpr hxy

theorem artanh_lt_artanh {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hxy : x < y) :
    artanh x < artanh y :=
  (artanh_lt_artanh_iff (by grind) (by grind)).mpr hxy

theorem artanh_eq_zero_iff {x : ℝ} : artanh x = 0 ↔ x ≤ -1 ∨ x = 0 ∨ 1 ≤ x := by
  grind [artanh, log_eq_zero, div_nonpos_iff]

theorem artanh_pos {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 < artanh x := by
  rw [← artanh_zero, artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.1

theorem artanh_neg {x : ℝ} (hx : x ∈ Ioo (-1) 0) : artanh x < 0 := by
  rw [← artanh_zero, artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.2

theorem artanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ artanh x := by
  by_cases x < 1
  case pos =>
    rw [← artanh_zero, artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

theorem artanh_nonpos {x : ℝ} (hx : x ≤ 0) : artanh x ≤ 0 := by
  by_cases -1 < x
  case pos =>
    rw [← artanh_zero, artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

/-- `Real.tanh` as a `PartialEquiv`. -/
def tanhPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := tanh
  invFun := artanh
  source := univ
  target := Ioo (-1) 1
  map_source' r _ := mem_Ioo.mpr ⟨neg_one_lt_tanh r, tanh_lt_one r⟩
  map_target' _ _ := trivial
  left_inv' r _ := artanh_tanh r
  right_inv' _ hr := tanh_artanh hr

theorem tanh_bijOn : BijOn tanh univ (Ioo (-1) 1) := tanhPartialEquiv.bijOn

theorem tanh_injective : Injective tanh := fun _ _ ↦ tanhPartialEquiv.injOn trivial trivial

theorem tanh_surjOn : SurjOn tanh univ (Ioo (-1) 1) := tanhPartialEquiv.surjOn

theorem artanh_bijOn : BijOn artanh (Ioo (-1) 1) univ := tanhPartialEquiv.symm.bijOn

theorem artanh_injOn : InjOn artanh (Ioo (-1) 1) := tanhPartialEquiv.symm.injOn

theorem artanh_surjOn : SurjOn artanh (Ioo (-1) 1) univ := tanhPartialEquiv.symm.surjOn

end Real
