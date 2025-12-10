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

- `Real.tanhPartialEquiv`: `Real.tanh` as a `PartialEquiv`.

## Main Results

- `Real.tanh_artanh`, `Real.artanh_tanh`: tanh and artanh are inverse in the appropriate domains.

## Tags

artanh, arctanh, argtanh, atanh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `artanh` is defined using a logarithm, `arcosh x = log √((1 + x) / (1 - x))`. -/
@[pp_nodot]
def artanh (x : ℝ) :=
  log √((1 + x) / (1 - x))

theorem artanh_eq_half_log {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    artanh x = 1 / 2 * log ((1 + x) / (1 - x)) := by
  rw [artanh, log_sqrt <| le_of_lt <| div_pos (neg_lt_iff_pos_add'.mp hx.1) (sub_pos.mpr hx.2),
    one_div_mul_eq_div]

theorem exp_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : exp (artanh x) = √((1 + x) / (1 - x)) :=
  exp_log <| sqrt_pos_of_pos <| div_pos (neg_lt_iff_pos_add'.mp hx.1) (sub_pos.mpr hx.2)

@[simp]
theorem artanh_zero : artanh 0 = 0 := by simp [artanh]

theorem sinh_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : sinh (artanh x) = x / √(1 - x ^ 2) := by
  have : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
  rw [this, artanh, sinh_eq, exp_neg, exp_log, sqrt_div, sqrt_mul]
  · field_simp
    rw [sq_sqrt, sq_sqrt]
    · ring
    · exact le_of_lt <| sub_pos.mpr hx.2
    · exact le_of_lt <| neg_lt_iff_pos_add'.mp hx.1
  · exact le_of_lt <| neg_lt_iff_pos_add'.mp hx.1
  · exact le_of_lt <| neg_lt_iff_pos_add'.mp hx.1
  · exact sqrt_pos_of_pos <| div_pos (neg_lt_iff_pos_add'.mp hx.1) (sub_pos.mpr hx.2)

theorem cosh_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : cosh (artanh x) = 1 / √(1 - x ^ 2) := by
  have : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
  rw [this, artanh, cosh_eq, exp_neg, exp_log, sqrt_div, sqrt_mul]
  · field_simp
    rw [sq_sqrt, sq_sqrt]
    · ring
    · exact le_of_lt <| sub_pos.mpr hx.2
    · exact le_of_lt <| neg_lt_iff_pos_add'.mp hx.1
  · exact le_of_lt <| neg_lt_iff_pos_add'.mp hx.1
  · exact le_of_lt <| neg_lt_iff_pos_add'.mp hx.1
  · exact sqrt_pos_of_pos <| div_pos (neg_lt_iff_pos_add'.mp hx.1) (sub_pos.mpr hx.2)

/-- `artanh` is the right inverse of `tanh` over (-1, 1). -/
theorem tanh_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : tanh (artanh x) = x := by
  rw [tanh_eq_sinh_div_cosh, sinh_artanh hx, cosh_artanh hx, div_div_div_cancel_right₀, div_one]
  apply sqrt_ne_zero'.mpr
  rw [show 1 - x ^ 2 = (1 + x) * (1 - x) by ring]
  exact mul_pos (neg_lt_iff_pos_add'.mp hx.1) (sub_pos.mpr hx.2)

theorem tanh_lt_one (x : ℝ) : tanh x < 1 := by
  rw [tanh_eq]
  field_simp
  suffices 0 < rexp (-x) by linarith
  positivity

theorem neg_one_lt_tanh (x : ℝ) : -1 < tanh x := by
  rw [tanh_eq]
  field_simp
  suffices 0 < rexp x by linarith
  positivity

/-- `artanh` is the left inverse of `tanh`. -/
theorem artanh_tanh (x : ℝ) : artanh (tanh x) = x := by
  rw [artanh, ← exp_eq_exp, exp_log, ← sq_eq_sq₀, sq_sqrt, tanh_eq, exp_neg]
  · field
  · exact le_of_lt <| div_pos
      (neg_lt_iff_pos_add'.mp (neg_one_lt_tanh x)) (sub_pos.mpr (tanh_lt_one x))
  · positivity
  · positivity
  · exact sqrt_pos_of_pos <| div_pos
      (neg_lt_iff_pos_add'.mp (neg_one_lt_tanh x)) (sub_pos.mpr (tanh_lt_one x))

/-- `Real.tanh` as a `PartialEquiv`. -/
def tanhPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := tanh
  invFun := artanh
  source := univ
  target := Ioo (-1 : ℝ) 1
  map_source' r _ := mem_Ioo.mpr ⟨neg_one_lt_tanh r, tanh_lt_one r⟩
  map_target' _ _ := trivial
  left_inv' r _ := artanh_tanh r
  right_inv' _ hr := tanh_artanh hr

end Real
