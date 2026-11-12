/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Norms on `ℝ` and `ℝ≥0`

We equip `ℝ`, `ℝ≥0`, and `ℝ≥0∞` with their natural norms / enorms.

## Tags

normed group
-/

public section


variable {E : Type*}

open Filter
open ENNReal Filter NNReal

namespace NNReal

instance : NNNorm ℝ≥0 where
  nnNorm x := x

@[simp] lemma nnNorm_eq_self (x : ℝ≥0) : ‖x‖₊ = x := rfl

@[deprecated (since := "2026-10-31")] alias nnnorm_eq_self := nnNorm_eq_self

@[simp] lemma eNorm_eq_coe (x : ℝ≥0) : ‖x‖ₑ = x := rfl

@[deprecated (since := "2026-11-06")] alias enorm_eq_coe := eNorm_eq_coe

end NNReal

instance : ENorm ℝ≥0∞ where
  eNorm x := x

@[simp] lemma eNorm_eq_self (x : ℝ≥0∞) : ‖x‖ₑ = x := rfl

@[deprecated (since := "2026-11-06")] alias enorm_eq_self := eNorm_eq_self

noncomputable instance : ENormedAddCommMonoid ℝ≥0∞ where
  continuous_eNorm := continuous_id
  eNorm_zero := by simp
  eNorm_eq_zero := by simp
  eNorm_add_le := by simp

namespace Real

variable {r : ℝ}

instance norm : Norm ℝ where
  norm r := |r|

@[simp]
theorem norm_eq_abs (r : ℝ) : ‖r‖ = |r| :=
  rfl

instance normedAddCommGroup : NormedAddCommGroup ℝ :=
  ⟨fun _r _y => by rw [Real.dist_eq, ← abs_neg, neg_sub, add_comm, sub_eq_add_neg, norm_eq_abs]⟩

theorem norm_of_nonneg (hr : 0 ≤ r) : ‖r‖ = r :=
  abs_of_nonneg hr

theorem norm_of_nonpos (hr : r ≤ 0) : ‖r‖ = -r :=
  abs_of_nonpos hr

theorem le_norm_self (r : ℝ) : r ≤ ‖r‖ :=
  le_abs_self r

lemma norm_natCast (n : ℕ) : ‖(n : ℝ)‖ = n := abs_of_nonneg n.cast_nonneg
@[simp 1100] lemma nnNorm_natCast (n : ℕ) : ‖(n : ℝ)‖₊ = n := NNReal.eq <| norm_natCast _
@[simp 1100] lemma eNorm_natCast (n : ℕ) : ‖(n : ℝ)‖ₑ = n := by simp [eNorm]

@[deprecated (since := "2026-10-31")] alias nnnorm_natCast := nnNorm_natCast
@[deprecated (since := "2026-11-06")] alias enorm_natCast := eNorm_natCast

@[simp 1100] lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℝ)‖ = ofNat(n) := norm_natCast n

@[simp 1100] lemma nnNorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℝ)‖₊ = ofNat(n) := nnNorm_natCast n

@[deprecated (since := "2026-10-31")] alias nnnorm_ofNat := nnNorm_ofNat

lemma norm_two : ‖(2 : ℝ)‖ = 2 := abs_of_pos zero_lt_two
lemma nnNorm_two : ‖(2 : ℝ)‖₊ = 2 := NNReal.eq <| by simp

@[deprecated (since := "2026-10-31")] alias nnnorm_two := nnNorm_two

@[simp 1100, norm_cast]
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℝ)‖ = q := norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
lemma nnNorm_nnRatCast (q : ℚ≥0) : ‖(q : ℝ)‖₊ = q := by
  simp [nnNorm]
  rfl

@[deprecated (since := "2026-10-31")] alias nnnorm_nnratCast := nnNorm_nnRatCast

theorem nnNorm_of_nonneg (hr : 0 ≤ r) : ‖r‖₊ = .mk r hr :=
  NNReal.eq <| norm_of_nonneg hr

@[deprecated (since := "2026-10-31")] alias nnnorm_of_nonneg := nnNorm_of_nonneg

lemma eNorm_of_nonneg (hr : 0 ≤ r) : ‖r‖ₑ = .ofReal r := by
  simp [eNorm, nnNorm_of_nonneg hr, ENNReal.ofReal, toNNReal, hr]

@[deprecated (since := "2026-11-06")] alias enorm_of_nonneg := eNorm_of_nonneg

lemma eNorm_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ := by
  simp [Real.eNorm_of_nonneg, ha]

@[deprecated (since := "2026-11-06")] alias enorm_ofReal_of_nonneg := eNorm_ofReal_of_nonneg

@[simp] lemma nnNorm_abs (r : ℝ) : ‖|r|‖₊ = ‖r‖₊ := by simp [nnNorm]
@[simp] lemma eNorm_abs (r : ℝ) : ‖|r|‖ₑ = ‖r‖ₑ := by simp [eNorm]

@[deprecated (since := "2026-10-31")] alias nnnorm_abs := nnNorm_abs
@[deprecated (since := "2026-11-06")] alias enorm_abs := eNorm_abs

theorem eNorm_eq_ofReal (hr : 0 ≤ r) : ‖r‖ₑ = .ofReal r := by
  rw [← ofReal_norm, norm_of_nonneg hr]

@[deprecated (since := "2026-11-06")] alias enorm_eq_ofReal := eNorm_eq_ofReal

@[simp] lemma eNorm_toReal {a : ℝ≥0∞} (ha : a ≠ ∞) : ‖a.toReal‖ₑ = a := by
  simp [eNorm_eq_ofReal, ha]

@[deprecated (since := "2026-11-06")] alias enorm_toReal := eNorm_toReal

theorem eNorm_eq_ofReal_abs (r : ℝ) : ‖r‖ₑ = ENNReal.ofReal |r| := by
  rw [← eNorm_eq_ofReal (abs_nonneg _), eNorm_abs]

@[deprecated (since := "2026-11-06")] alias enorm_eq_ofReal_abs := eNorm_eq_ofReal_abs

theorem toNNReal_eq_nnNorm_of_nonneg (hr : 0 ≤ r) : r.toNNReal = ‖r‖₊ := by
  rw [Real.toNNReal_of_nonneg hr]
  congr
  rw [Real.norm_eq_abs r, abs_of_nonneg hr]

@[deprecated (since := "2026-10-31")]
alias toNNReal_eq_nnnorm_of_nonneg := toNNReal_eq_nnNorm_of_nonneg

theorem ofReal_le_eNorm (r : ℝ) : ENNReal.ofReal r ≤ ‖r‖ₑ := by
  rw [eNorm_eq_ofReal_abs]; gcongr; exact le_abs_self _

@[deprecated (since := "2026-11-06")] alias ofReal_le_enorm := ofReal_le_eNorm

end Real

section SeminormedCommGroup

variable [SeminormedCommGroup E] {a : E}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive (attr := simp high) norm_norm] -- Higher priority as a shortcut lemma.
lemma norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖ := Real.norm_of_nonneg (norm_nonneg' _)

@[to_additive (attr := simp) nnNorm_norm]
lemma nnNorm_norm' (x : E) : ‖‖x‖‖₊ = ‖x‖₊ := by simp [nnNorm]

@[to_additive (attr := deprecated (since := "2026-10-31")) nnnorm_norm]
alias nnnorm_norm' := nnNorm_norm'

@[to_additive (attr := simp) eNorm_norm]
lemma eNorm_norm' (x : E) : ‖‖x‖‖ₑ = ‖x‖ₑ := by simp [eNorm]

@[to_additive (attr := deprecated (since := "2026-11-06")) enorm_norm]
alias enorm_norm' := eNorm_norm'

lemma eNorm_eNorm {ε : Type*} [ENorm ε] (x : ε) : ‖‖x‖ₑ‖ₑ = ‖x‖ₑ := by simp [eNorm]

@[deprecated (since := "2026-11-06")] alias enorm_enorm := eNorm_eNorm

end SeminormedCommGroup

lemma tendsto_norm_atTop_atTop : Tendsto (norm : ℝ → ℝ) atTop atTop := tendsto_abs_atTop_atTop
