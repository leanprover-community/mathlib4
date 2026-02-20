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

@[expose] public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

namespace NNReal

instance : NNNorm ℝ≥0 where
  nnnorm x := x

@[simp] lemma nnnorm_eq_self (x : ℝ≥0) : ‖x‖₊ = x := rfl

end NNReal

instance : ENorm ℝ≥0∞ where
  enorm x := x

@[simp] lemma enorm_eq_self (x : ℝ≥0∞) : ‖x‖ₑ = x := rfl

instance : ENormedAddCommMonoid ℝ≥0∞ where
  continuous_enorm := continuous_id
  enorm_zero := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp

namespace Real

variable {r : ℝ}

instance norm : Norm ℝ where
  norm r := |r|

@[simp]
theorem norm_eq_abs (r : ℝ) : ‖r‖ = |r| :=
  rfl

instance normedAddCommGroup : NormedAddCommGroup ℝ :=
  ⟨fun _r _y => rfl⟩

theorem norm_of_nonneg (hr : 0 ≤ r) : ‖r‖ = r :=
  abs_of_nonneg hr

theorem norm_of_nonpos (hr : r ≤ 0) : ‖r‖ = -r :=
  abs_of_nonpos hr

theorem le_norm_self (r : ℝ) : r ≤ ‖r‖ :=
  le_abs_self r

lemma norm_natCast (n : ℕ) : ‖(n : ℝ)‖ = n := abs_of_nonneg n.cast_nonneg
@[simp 1100] lemma nnnorm_natCast (n : ℕ) : ‖(n : ℝ)‖₊ = n := NNReal.eq <| norm_natCast _
@[simp 1100] lemma enorm_natCast (n : ℕ) : ‖(n : ℝ)‖ₑ = n := by simp [enorm]

@[simp 1100] lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℝ)‖ = ofNat(n) := norm_natCast n

@[simp 1100] lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℝ)‖₊ = ofNat(n) := nnnorm_natCast n

lemma norm_two : ‖(2 : ℝ)‖ = 2 := abs_of_pos zero_lt_two
lemma nnnorm_two : ‖(2 : ℝ)‖₊ = 2 := NNReal.eq <| by simp

@[simp 1100, norm_cast]
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℝ)‖ = q := norm_of_nonneg q.cast_nonneg

set_option backward.isDefEq.respectTransparency false in
@[simp 1100, norm_cast]
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : ℝ)‖₊ = q := by simp [nnnorm, -norm_eq_abs]

theorem nnnorm_of_nonneg (hr : 0 ≤ r) : ‖r‖₊ = ⟨r, hr⟩ :=
  NNReal.eq <| norm_of_nonneg hr

lemma enorm_of_nonneg (hr : 0 ≤ r) : ‖r‖ₑ = .ofReal r := by
  simp [enorm, nnnorm_of_nonneg hr, ENNReal.ofReal, toNNReal, hr]

lemma enorm_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ := by
  simp [Real.enorm_of_nonneg, ha]

@[simp] lemma nnnorm_abs (r : ℝ) : ‖|r|‖₊ = ‖r‖₊ := by simp [nnnorm]
@[simp] lemma enorm_abs (r : ℝ) : ‖|r|‖ₑ = ‖r‖ₑ := by simp [enorm]

theorem enorm_eq_ofReal (hr : 0 ≤ r) : ‖r‖ₑ = .ofReal r := by
  rw [← ofReal_norm_eq_enorm, norm_of_nonneg hr]

theorem enorm_eq_ofReal_abs (r : ℝ) : ‖r‖ₑ = ENNReal.ofReal |r| := by
  rw [← enorm_eq_ofReal (abs_nonneg _), enorm_abs]

theorem toNNReal_eq_nnnorm_of_nonneg (hr : 0 ≤ r) : r.toNNReal = ‖r‖₊ := by
  rw [Real.toNNReal_of_nonneg hr]
  congr
  rw [Real.norm_eq_abs r, abs_of_nonneg hr]

theorem ofReal_le_enorm (r : ℝ) : ENNReal.ofReal r ≤ ‖r‖ₑ := by
  rw [enorm_eq_ofReal_abs]; gcongr; exact le_abs_self _

end Real

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive (attr := simp high) norm_norm] -- Higher priority as a shortcut lemma.
lemma norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖ := Real.norm_of_nonneg (norm_nonneg' _)

@[to_additive (attr := simp) nnnorm_norm]
lemma nnnorm_norm' (x : E) : ‖‖x‖‖₊ = ‖x‖₊ := by simp [nnnorm]

@[to_additive (attr := simp) enorm_norm]
lemma enorm_norm' (x : E) : ‖‖x‖‖ₑ = ‖x‖ₑ := by simp [enorm]

lemma enorm_enorm {ε : Type*} [ENorm ε] (x : ε) : ‖‖x‖ₑ‖ₑ = ‖x‖ₑ := by simp [enorm]

end SeminormedCommGroup

lemma tendsto_norm_atTop_atTop : Tendsto (norm : ℝ → ℝ) atTop atTop := tendsto_abs_atTop_atTop
