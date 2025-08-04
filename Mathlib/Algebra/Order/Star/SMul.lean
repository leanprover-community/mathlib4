/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.NNReal.Star

/-!
# `StarOrderedRing` implies `OrderedSMul`

We show that `StarOrderedRing R` implies `OrderedSMul 𝕜 R` when `𝕜` is either `RCLike` or
`𝕜 = ℝ≥0`.
-/

open scoped ComplexOrder

namespace StarOrderedRing

section RCLike

variable {𝕜 R : Type*} [RCLike 𝕜] [NonUnitalRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] [Module 𝕜 R] [StarModule 𝕜 R]
    [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

open AddSubmonoid in
lemma smul_nonneg {c : 𝕜} {a : R} (hc : 0 ≤ c) (ha : 0 ≤ a) : 0 ≤ c • a := by
  rw [nonneg_iff] at ha
  induction ha using closure_induction with
  | mem x hx =>
      obtain ⟨rc, hrc₁, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp hc
      obtain ⟨z, rfl⟩ := hx
      let y := (Real.sqrt rc : 𝕜) • z
      have : (Real.sqrt rc : 𝕜) * Real.sqrt rc = rc := by exact_mod_cast Real.mul_self_sqrt hrc₁
      have hmain : (rc : 𝕜) • (star z * z) = star y * y := by
        simp [y, smul_mul_smul, this]
      rw [hmain]
      exact star_mul_self_nonneg y
  | one => simp
  | mul x y hx hy hx' hy' => simp [Left.add_nonneg hx' hy']

lemma smul_lt_smul_of_pos {a b : R} {c : 𝕜} (hab : a < b) (hc : 0 < c) : c • a < c • b :=
  have hab' : 0 < b - a := sub_pos_of_lt hab
  lt_of_sub_pos <| smul_sub c b a ▸
    lt_of_le_of_ne (smul_nonneg (le_of_lt hc) (le_of_lt hab'))
    (smul_ne_zero (ne_of_lt hc).symm (ne_of_lt hab').symm).symm

instance (priority := 100) toOrderedSMulRCLike : OrderedSMul 𝕜 R where
  smul_lt_smul_of_pos := smul_lt_smul_of_pos
  lt_of_smul_lt_smul_of_pos {a} {b} {c} hab hc := by
    have hc' : c⁻¹ * c = 1 := by grind
    have hmain : c⁻¹ • (c • a) < c⁻¹ • (c • b) := smul_lt_smul_of_pos hab (inv_pos_of_pos hc)
    simpa [smul_smul, hc'] using hmain

end RCLike

section NNReal
open scoped NNReal

variable {R : Type*} [NonUnitalRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] [Module ℝ≥0 R] [StarModule ℝ≥0 R]
    [IsScalarTower ℝ≥0 R R] [SMulCommClass ℝ≥0 R R]

open AddSubmonoid in
lemma smul_nnreal_nonneg {c : ℝ≥0} {a : R} (ha : 0 ≤ a) : 0 ≤ c • a := by
  rw [nonneg_iff] at ha
  induction ha using closure_induction with
  | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      let y := NNReal.sqrt c • z
      have hmain : c • (star z * z) = star y * y := by
        simp [y, smul_mul_smul, NNReal.mul_self_sqrt]
      rw [hmain]
      exact star_mul_self_nonneg y
  | one => simp
  | mul x y hx hy hx' hy' => simp [Left.add_nonneg hx' hy']

lemma smul_lt_smul_of_pos_nnreal {a b : R} {c : ℝ≥0} (hab : a < b) (hc : 0 < c) :
    c • a < c • b :=
  have hab' : 0 < b - a := sub_pos_of_lt hab
  lt_of_sub_pos <| smul_sub c b a ▸
    lt_of_le_of_ne (smul_nnreal_nonneg (le_of_lt hab'))
    (smul_ne_zero (ne_of_lt hc).symm (ne_of_lt hab').symm).symm

instance (priority := 100) toOrderedSMulNNReal : OrderedSMul ℝ≥0 R where
  smul_lt_smul_of_pos := smul_lt_smul_of_pos_nnreal
  lt_of_smul_lt_smul_of_pos {a} {b} {c} hab hc := by
    have hc' : c⁻¹ * c = 1 := inv_mul_cancel₀ (pos_iff_ne_zero.mp hc)
    have hmain : c⁻¹ • (c • a) < c⁻¹ • (c • b) := smul_lt_smul_of_pos_nnreal hab (inv_pos_of_pos hc)
    simpa [smul_smul, hc'] using hmain

end NNReal

end StarOrderedRing
