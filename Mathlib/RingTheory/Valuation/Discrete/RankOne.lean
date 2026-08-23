/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Data.Int.WithZero

/-!
# Discrete valuations have rank one

## Main Definitions and Results
* `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt` : the order-preserving isomorphism
  between the `valueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
* `Valuation.IsRankOneDiscrete.rankOne` : a discrete valuation has rank one.

## Tags
valuation, discrete, rank one
-/

@[expose] public section

namespace Valuation.IsRankOneDiscrete

open WithZero MonoidWithZeroHom NNReal WithZeroMulInt

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {R : Type*} [Ring R]

section LinearOrderedCommGroupWithZero

variable (v : Valuation R Γ) [hv : v.IsRankOneDiscrete]

lemma generator₀_pos : 0 < hv.generator₀ :=
  Subtype.coe_lt_coe.1 (by simp [coe_generator₀, zero_lt_iff, (generator v).ne_zero])

lemma generator₀_lt_one : hv.generator₀ < 1 := by
  rw [← Subtype.coe_lt_coe]
  simpa [coe_generator₀, ← Units.val_lt_val] using hv.generator_lt_one

lemma generator₀_zpowers₀_eq_top :
    SubgroupWithZero.zpowers₀ hv.generator₀ = ⊤ :=
  SubgroupWithZero.zpowers₀_coe_eq_top _ (by
    rw [coe_generator₀]; exact generator_zpowers₀_eq_valueGroup₀ v)

/-- An order-preserving isomorphism between the `valueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
TODO: rename this into lowerCamelCase. -/
noncomputable def valueGroup₀_equiv_withZeroMulInt : valueGroup₀ (.ofClass v) ≃*o ℤᵐ⁰ :=
  orderIsoWithZeroMulInt (generator₀_pos v) (generator₀_lt_one v) (generator₀_zpowers₀_eq_top v)

lemma valueGroup₀_equiv_withZeroMulInt_apply_zero :
    valueGroup₀_equiv_withZeroMulInt v 0 = 0 := map_zero _

lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow (k : ℤ) :
    valueGroup₀_equiv_withZeroMulInt v (hv.generator₀ ^ k) = WithZero.exp (- k) :=
  orderIsoWithZeroMulInt_zpow _ _ _ k

lemma valueGroup₀_equiv_withZeroMulInt_strictMono :
    StrictMono (valueGroup₀_equiv_withZeroMulInt v) :=
  (valueGroup₀_equiv_withZeroMulInt v).strictMono

/-- A discrete valuation has rank one. -/
@[instance_reducible]
noncomputable def rankOne {e : ℝ≥0} (he : 1 < e) : v.RankOne where
  hom' := (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp
      (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

end LinearOrderedCommGroupWithZero

section WithZeroMulInt

variable {v : Valuation R ℤᵐ⁰} [hv : v.IsRankOneDiscrete]

lemma valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (hsurj : Function.Surjective v)
    (x : R) : (valueGroup₀_equiv_withZeroMulInt v) (v.restrict x) = v x := by
  rcases eq_or_ne (v x) 0 with h0 | h0
  · rw [show v.restrict x = 0 from by simp [h0], map_zero, h0]
  · obtain ⟨k, hk⟩ := (SubgroupWithZero.mem_zpowers₀_iff_of_ne_zero h0).1
      (by rw [IsRankOneDiscrete.generator_zpowers₀_eq_valueGroup₀ v]; exact apply_mem_valueGroup₀ x)
    have hres : v.restrict x = hv.generator₀ ^ k := Subtype.ext hk.symm
    rw [hres, valueGroup₀_equiv_withZeroMulInt_apply_zpow, ← hk,
      IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective hsurj]
    simp [← WithZero.exp_zsmul]

end WithZeroMulInt

end Ring

end Valuation.IsRankOneDiscrete
