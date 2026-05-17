/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.RankOne

/-!
# Discrete valuations have rank one

## Main Definitions and Results
* `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range` : the generator of
a discrete valuation in `ℤᵐ⁰` that contains `exp (-1)` in its range is equal to `exp (-1)`.
* `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective` : the generator of
a surjective discrete valuation in `ℤᵐ⁰` is equal to `exp (-1)`.
* `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt` : the order-preserving isomorphism
  between the `ValueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
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

/-- An order-preserving isomorphism between the `ValueGroup₀` of a discrete valuation and `ℤᵐ⁰`. -/
@[simps!]
noncomputable def valueGroup₀_equiv_withZeroMulInt : (ValueGroup₀ v) ≃* ℤᵐ⁰ :=
  MulEquiv.withZero (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm

lemma valueGroup₀_equiv_withZeroMulInt_apply_zero :
    valueGroup₀_equiv_withZeroMulInt v 0 = 0 := by simp

lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow (k : ℤ) :
    valueGroup₀_equiv_withZeroMulInt v (hv.generator' ^ k) = WithZero.exp (- k) := by
  simp only [map_zpow₀, valueGroup₀_equiv_withZeroMulInt_apply, WithZero.map'_coe,
    MonoidHom.coe_coe]
  rw [← WithZero.coe_zpow, WithZero.exp, WithZero.coe_inj, ← map_zpow]
  simp [← mulintEquivOfZPowersEqTop_symm_apply_zpow
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)]

lemma valueGroup₀_equiv_withZeroMulInt_strictMono :
    StrictMono (valueGroup₀_equiv_withZeroMulInt v) := by
  intro x y hxy
  simp only [valueGroup₀_equiv_withZeroMulInt, MulEquiv.withZero_apply_apply]
  rwa [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).lt_iff_lt]

/-- A discrete valuation has rank one. -/
@[implicit_reducible]
noncomputable def rankOne {e : ℝ≥0} (he : 1 < e) : v.RankOne where
  hom' := (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp (valueGroup₀_equiv_withZeroMulInt v)
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

end LinearOrderedCommGroupWithZero

section WithZeroMulInt

variable {v : Valuation R ℤᵐ⁰} [hv : v.IsRankOneDiscrete]

open LinearOrderedCommGroup in
/--
The generator of a discrete valuation in `ℤᵐ⁰` that contains `exp (-1)` in its range
is equal to `exp (-1)`. -/
theorem generator_eq_exp_neg_one_of_mem_range (hπ : exp (-1) ∈ Set.range v) :
    hv.generator = Units.mk0 (exp (-1 : ℤ) : ℤᵐ⁰) (by simp) := by
  rw [← Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator]
  suffices Units.mk0 (exp (-1)) (by simp) = (Subgroup.genLTOne (valueGroup v)) by simp [← this]
  apply LinearOrderedCommGroup.Subgroup.genLTOne_unique
  · exact compareOfLessAndEq_eq_lt.mp rfl
  · ext n
    simp_all only [Int.reduceNeg, exp_neg, Subgroup.mem_zpowers_iff, mem_valueGroup_iff_of_comm,
      ne_eq]
    refine ⟨fun ⟨k, h⟩ ↦ ?_ , fun _ ↦ ⟨-WithZero.log n, by aesop⟩⟩
    rw [← h]
    have ⟨π, hπ⟩ := hπ
    cases k with
    | ofNat n => refine ⟨1, ?_, π ^ n, ?_⟩ <;> simp [hπ]
    | negSucc n => refine ⟨π ^ (n + 1), ?_, 1, ?_⟩ <;> simp [hπ, Int.negSucc_eq, mul_assoc]

/--
The generator of a surjective discrete valuation in `ℤᵐ⁰` is equal to `exp (-1)`. -/
lemma generator_eq_exp_neg_one_of_surjective (hsurj : Function.Surjective v) :
    hv.generator = Units.mk0 (exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
  generator_eq_exp_neg_one_of_mem_range (by aesop)

@[deprecated generator_eq_exp_neg_one_of_surjective (since := "2026-04-01")]
lemma generator_eq_neg_exp_one_of_surjective (hsurj : Function.Surjective v) :
    hv.generator = Units.mk0 (exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
  generator_eq_exp_neg_one_of_surjective hsurj

lemma valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (hsurj : Function.Surjective v)
    (x : R) : (valueGroup₀_equiv_withZeroMulInt v) (v.restrict x) = v x := by
  simp only [Valuation.restrict_def, ValueGroup₀.restrict₀_apply,
    valueGroup₀_equiv_withZeroMulInt_apply]
  split_ifs with h0
  · simp [h0]
  · simp only [WithZero.map'_coe, MonoidHom.coe_coe]
    conv_rhs => rw [← coe_unzero h0]
    rw [WithZero.coe_inj, ← (MulEquiv.injective (intEquivOfZPowersEqTop _
      (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top))).eq_iff,
      MulEquiv.apply_symm_apply]
    ext
    simp only [Units.val_mk0, intEquivOfZPowersEqTop_apply, inv_zpow', generator',
      SubgroupClass.coe_zpow]
    have hg : hv.generator = Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
      generator_eq_exp_neg_one_of_surjective hsurj
    rw [hg]
    conv_lhs => rw [← coe_unzero h0]
    simp only [coe_unzero, Int.reduceNeg, exp_neg, zpow_neg, Units.val_inv_eq_inv_val,
      Units.val_zpow_eq_zpow_val, Units.val_mk0, inv_zpow', ← exp_zsmul, Int.zsmul_eq_mul, mul_one,
      inv_inv]
    simp [WithZero.exp]

end WithZeroMulInt

end Ring

end Valuation.IsRankOneDiscrete
