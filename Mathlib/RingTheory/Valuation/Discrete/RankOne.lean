/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Data.Int.WithZero
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Discrete valuations have rank one

## Main Definitions and Results
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

/-- An order-preserving isomorphism between the `ValueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
TODO: rename this into lowerCamelCase. -/
@[simps!]
noncomputable def valueGroup₀_equiv_withZeroMulInt : v.ValueGroup₀ ≃*o ℤᵐ⁰ where
  __ := MulEquiv.withZero (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm
  map_le_map_iff' {x y} := by
    rw [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).le_iff_le]

lemma valueGroup₀_equiv_withZeroMulInt_apply_zero :
    valueGroup₀_equiv_withZeroMulInt v 0 = 0 := by simp

lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow (k : ℤ) :
    valueGroup₀_equiv_withZeroMulInt v (hv.generator' ^ k) = WithZero.exp (- k) := by
  simp [WithZero.exp, ← mulintEquivOfZPowersEqTop_symm_apply_zpow
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)]

lemma valueGroup₀_equiv_withZeroMulInt_strictMono :
    StrictMono (valueGroup₀_equiv_withZeroMulInt v) := by
  intro x y hxy
  rwa [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).lt_iff_lt]

/-- A discrete valuation has rank one. -/
@[instance_reducible]
noncomputable def rankOne {e : ℝ≥0} (he : 1 < e) : v.RankOne where
  hom' := (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp (valueGroup₀_equiv_withZeroMulInt v)
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

lemma rankOne_hom_eq {e : ℝ≥0} (he : 1 < e) :
    (hv.rankOne v he).hom =
      (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp (valueGroup₀_equiv_withZeroMulInt v) :=
  rfl

end LinearOrderedCommGroupWithZero

section WithZeroMulInt

variable {v : Valuation R ℤᵐ⁰} [hv : v.IsRankOneDiscrete]

lemma valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (hsurj : Function.Surjective v)
    (x : R) : (valueGroup₀_equiv_withZeroMulInt v) (v.restrict x) = v x := by
  simp only [Valuation.restrict_def, ValueGroup₀.restrict₀_apply,
    valueGroup₀_equiv_withZeroMulInt_apply]
  split_ifs with h0 <;>
  simp only [coe_toMonoidWithZeroHom] at h0
  · simp [h0]
  · rw [WithZero.map'_coe, ← coe_unzero h0, WithZero.coe_inj,
    ← (MulEquiv.injective (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top))).eq_iff]
    ext
    simp [generator', generator_eq_exp_neg_one_of_surjective hsurj, toAdd_unzero_eq_log h0,
      exp_log h0]

lemma valueGroup₀_equiv_withZeroMulInt_restrict_zpow_eq {v : Valuation R ℤᵐ⁰}
    [hv : IsRankOneDiscrete v] (hv0 : ∀ x ≠ 0, v x ≠ 0) (x : R) :
    ((hv.valueGroup₀_equiv_withZeroMulInt v) (v.restrict x)) ^ (- logEquiv hv.generator) = v x := by
  by_cases hx : x = 0
  · simp only [hx, map_zero, logEquiv_apply, zpow_neg, inv_eq_zero]
    rw [zero_zpow]
    simp [ne_eq, ← exp_inj (y := (0 : ℤ)), (IsRankOneDiscrete.generator_lt_one v).ne]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (hv.generator' : ValueGroup₀ (v : R →*₀ ℤᵐ⁰))⁻¹ ^ c = v.restrict x := by
    rw [restrict_def, ValueGroup₀.restrict₀_of_ne_zero (by simp [hv0, hx])]
    simp [← coe_inv, ← WithZero.coe_zpow, WithZero.coe_inj,-inv_zpow', ← Subgroup.mem_zpowers_iff,
       hv.generator'_zpowers_eq_top, Subgroup.mem_top]
  have hc' : hv.generator ^ (- c) = v x := by
    simp [← v.embedding_restrict, ← hc, hv.embedding_generator']
  rw [restrict_def, ValueGroup₀.restrict₀_of_ne_zero (by simp [hv0, hx])] at hc ⊢
  simp only [← coe_inv, ← WithZero.coe_zpow, WithZero.coe_inj] at hc
  rw [IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply, map'_coe, MonoidHom.coe_ofClass]
  have hg' : Subgroup.zpowers (hv.generator' v)⁻¹ = ⊤ := by
    simp [Subgroup.zpowers_inv, IsRankOneDiscrete.generator'_zpowers_eq_top v]
  rw [← hc, mulintEquivOfZPowersEqTop_symm_apply_zpow hg' c]
  simp only [logEquiv_apply, ← hc', zpow_neg]
  nth_rw 2 [← exp_log (hv.generator_ne_zero v)]
  simp [exp, ← WithZero.coe_zpow, ← Int.ofAdd_mul, mul_comm c]

end WithZeroMulInt

end Ring

/-- Absolute value corresponding to a discrete valuation. -/
@[simps!]
noncomputable def absoluteValue {K : Type*} [DivisionRing K] {v : Valuation K Γ}
    [v.IsRankOneDiscrete] {e : ℝ≥0} (he : 1 < e) : AbsoluteValue K ℝ :=
  let : v.RankOne := IsRankOneDiscrete.rankOne v he
  v.absoluteValue

end Valuation.IsRankOneDiscrete

open WithZero MonoidWithZeroHom ValueGroup₀ in
lemma Valuation.nonempty_valueGroup₀_orderMonoidIso_withZeroMulInt_iff {Γ R : Type*}
    [LinearOrderedCommGroupWithZero Γ] [Ring R] (v : Valuation R Γ) :
    Nonempty (ValueGroup₀ (v : R →*₀ Γ) ≃*o ℤᵐ⁰) ↔ IsRankOneDiscrete v := by
  refine ⟨fun ⟨f⟩ ↦ ?_, fun hv ↦ ⟨(hv.valueGroup₀_equiv_withZeroMulInt v).toMulEquiv,
      (hv.valueGroup₀_equiv_withZeroMulInt_strictMono v).le_iff_le⟩⟩
  have hf : IsUnit (f.symm (WithZero.exp (-1))) := by simp
  refine ⟨Units.map embedding.toMonoidHom hf.unit, ?_, ?_⟩
  · ext γ
    refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun h ↦ ?_⟩
    · wlog hk0 : 0 ≤ k
      · rw [← Subgroup.inv_mem_iff]
        exact this _ ⟨f⟩ f hf γ⁻¹ ⟨-k, (by simp [← hk])⟩ (-k) (by simp [← hk]) (by linarith)
      have h0 : f.symm (WithZero.exp (-1)) ≠ 0 := by simp
      obtain ⟨r, s, hr0, hs0, hrs⟩ :=
        Or.resolve_left (zero_or_exists_mk (v : R →*₀ Γ) (f.symm (WithZero.exp (-1)))) h0
      rw [mem_valueGroup_iff_of_comm]
      refine ⟨r ^ k.natAbs, ?_,  s ^ k.natAbs, ?_⟩
      · simp only [coe_toMonoidWithZeroHom, ne_eq] at hr0
        simp [hr0]
      · simp only [coe_toMonoidWithZeroHom, ne_eq] at hr0 hs0
        simp only [← hk, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec,
          ← Int.reduceNeg, hrs, map_pow, ← zpow_natCast, Nat.cast_natAbs,
          abs_eq_self.mpr hk0, Int.cast_eq, MonoidHom.coe_mk, ZeroHom.toFun_eq_coe, toZeroHom_coe,
          OneHom.coe_mk, ← mul_zpow]
        rw [← embedding_restrict₀ r, ← embedding_restrict₀ s, valueGroup.mk, ← map_mul]
        simp [restrict₀, hr0, hs0,← WithZero.coe_mul]
    · obtain ⟨a, ha, b, hb, hab⟩ := (mem_valueGroup_iff_of_comm' (v : R →*₀ Γ)).mp h
      set g := f ((restrict₀ (v : R →*₀ Γ) b)⁻¹ * (restrict₀ (v : R →*₀ Γ) a))
      simp only [coe_toMonoidWithZeroHom, ne_eq] at ha hb hab
      have hg : g ≠ 0 := by simp [g, ha, hb]
      use log g
      ext
      simp only [Int.reduceNeg, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec,
        MonoidHom.coe_mk, ZeroHom.toFun_eq_coe, toZeroHom_coe, OneHom.coe_mk, ← map_zpow₀,
        ← exp_zsmul, Int.zsmul_eq_mul, mul_neg, mul_one]
      rw [← mul_right_inj' ha, hab, neg_eq_neg_one_mul, ← smul_eq_mul (-1), exp_zsmul, exp_log hg]
      simp [ha, g]
  · simp only [ ← Units.val_lt_val, Units.coe_map,IsUnit.unit_spec, MonoidHom.coe_mk,
      ZeroHom.toFun_eq_coe, toZeroHom_coe, OneHom.coe_mk, Units.val_one]
    rw [← map_one (embedding (f := (v : R →*₀ Γ))), embedding_strictMono.lt_iff_lt]
    exact (OrderMonoidIso.symm_apply_lt f).mpr (by simp [← WithZero.exp_zero])
