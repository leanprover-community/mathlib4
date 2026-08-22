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

/-- The value group with zero, as `WithZero` of its group of units.

Since `ValueGroup₀` is now a `SetLike` subobject of `Γ` rather than a `WithZero`, this is the
bridge that lets the `WithZero`-shaped constructions below still apply. -/
noncomputable def valueGroup₀OrderIsoWithZeroUnits :
    ValueGroup₀ (.ofClass v) ≃*o WithZero ↥(valueGroup (.ofClass v)) :=
  OrderMonoidIso.withZeroUnits.symm.trans
    (SubgroupWithZero.unitsOrderMonoidIso (valueGroup₀ (.ofClass v))).withZero

omit hv in
@[simp]
lemma valueGroup₀OrderIsoWithZeroUnits_symm_coe (u : ↥(valueGroup (.ofClass v))) :
    (valueGroup₀OrderIsoWithZeroUnits v).symm (u : WithZero ↥(valueGroup (.ofClass v))) =
      ⟨((u : Γˣ) : Γ), u.2⟩ := rfl

/-- An order-preserving isomorphism between the `ValueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
TODO: rename this into lowerCamelCase. -/
@[simps!]
noncomputable def valueGroup₀_equiv_withZeroMulInt : ValueGroup₀ (.ofClass v) ≃*o ℤᵐ⁰ :=
  (valueGroup₀OrderIsoWithZeroUnits v).trans <| {
  __ := MulEquiv.withZero (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm
  map_le_map_iff' {x y} := by
    rw [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).le_iff_le] }

lemma valueGroup₀_equiv_withZeroMulInt_apply_zero :
    valueGroup₀_equiv_withZeroMulInt v 0 = 0 := by simp

lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow (k : ℤ) :
    valueGroup₀_equiv_withZeroMulInt v (hv.generator₀ ^ k) = WithZero.exp (- k) := by
  have key : valueGroup₀OrderIsoWithZeroUnits v hv.generator₀ =
      (hv.generator' : WithZero ↥(valueGroup (.ofClass v))) := by
    conv_rhs => rw [← (valueGroup₀OrderIsoWithZeroUnits v).apply_symm_apply
      (hv.generator' : WithZero ↥(valueGroup (.ofClass v)))]
    rw [valueGroup₀OrderIsoWithZeroUnits_symm_coe]
    rfl
  simp [valueGroup₀_equiv_withZeroMulInt, key, WithZero.exp,
    ← mulintEquivOfZPowersEqTop_symm_apply_zpow
      (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)]

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
