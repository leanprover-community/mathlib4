/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Reduction of Weierstrass curves over local fields

This file defines reduction of Weierstrass curves over local fields, or more generally,
fraction fields of discrete valuation rings.

## Main definitions

* TODO

## Main statements

* TODO

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, minimal weierstrass equation, reduction
-/

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

section Minimal

open IsDedekindDomain.HeightOneSpectrum
open IsDiscreteValuationRing

class IsIntegralWeierstrassEquation (W : WeierstrassCurve K) : Prop where
  integral : ∃ W_int : WeierstrassCurve R, W = W_int.baseChange K

noncomputable abbrev valuation_fractionRing := valuation K (maximalIdeal R)

lemma isIntegralWeierstrassEquation_of_val_le_one {W : WeierstrassCurve K}
    (h₁ : (valuation_fractionRing R) W.a₁ ≤ 1)
    (h₂ : (valuation_fractionRing R) W.a₂ ≤ 1)
    (h₃ : (valuation_fractionRing R) W.a₃ ≤ 1)
    (h₄ : (valuation_fractionRing R) W.a₄ ≤ 1)
    (h₆ : (valuation_fractionRing R) W.a₆ ≤ 1) :
    IsIntegralWeierstrassEquation R W := by
  use ⟨ (exists_lift_of_le_one h₁).choose,
      (exists_lift_of_le_one h₂).choose,
      (exists_lift_of_le_one h₃).choose,
      (exists_lift_of_le_one h₄).choose,
      (exists_lift_of_le_one h₆).choose ⟩
  ext
  all_goals
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
    apply (exists_lift_of_le_one _).choose_spec.symm
    assumption

theorem exists_integralWeierstrassEquation (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsIntegralWeierstrassEquation R (C • W) := by
  obtain ⟨ π, hπ ⟩ := valuation_exists_uniformizer K (maximalIdeal R)
  have isUnit_π : IsUnit π :=
    IsUnit.mk0 π ((Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hπ WithZero.coe_ne_zero))
  /- have val_π_zpow (n : ℤ) :
      (valuation_fractionRing R) ((isUnit_π.unit : K) ^ n) =  Multiplicative.ofAdd (- (n : ℤ)) := by
    simp only [IsUnit.unit_spec, map_zpow₀, hπ, Int.reduceNeg, ofAdd_neg, WithZero.coe_inv,
      inv_zpow', zpow_neg, inv_inj]
    apply WithZero.coe_inj.mpr
    rw [← ofAdd_zsmul]
    apply (Equiv.apply_eq_iff_eq Multiplicative.ofAdd).mpr
    exact zsmul_int_one n -/
  let v₁ := (valuation_fractionRing R) W.a₁
  let v₂ := (valuation_fractionRing R) W.a₂
  let v₃ := (valuation_fractionRing R) W.a₃
  let v₄ := (valuation_fractionRing R) W.a₄
  let v₆ := (valuation_fractionRing R) W.a₆
  let large := max 1 (max v₁ (max v₂ (max v₃ (max v₄ v₆))))
  have zero_lt_large : 0 < large := by calc
    0 < 1 := zero_lt_one
    1 ≤ large := le_max_left 1 _
  let largeZ : ℤ := WithZero.unzero (zero_lt_iff.mp zero_lt_large)
  use ⟨ isUnit_π.unit ^ (- largeZ) , 0 , 0 , 0 ⟩
  apply isIntegralWeierstrassEquation_of_val_le_one R
  all_goals
    simp only [zpow_neg, variableChange_def, inv_inv, Units.val_zpow_eq_zpow_val, IsUnit.unit_spec,
      mul_zero, add_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, map_mul, map_pow, map_zpow₀]
    rw [hπ]; simp only [Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, inv_zpow', zpow_neg, inv_pow]
    refine inv_mul_le_one_of_le₀ ?_ zero_le'
  any_goals rw [← WithZero.coe_zpow, ← ofAdd_zsmul, zsmul_int_one];
  any_goals rw [← WithZero.coe_pow, ← ofAdd_nsmul]; simp only [Int.nsmul_eq_mul, Nat.cast_ofNat]
  all_goals
    refine (WithZero.unzero_le_unzero ?_ ?_).mp ?_

  all_goals sorry

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma Δ_integral_of_isIntegralWeierstrassEquation {W : WeierstrassCurve K}
    (hW : IsIntegralWeierstrassEquation R W) :
    ∃ r : R, (algebraMap R K) r = W.Δ := by
  obtain ⟨ W_int, hW_int ⟩ := hW.integral
  use W_int.Δ
  rw[hW_int, map_Δ]

lemma val_Δ_le_one_of_isIntegralWeierstrassEquation {W : WeierstrassCurve K}
    (hW : IsIntegralWeierstrassEquation R W) :
    (valuation_fractionRing R) W.Δ ≤ 1 := by
  obtain ⟨ r, hr ⟩ := Δ_integral_of_isIntegralWeierstrassEquation R hW
  rw[← hr]
  exact valuation_le_one (maximalIdeal R) r

class IsMinimalWeierstrassEquation (W : WeierstrassCurve K) : Prop where
  val_Δ_minimal :
    MinimalFor
      (fun (C : VariableChange K) => IsIntegralWeierstrassEquation R (C • W))
      (fun (C : VariableChange K) =>
        addVal R ((algebraMap R K).toFun.invFun (C • W).Δ))
      (1 : VariableChange K)

omit [IsFractionRing R K] in
lemma isIntegralWeierstrassEquation_of_isMinimalWeierstrassEquation
    {W : WeierstrassCurve K} (hW : IsMinimalWeierstrassEquation R W) :
    IsIntegralWeierstrassEquation R W := by simpa using hW.val_Δ_minimal.1

theorem exists_minimalWeierstrassEquation (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsMinimalWeierstrassEquation R (C • W) := by
  obtain ⟨ C , hC ⟩ := exists_minimalFor_of_wellFoundedLT
    (fun (C : VariableChange K) => IsIntegralWeierstrassEquation R (C • W))
    (fun (C : VariableChange K) =>
      addVal R ((algebraMap R K).toFun.invFun (C • W).Δ))
    (exists_integralWeierstrassEquation R W)
  use C
  refine { val_Δ_minimal := ?_ }
  constructor
  · simp only [one_smul]; exact hC.1
  intro j hj; rw[← smul_assoc] at hj
  let h := hC.2 hj
  simp_all only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, one_smul]
  rw[← smul_assoc]
  exact h

end Minimal

section Reduction

open IsLocalRing

noncomputable def reduction_minimalWeierstrassEquation {W : WeierstrassCurve K}
    (hW : IsMinimalWeierstrassEquation R W) :
    WeierstrassCurve (ResidueField R) :=
  (isIntegralWeierstrassEquation_of_isMinimalWeierstrassEquation R hW).integral.choose.map
    (residue R)

noncomputable def reduction (W : WeierstrassCurve K) :
    WeierstrassCurve (ResidueField R) :=
  reduction_minimalWeierstrassEquation R (exists_minimalWeierstrassEquation R W).choose_spec

end Reduction

end WeierstrassCurve
