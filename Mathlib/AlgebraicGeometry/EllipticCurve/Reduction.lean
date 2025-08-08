/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Reduction of Weierstrass curves over local fields

This file defines reduction of Weierstrass curves over local fields, or more generally,
fraction fields of discrete valuation rings.

## Main definitions

* `IsIntegralWeierstrassEquation`: a predicate expressing that a given Weierstrass equation
  has integral coefficients.
* `IsMinimalWeierstrassEquation`: a predicate expressing that a given Weierstrass equation
  has minimal valuation of discriminant among all isomorphic integral Weierstrass equations.
* `reduction`: the reduction of a Weierstrass curve given by a minimal Weierstrass equation,
  which is a Weierstrass curve over the residue field.

## Main statements

* `exists_integralWeierstrassEquation`: any Weierstrass curve is isomorphic to one given by
  an integral Weierstrass equation.
* `exists_minimalWeierstrassEquation`: any Weierstrass curve is isomorphic to one given by
  a minimal Weierstrass equation.

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

/-- A Weierstrass equation over the fraction field `K` is integral if
it has coefficients in the DVR `R`. -/
class IsIntegralWeierstrassEquation (W : WeierstrassCurve K) : Prop where
  integral : ∃ W_int : WeierstrassCurve R, W = W_int.baseChange K

lemma isIntegralWeierstrassEquation_of_val_le_one {W : WeierstrassCurve K}
    (h₁ : valuation K (maximalIdeal R) W.a₁ ≤ 1)
    (h₂ : valuation K (maximalIdeal R) W.a₂ ≤ 1)
    (h₃ : valuation K (maximalIdeal R) W.a₃ ≤ 1)
    (h₄ : valuation K (maximalIdeal R) W.a₄ ≤ 1)
    (h₆ : valuation K (maximalIdeal R) W.a₆ ≤ 1) :
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
  let l := [(valuation K (maximalIdeal R) W.a₁),
    (valuation K (maximalIdeal R) W.a₂),
    (valuation K (maximalIdeal R) W.a₃),
    (valuation K (maximalIdeal R) W.a₄),
    (valuation K (maximalIdeal R) W.a₆)]
  let lmax : WithZero (Multiplicative ℤ) :=
    l.maximum_of_length_pos (List.length_pos_of_mem (l.get_mem (0 : Fin 5)))
  have hlmax : ∀ v ∈ l, v ≤ lmax := fun v hv ↦
      List.le_maximum_of_length_pos_of_mem hv (List.length_pos_of_mem (l.get_mem (0 : Fin 5)))
  let lmaxZ : ℤ := if h : lmax = 0 then 0 else max 0 (WithZero.unzero h)
  have zero_le_lmaxZ : 0 ≤ lmaxZ := by unfold lmaxZ; by_cases h : lmax = 0; all_goals simp [h]
  have lmax_le_lmaxZ : lmax ≤ Multiplicative.ofAdd lmaxZ := by
    unfold lmaxZ; by_cases h : lmax = 0
    all_goals simp only [h, ↓reduceDIte, ofAdd_zero, WithZero.coe_one, zero_le']
    conv_lhs => rw [← WithZero.coe_unzero h]
    simp only [WithZero.coe_le_coe]
    calc
      WithZero.unzero h = Multiplicative.ofAdd (WithZero.unzero h) := rfl
      Multiplicative.ofAdd (WithZero.unzero h) ≤
      Multiplicative.ofAdd (max (0 : ℤ) (WithZero.unzero h)) := by
        apply Multiplicative.ofAdd_le.mpr; simp
  have h (n : ℕ) (hn : 1 ≤ n) :
      ∀ v ∈ l, v ≤ (Multiplicative.ofAdd (n * lmaxZ)) :=
    fun v hv => calc
      v ≤ lmax := hlmax v hv
      lmax ≤ Multiplicative.ofAdd lmaxZ := lmax_le_lmaxZ
      (((Multiplicative.ofAdd lmaxZ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
      (((Multiplicative.ofAdd (n * lmaxZ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
        convert Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hn) zero_le_lmaxZ
        simp

  obtain ⟨ π, hπ ⟩ := valuation_exists_uniformizer K (maximalIdeal R)
  have isUnit_π : IsUnit π :=
    IsUnit.mk0 π ((Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hπ WithZero.coe_ne_zero))
  use ⟨ isUnit_π.unit ^ (-lmaxZ) , 0 , 0 , 0 ⟩

  apply isIntegralWeierstrassEquation_of_val_le_one R
  any_goals
    simp only [zpow_neg, variableChange_def, inv_inv, Units.val_zpow_eq_zpow_val, IsUnit.unit_spec,
      mul_zero, add_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, map_mul, map_pow, map_zpow₀]
    rw [hπ]; simp only [Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, inv_zpow', zpow_neg, inv_pow]
    refine inv_mul_le_one_of_le₀ ?_ zero_le'
  any_goals rw [← WithZero.coe_zpow, ← ofAdd_zsmul, zsmul_int_one];
  any_goals rw [← WithZero.coe_pow, ← ofAdd_nsmul]; simp only [Int.nsmul_eq_mul, Nat.cast_ofNat]
  any_goals convert h _ _ _ _
  swap
  · exact 1
  · simp
  any_goals linarith
  · apply l.get_mem (0 : Fin 5)
  · apply l.get_mem (1 : Fin 5)
  · apply l.get_mem (2 : Fin 5)
  · apply l.get_mem (3 : Fin 5)
  · apply l.get_mem (4 : Fin 5)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma Δ_integral_of_isIntegralWeierstrassEquation (W : WeierstrassCurve K)
    [IsIntegralWeierstrassEquation R W] :
    ∃ r : R, (algebraMap R K) r = W.Δ := by
  obtain ⟨W_int, hW_int⟩ : ∃ W_int : WeierstrassCurve R, W = W_int.baseChange K :=
    IsIntegralWeierstrassEquation.integral
  use W_int.Δ
  rw [hW_int, map_Δ]

/-- A Weierstrass equation over the fraction field `K` is minimal if the valuation
of its discriminant is minimal among all isomorphic integral Weierstrass equations. -/
class IsMinimalWeierstrassEquation (W : WeierstrassCurve K) : Prop where
  val_Δ_minimal :
    MinimalFor
      (fun (C : VariableChange K) => IsIntegralWeierstrassEquation R (C • W))
      (fun (C : VariableChange K) => addVal R ((algebraMap R K).toFun.invFun (C • W).Δ))
      (1 : VariableChange K)

omit [IsFractionRing R K] in
instance {W : WeierstrassCurve K} [IsMinimalWeierstrassEquation R W] :
    IsIntegralWeierstrassEquation R W := by simpa using IsMinimalWeierstrassEquation.val_Δ_minimal.1

theorem exists_minimalWeierstrassEquation (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsMinimalWeierstrassEquation R (C • W) := by
  obtain ⟨ C , hC ⟩ := exists_minimalFor_of_wellFoundedLT
    (fun (C : VariableChange K) ↦ IsIntegralWeierstrassEquation R (C • W))
    (fun (C : VariableChange K) ↦ addVal R ((algebraMap R K).toFun.invFun (C • W).Δ))
    (exists_integralWeierstrassEquation R W)
  use C
  refine { val_Δ_minimal := ?_ }
  constructor
  · simp only [one_smul]; exact hC.1
  intro j hj; rw [← smul_assoc] at hj
  let h := hC.2 hj
  simp_all only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, one_smul]
  rw [← smul_assoc]
  exact h

end Minimal

section Reduction

open IsLocalRing

/-- The reduction of a Weierstrass curve over `K` given by a minimal Weierstrass equation,
which is a Weierstrass curve over the residue field of `R`. -/
noncomputable def reduction (W : WeierstrassCurve K) [IsMinimalWeierstrassEquation R W] :
    WeierstrassCurve (ResidueField R) :=
  letI hW : IsIntegralWeierstrassEquation R W := inferInstance
  hW.integral.choose.map (residue R)

end Reduction

end WeierstrassCurve
