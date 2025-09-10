/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Reduction of Weierstrass curves over local fields

This file defines reduction of Weierstrass curves over local fields, or more generally,
fraction fields of discrete valuation rings.

## Main definitions

* `IsIntegral`: a predicate expressing that a given Weierstrass equation
  has integral coefficients.
* `IsMinimal`: a predicate expressing that a given Weierstrass equation
  has minimal valuation of discriminant among all isomorphic integral Weierstrass equations.
* `reduction`: the reduction of a Weierstrass curve given by a minimal Weierstrass equation,
  which is a Weierstrass curve over the residue field.
* `IsGoodReduction`: a predicate expressing that a given minimal Weierstrass equation
  has valuation of its discriminant equal to zero.

## Main statements

* `exists_integral`: any Weierstrass curve is isomorphic to one given by
  an integral Weierstrass equation.
* `exists_minimal`: any Weierstrass curve is isomorphic to one given by
  a minimal Weierstrass equation.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, minimal weierstrass equation, reduction
-/

namespace WeierstrassCurve

section Integral

variable (R : Type*) [CommRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A Weierstrass equation over the fraction field `K` is integral if
it has coefficients in the ring `R`. -/
@[mk_iff]
class IsIntegral (W : WeierstrassCurve K) : Prop where
  integral : ∃ W_int : WeierstrassCurve R, W = W_int.baseChange K

def integralModel (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    WeierstrassCurve R :=
  hW.choose

  

omit [IsFractionRing R K] in
lemma isIntegral_of_exists_lift {W : WeierstrassCurve K}
    (h₁ : ∃ r₁, (algebraMap R K) r₁ = W.a₁)
    (h₂ : ∃ r₂, (algebraMap R K) r₂ = W.a₂)
    (h₃ : ∃ r₃, (algebraMap R K) r₃ = W.a₃)
    (h₄ : ∃ r₄, (algebraMap R K) r₄ = W.a₄)
    (h₆ : ∃ r₆, (algebraMap R K) r₆ = W.a₆) :
    IsIntegral R W := by
  use ⟨h₁.choose, h₂.choose, h₃.choose, h₄.choose, h₆.choose⟩
  ext
  all_goals simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  · apply h₁.choose_spec.symm
  · apply h₂.choose_spec.symm
  · apply h₃.choose_spec.symm
  · apply h₄.choose_spec.symm
  · apply h₆.choose_spec.symm

omit [IsFractionRing R K] in
lemma Δ_integral_of_isIntegral (W : WeierstrassCurve K) [IsIntegral R W] :
    ∃ r : R, algebraMap R K r = W.Δ := by
  obtain ⟨W_int, hW_int⟩ : ∃ W_int : WeierstrassCurve R, W = W_int.baseChange K :=
    IsIntegral.integral
  use W_int.Δ
  rw [hW_int, map_Δ]

lemma integral_Δ_eq_of_isIntegral (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    hW.integral.choose.Δ =
    (algebraMap R K).toFun.invFun W.Δ := by
  conv_rhs => simp [Function.invFun, Δ_integral_of_isIntegral R W]
  apply (@IsFractionRing.coe_inj R _ K _ _ _ _).mp
  unfold Algebra.cast
  rw [← map_Δ]
  conv_lhs => arg 1; equals W => apply hW.integral.choose_spec.symm
  rw [(Δ_integral_of_isIntegral R W).choose_spec]

variable [IsDomain R] [ValuationRing R]

open ValuationRing

theorem exists_integral (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsIntegral R (C • W) := by
  let l₀ := [W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  let l := l₀.map (fun a ↦ valuation R K a)
  let lmax : ValueGroup R K :=
    l.maximum_of_length_pos (by simp [l₀, l])
  have hlmax_mem : lmax ∈ l :=
    List.maximum_of_length_pos_mem (by simp [l₀, l])
  have hlmax : ∀ v ∈ l, v ≤ lmax := fun v hv ↦
    List.le_maximum_of_length_pos_of_mem hv (by simp [l₀, l])
  by_cases hlmax_le_1 : lmax ≤ 1
  · use ⟨1, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals
      apply (mem_integer_iff _ _ _).mp
      simp only [variableChange_def, inv_one, Units.val_one, mul_zero, add_zero, one_mul, one_pow,
        zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      apply (Valuation.mem_integer_iff _ _).mpr
      exact (hlmax _ (by simp [l₀, l])).trans hlmax_le_1
  · have hlmax_ge_1 : lmax ≥ 1 := le_of_not_ge hlmax_le_1
    have h : ∃ a : K, valuation R K a = lmax := by
      let i : ℕ := l.idxOf lmax
      have hi : i < l.length := List.idxOf_lt_length_of_mem hlmax_mem
      use l₀[i]
      have hi₁ : (valuation R K) l₀[i] = l[i] := by simp [l]
      simpa only [hi₁] using (List.getElem_idxOf hi)
    choose a ha using h
    have ha₀ : a ≠ 0 := by
      by_contra ha₀; simp only [ha₀, map_zero] at ha
      exact (ha ▸ hlmax_le_1) zero_le_one
    have isUnit_a : IsUnit a := IsUnit.mk0 a ha₀
    use ⟨isUnit_a.unit, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals
      apply (mem_integer_iff _ _ _).mp
      simp only [variableChange_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, mul_zero, add_zero,
        inv_pow, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      apply (Valuation.mem_integer_iff _ _).mpr
      simp only [map_mul, map_inv₀, map_pow, ha]
      refine inv_mul_le_one_of_le₀ ?_ zero_le'
      refine (hlmax _ (by simp [l₀, l])).trans ?_
    any_goals
      apply le_self_pow hlmax_ge_1.le
      linarith
    rfl

end Integral

section Minimal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

/-- The valuation of the discriminant of a Weierstrass curve `W`,
which is at most 1 if `W` is integral. Zero otherwise. -/
noncomputable def valuation_Δ_aux (W : WeierstrassCurve K) :
    { v : WithZero (Multiplicative ℤ) // v ≤ 1 } := by
  by_cases h : IsIntegral R W
  · exact ⟨valuation K (maximalIdeal R) W.Δ, by
      choose r hr using Δ_integral_of_isIntegral R W
      rw [← hr]
      exact valuation_le_one (maximalIdeal R) r⟩
  · exact ⟨⊥, bot_le⟩

lemma valuation_Δ_aux_eq_of_isIntegral (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    valuation_Δ_aux R W = valuation K (maximalIdeal R) W.Δ := by
  simp [valuation_Δ_aux, hW]

instance : WellFoundedGT { v : WithZero (Multiplicative ℤ) // v ≤ 1 } :=
  { wf :=
    (LinearOrderedCommGroupWithZero.wellFoundedOn_setOf_ge_gt_iff_nonempty_discrete_of_ne_zero
    one_ne_zero).mpr instNonemptyOfInhabited }

/-- A Weierstrass equation over the fraction field `K` is minimal if the (multiplicative) valuation
of its discriminant is maximal among all isomorphic integral Weierstrass equations.
We still use 'minimal' for the naming, so as to standardize the naming with Silverman's book. -/
@[mk_iff]
class IsMinimal (W : WeierstrassCurve K) : Prop where
  val_Δ_maximal :
    MaximalFor
      (fun (C : VariableChange K) ↦ IsIntegral R (C • W))
      (fun (C : VariableChange K) ↦ valuation_Δ_aux R (C • W))
      (1 : VariableChange K)

omit [IsFractionRing R K] in
instance {W : WeierstrassCurve K} [IsMinimal R W] :
    IsIntegral R W := by simpa using IsMinimal.val_Δ_maximal.1

theorem exists_minimal (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsMinimal R (C • W) := by
  obtain ⟨C, hC⟩ := exists_maximalFor_of_wellFoundedGT
    (fun (C : VariableChange K) ↦ IsIntegral R (C • W))
    (fun (C : VariableChange K) ↦ valuation_Δ_aux R (C • W))
    (exists_integral R W)
  refine ⟨C, ⟨⟨by simp only [one_smul, hC.1], ?_⟩⟩⟩
  intro j hj; rw [← smul_assoc] at hj
  let h := hC.2 hj
  simp_all only [one_smul]
  rw [← smul_assoc]
  exact h

/-- A minimal Weierstrass equation for a given Weierstrass curve over `K`. -/
noncomputable def minimal (W : WeierstrassCurve K) : WeierstrassCurve K :=
  (W.exists_minimal R).choose • W

instance {W : WeierstrassCurve K} :
    IsMinimal R (W.minimal R) := (W.exists_minimal R).choose_spec

end Minimal

section Reduction

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsLocalRing

/-- The reduction of a Weierstrass curve over `K` given by a minimal Weierstrass equation,
which is a Weierstrass curve over the residue field of `R`. -/
noncomputable def reduction (W : WeierstrassCurve K) [IsMinimal R W] :
    WeierstrassCurve (ResidueField R) :=
  letI hW : IsIntegral R W := inferInstance
  hW.integral.choose.map (residue R)

/-- A minimal Weierstrass equation has good reduction if and only if
the valuation of its discriminant is zero. -/
@[mk_iff]
class IsGoodReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop where
  goodReduction : addVal R ((algebraMap R K).toFun.invFun W.Δ) = 0

lemma isGoodReduction_iff_reduction_isElliptic {W : WeierstrassCurve K} [IsMinimal R W] :
    IsGoodReduction R W ↔ (W.reduction R).IsElliptic := by
  refine Iff.trans ?_ (W.reduction R).isElliptic_iff.symm
  simp only [reduction, map_Δ, isUnit_iff_ne_zero, ne_eq, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff, not_not]
  refine Iff.trans ?_ addVal_eq_zero_iff
  rw [integral_Δ_eq_of_isIntegral R W]
  exact isGoodReduction_iff _ _

end Reduction

end WeierstrassCurve
