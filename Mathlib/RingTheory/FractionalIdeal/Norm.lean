/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Localization.NormTrace

/-!

# Fractional ideal norms

This file defines the absolute ideal norm of a fractional ideal `I : FractionalIdeal R⁰ K` where
`K` is a fraction field of `R`. The norm is defined by
`FractionalIdeal.absNorm I = Ideal.absNorm I.num / |Algebra.norm ℤ I.den|` where `I.num` is an
ideal of `R` and `I.den` an element of `R⁰` such that `I.den • I = I.num`.

## Main definitions and results

* `FractionalIdeal.absNorm`: the norm as a zero-preserving morphism with values in `ℚ`.
* `FractionalIdeal.absNorm_eq'`: the value of the norm does not depend on the choice of
  `I.num` and `I.den`.
* `FractionalIdeal.abs_det_basis_change`: the norm is given by the determinant
  of the basis change matrix.
* `FractionalIdeal.absNorm_span_singleton`: the norm of a principal fractional ideal is the
  norm of its generator
-/

@[expose] public section

open Module
open scoped Pointwise nonZeroDivisors

namespace FractionalIdeal
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

section

variable [Infinite R] [Ring.HasFiniteQuotients R]

theorem absNorm_div_absNorm_span_eq {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
    (h : a • (I : Submodule R K) = Submodule.map (Algebra.linearMap R K) I₀) :
    (Ideal.absNorm I.num : ℚ) / (Ideal.absNorm (Ideal.span {(I.den : R)}) : ℚ) =
      (Ideal.absNorm I₀ : ℚ) / (Ideal.absNorm (Ideal.span {(a : R)}) : ℚ) := by
  rw [div_eq_div_iff]
  · replace h := congr_arg (I.den • ·) h
    have h' := congr_arg (a • ·) (den_mul_self_eq_num I)
    rw [smul_comm] at h
    rw [h, Submonoid.smul_def, Submonoid.smul_def, ← Submodule.ideal_span_singleton_smul,
      ← Submodule.ideal_span_singleton_smul, ← Submodule.map_smul'', ← Submodule.map_smul'',
      (LinearMap.map_injective ?_).eq_iff, smul_eq_mul, smul_eq_mul] at h'
    · simp_rw [← Nat.cast_mul]
      rw [← map_mul, ← map_mul, mul_comm, ← h', mul_comm]
    · exact LinearMap.ker_eq_bot.mpr (IsFractionRing.injective R K)
  all_goals simp [Ideal.absNorm_eq_zero_iff, nonZeroDivisors.coe_ne_zero]

/-- The absolute norm of the fractional ideal `I`, defined via the absolute norm of ideals only
(so without requiring `R` to be a free `ℤ`-module). -/
noncomputable def absNorm : FractionalIdeal R⁰ K →*₀ ℚ where
  toFun I := (Ideal.absNorm I.num : ℚ) / (Ideal.absNorm (Ideal.span {(I.den : R)}) : ℚ)
  map_zero' := by
    rw [num_zero_eq, Submodule.zero_eq_bot, Ideal.absNorm_bot, Nat.cast_zero, zero_div]
    exact IsFractionRing.injective R K
  map_one' := by
    rw [absNorm_div_absNorm_span_eq 1 ⊤ (by simp [Submodule.one_eq_range])]
    simp
  map_mul' I J := by
    rw [absNorm_div_absNorm_span_eq (I.den * J.den) (I.num * J.num) (by
        have : Algebra.linearMap R K = (IsScalarTower.toAlgHom R R K).toLinearMap := rfl
        rw [coe_mul, this, Submodule.map_mul, ← this, ← den_mul_self_eq_num, ← den_mul_self_eq_num]
        exact Submodule.mul_smul_mul_eq_smul_mul_smul _ _ _ _),
      Submonoid.coe_mul, map_mul, ← Ideal.span_singleton_mul_span_singleton, map_mul,
      Nat.cast_mul, Nat.cast_mul, div_mul_div_comm]

theorem absNorm_eq_absNorm_span (I : FractionalIdeal R⁰ K) :
    absNorm I = (Ideal.absNorm I.num : ℚ) / (Ideal.absNorm (Ideal.span {(I.den : R)}) : ℚ) := rfl

theorem absNorm_eq_absNorm_span' {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
    (h : a • (I : Submodule R K) = Submodule.map (Algebra.linearMap R K) I₀) :
    absNorm I = (Ideal.absNorm I₀ : ℚ) / (Ideal.absNorm (Ideal.span {(a : R)}) : ℚ) := by
  rw [absNorm, ← absNorm_div_absNorm_span_eq a I₀ h, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]

theorem absNorm_nonneg (I : FractionalIdeal R⁰ K) : 0 ≤ absNorm I := by
  dsimp [absNorm]; positivity

theorem absNorm_bot : absNorm (⊥ : FractionalIdeal R⁰ K) = 0 := absNorm.map_zero'

theorem absNorm_one : absNorm (1 : FractionalIdeal R⁰ K) = 1 := by convert! absNorm.map_one'

theorem absNorm_eq_zero_iff [IsDomain K] {I : FractionalIdeal R⁰ K} :
    absNorm I = 0 ↔ I = 0 := by
  refine ⟨fun h ↦ zero_of_num_eq_bot zero_notMem_nonZeroDivisors ?_, fun h ↦ h ▸ absNorm_bot⟩
  rw [absNorm_eq_absNorm_span, div_eq_zero_iff] at h
  refine Ideal.absNorm_eq_zero_iff.mp <| Nat.cast_eq_zero.mp <| h.resolve_right ?_
  simp [Ideal.absNorm_eq_zero_iff, nonZeroDivisors.coe_ne_zero]

theorem coeIdeal_absNorm (I₀ : Ideal R) :
    absNorm (I₀ : FractionalIdeal R⁰ K) = Ideal.absNorm I₀ := by
  rw [absNorm_eq_absNorm_span' 1 I₀ (by rw [one_smul]; rfl), OneMemClass.coe_one,
    Ideal.span_singleton_one, Ideal.absNorm_top, Nat.cast_one, _root_.div_one]

end

variable [Module.Free ℤ R] [Module.Finite ℤ R]

-- `Infinite R` for the basis/determinant lemmas below (a nontrivial free `ℤ`-module is infinite).
local instance : Infinite R := Module.Free.infinite ℤ R

theorem absNorm_eq (I : FractionalIdeal R⁰ K) :
    absNorm I = (Ideal.absNorm I.num : ℚ) / |Algebra.norm ℤ (I.den : R)| := by
  rw [absNorm_eq_absNorm_span, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]

theorem absNorm_eq' {I : FractionalIdeal R⁰ K} (a : R⁰) (I₀ : Ideal R)
    (h : a • (I : Submodule R K) = Submodule.map (Algebra.linearMap R K) I₀) :
    absNorm I = (Ideal.absNorm I₀ : ℚ) / |Algebra.norm ℤ (a : R)| := by
  rw [absNorm_eq_absNorm_span' a I₀ h, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]

section IsLocalization

variable [IsLocalization (Algebra.algebraMapSubmonoid R ℤ⁰) K] [Algebra ℚ K]

theorem abs_det_basis_change [IsDomain K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℤ R) (I : FractionalIdeal R⁰ K) (bI : Basis ι ℤ I) :
    |(b.localizationLocalization ℚ ℤ⁰ K).det ((↑) ∘ bI)| = absNorm I := by
  have := IsFractionRing.nontrivial R K
  let b₀ : Basis ι ℚ K := b.localizationLocalization ℚ ℤ⁰ K
  let bI.num : Basis ι ℤ I.num := bI.map
      ((equivNum (nonZeroDivisors.coe_ne_zero _)).restrictScalars ℤ)
  rw [absNorm_eq, ← Ideal.natAbs_det_basis_change b I.num bI.num, Nat.cast_natAbs, Int.cast_abs,
    Int.cast_abs, Basis.det_apply, Basis.det_apply]
  change _ = |algebraMap ℤ ℚ _| / _
  rw [RingHom.map_det, show RingHom.mapMatrix (algebraMap ℤ ℚ) (b.toMatrix ((↑) ∘ bI.num)) =
      b₀.toMatrix ((algebraMap R K (den I : R)) • ((↑) ∘ bI)) by
    ext : 2
    simp_rw [bI.num, RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply,
      ← Basis.localizationLocalization_repr_algebraMap ℚ ℤ⁰ K, Function.comp_apply,
      Basis.map_apply, LinearEquiv.restrictScalars_apply, equivNum_apply, Submonoid.smul_def,
      Algebra.smul_def]
    rfl]
  rw [Basis.toMatrix_smul, Matrix.det_mul, abs_mul, ← Algebra.norm_eq_matrix_det,
    Algebra.norm_localization ℤ ℤ⁰, show (Algebra.norm ℤ (den I : R) : ℚ) =
    algebraMap ℤ ℚ (Algebra.norm ℤ (den I : R)) by rfl, mul_div_assoc, mul_div_cancel₀ _ (by
    rw [ne_eq, abs_eq_zero, IsFractionRing.to_map_eq_zero_iff, Algebra.norm_eq_zero_iff_of_basis b]
    exact nonZeroDivisors.coe_ne_zero _)]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
@[simp]
theorem absNorm_span_singleton [Module.Finite ℚ K] (x : K) :
    absNorm (spanSingleton R⁰ x) = |(Algebra.norm ℚ x)| := by
  have : IsDomain K := IsFractionRing.isDomain R
  obtain ⟨d, ⟨r, hr⟩⟩ := IsLocalization.exists_integer_multiple R⁰ x
  rw [absNorm_eq' d (Ideal.span {r})]
  · rw [Ideal.absNorm_span_singleton]
    simp_rw [Nat.cast_natAbs, Int.cast_abs, show ((Algebra.norm ℤ _) : ℚ) = algebraMap ℤ ℚ
      (Algebra.norm ℤ _) by rfl, ← Algebra.norm_localization ℤ ℤ⁰ (Sₘ := K) _]
    rw [hr, Algebra.smul_def, map_mul, abs_mul, mul_div_assoc, mul_div_cancel₀ _ (by
      rw [ne_eq, abs_eq_zero, Algebra.norm_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero _)]
  · ext
    simp_rw [Submodule.mem_smul_pointwise_iff_exists, mem_coe, mem_spanSingleton, Submodule.mem_map,
      Algebra.linearMap_apply, Submonoid.smul_def, Ideal.mem_span_singleton', exists_exists_eq_and,
      map_mul, hr, ← Algebra.smul_def, smul_comm (d : R)]

end IsLocalization

end FractionalIdeal
