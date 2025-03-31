/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-!
# Renaming variables of power series.

This file establishes the `rename` operation on multivariate power series,
which modifies the set of variables. Note that the function `f : σ → τ` must satisfies
`Tendsto f cofinite cofinite`, otherwise renaming does not make sense. This is the case if `f`
is injective (`Injective.tendsto_cofinite`) or if `σ` is a `Fintype` (`simp` can prove this).

## Main declarations

* `MvPowerSeries.rename`

## Notation

As in other files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPowerSeries σ R` which mathematicians might call `X^s`

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `F : MvPowerSeries σ α`

## TODO
Finish to copy the file `RingTheory.MvPolynomial.rename`.

-/

noncomputable section

variable {R S σ τ α : Type*}

namespace MvPowerSeries

section Rename

open WithPiTopology Function Filter

variable [CommRing R] {f : σ → τ} (hf : Tendsto f cofinite cofinite)

include hf

variable [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R] [CompleteSpace R]
  [T2Space R] [IsLinearTopology R R]

/-- Rename all the variables in a multivariable power series. -/
def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R :=
  aeval (hasEval_X_comp hf)

theorem rename_C (r : R) : rename hf (C σ R r) = C τ R r := by
  simp [rename, coe_aeval, ← c_eq_algebraMap]

@[simp]
theorem rename_X (i : σ) : rename hf (X i : MvPowerSeries σ R) = X (f i) := by
  simpa using aeval_coe (hasEval_X_comp hf) (MvPolynomial.X i)

@[simp]
theorem rename_monomial (n : σ →₀ ℕ) (r : R) :
    rename hf (monomial R n r : MvPowerSeries σ R) = monomial R (n.mapDomain f) r := by
  rw [← mul_one r, ← smul_eq_mul, map_smul, map_smul, map_smul]
  congr
  induction n using Finsupp.induction_linear with
  | h0 => simp [rename_C]
  | hadd n m hn hm =>
      rw [← one_mul 1, ← monomial_mul_monomial, map_mul, hn, hm, monomial_mul_monomial,
        Finsupp.mapDomain_add]
  | hsingle i n =>
    rw [← X_pow_eq, map_pow, rename_X, X_pow_eq, Finsupp.mapDomain_single]

@[fun_prop]
theorem continuous_rename : Continuous (rename (R := R) hf) :=
  continuous_aeval _

variable [CommRing S] [UniformSpace S] [IsTopologicalRing S] [IsUniformAddGroup S] [CompleteSpace S]
  [T2Space S] [IsLinearTopology S S] {φ : R →+* S}

theorem map_rename (hφ : Continuous φ) (F : MvPowerSeries σ R) :
    map τ φ (rename hf F) = rename hf (map σ φ F) := by
  have h1 := RingHom.comp_apply (map τ φ) (rename hf).toRingHom F
  have h2 := RingHom.comp_apply (rename hf).toRingHom (map σ φ) F
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2
  rw [← h1, ← h2]
  apply continuous_ringHom_ext
  · simp only [RingHom.coe_comp, RingHom.coe_coe]
    fun_prop
  · simp only [RingHom.coe_comp, RingHom.coe_coe]
    fun_prop
  · simp
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, comp_apply, map_C]
    rw [rename_C, map_C, rename_C]

lemma map_comp_rename (hφ : Continuous φ) :
    (map τ φ).comp (rename hf).toRingHom = (rename hf).toRingHom.comp (map σ φ) :=
  RingHom.ext fun p ↦ map_rename hf hφ p

@[simp]
theorem rename_rename {g : τ → α} (hg : Tendsto g cofinite cofinite) (F : MvPowerSeries σ R) :
    rename hg (rename hf F) = rename (hg.comp hf) F := by
    rw [← AlgHom.comp_apply]
    apply continuous_algHom_ext (by simp only [AlgHom.coe_comp]; fun_prop) (by fun_prop) (by simp)

lemma rename_comp_rename {g : τ → α} (hg : Tendsto g cofinite cofinite) :
    (rename (R := R) hg).comp (rename hf) = rename (hg.comp hf) :=
  AlgHom.ext fun F ↦ rename_rename hf hg F

omit hf

@[simp]
theorem rename_id : rename tendsto_id = AlgHom.id R (MvPowerSeries σ R) := by
  ext1 F
  apply continuous_algHom_ext (by fun_prop) (by simp only [AlgHom.coe_id]; fun_prop) (by simp)

omit hf in
lemma rename_id_apply (F : MvPowerSeries σ R) : rename tendsto_id F = F := by
  simp

theorem coeff_rename_mapDomain (hf : Function.Injective f) (F : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff R (n.mapDomain f) (rename hf.tendsto_cofinite F) = coeff R n F := by
  classical
  have h1 := LinearMap.comp_apply (coeff R (n.mapDomain f))
    (rename hf.tendsto_cofinite).toLinearMap F
  simp only [AlgHom.toLinearMap_apply] at h1
  rw [← h1]
  apply continuous_linearMap_ext
  · exact (continuous_coeff R _).comp (continuous_rename hf.tendsto_cofinite)
  · fun_prop
  · intro m
    rw [LinearMap.comp_apply]
    by_cases h : n = m
    · simp [coeff_monomial, h]
    · simp only [AlgHom.toLinearMap_apply, rename_monomial, coeff_monomial, h, reduceIte,
        ite_eq_right_iff]
      exact fun H ↦ by simpa using h <| Finsupp.mapDomain_injective hf H

theorem rename_injective (hf : Function.Injective f) :
    Function.Injective (rename hf.tendsto_cofinite : MvPowerSeries σ R → MvPowerSeries τ R) := by
  intro F₁ F₂ h
  ext n
  rw [← coeff_rename_mapDomain hf, ← coeff_rename_mapDomain hf, h]

end Rename

end MvPowerSeries

end
