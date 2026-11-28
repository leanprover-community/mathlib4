/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Linear maps acting on families of multivariate power series

For a family of power series whose coefficient vectors have finite support, a linear map
between finitely supported functions acts coefficientwise on the family.

## Main declarations

* `MvPowerSeries.vecCoeff`: the finitely supported coefficient vector of a family.
* `MvPowerSeries.mapVecCoeff`: the coefficientwise action of a linear map on a family.
* `MvPowerSeries.subst_mapVecCoeff`: substitution commutes with this action.
-/

@[expose] public section

noncomputable section

namespace MvPowerSeries

open Function

variable {ι τ σ υ R : Type*}

section Semiring

variable [Semiring R] (L : (ι →₀ R) →ₗ[R] (τ →₀ R)) {v : ι → MvPowerSeries σ R}
  (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite)

variable (v) in
/-- The finitely supported coefficient vector of `d` in the family `v`. -/
def vecCoeff (d : σ →₀ ℕ) : ι →₀ R :=
  Finsupp.ofSupportFinite (fun i ↦ coeff d (v i)) (hv d)

@[simp]
theorem vecCoeff_apply (d : σ →₀ ℕ) (i : ι) : vecCoeff v hv d i = coeff d (v i) := rfl

variable (v) in
/-- The family obtained by applying `L` to the coefficient vectors of `v`. -/
def mapVecCoeff : τ → MvPowerSeries σ R := fun j d ↦ L (vecCoeff v hv d) j

theorem coeff_mapVecCoeff (j : τ) (d : σ →₀ ℕ) :
    coeff d (mapVecCoeff L v hv j) = L (vecCoeff v hv d) j := rfl

theorem constantCoeff_mapVecCoeff (hv0 : ∀ i, constantCoeff (v i) = 0) (j : τ) :
    constantCoeff (mapVecCoeff L v hv j) = 0 := by
  have h : vecCoeff v hv 0 = 0 := by
    ext i
    simpa using hv0 i
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mapVecCoeff, h, map_zero, Finsupp.zero_apply]

theorem mapVecCoeff_eq_zero (h : ∀ i, v i = 0) (j : τ) : mapVecCoeff L v hv j = 0 := by
  ext d
  have hd : vecCoeff v hv d = 0 := by
    ext i
    simp [h i]
  rw [coeff_mapVecCoeff, hd, map_zero, Finsupp.zero_apply, coeff_zero]

variable {L} in
theorem eq_zero_of_mapVecCoeff_eq_zero (hL : Injective L) (h : mapVecCoeff L v hv = 0) :
    v = 0 := by
  ext i d
  have hd : L (vecCoeff v hv d) = 0 := Finsupp.ext fun j ↦ congrArg (coeff d) (congrFun h j)
  exact congr($((map_eq_zero_iff L hL).mp hd) i)

end Semiring

section CommRing

variable [CommRing R] (L : (ι →₀ R) →ₗ[R] (τ →₀ R)) {v : ι → MvPowerSeries σ R}
  (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite)

theorem HasSubst.mapVecCoeff (hv0 : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (mapVecCoeff L v hv) where
  const_coeff j := by simp [constantCoeff_mapVecCoeff L hv hv0 j]
  coeff_zero d := (L (vecCoeff v hv d)).hasFiniteSupport

/-- Substitution commutes with the coefficientwise action of a linear map. -/
theorem subst_mapVecCoeff (hv' : HasSubst v) {a : σ → MvPowerSeries υ R} (ha : HasSubst a) (j : τ) :
    (mapVecCoeff L v hv'.coeff_zero j).subst a =
      mapVecCoeff L (fun i ↦ (v i).subst a) (hv'.subst ha).coeff_zero j := by
  classical
  ext e
  let c : (σ →₀ ℕ) → R := fun d ↦ coeff e (d.prod fun s n ↦ a s ^ n)
  have h1 (d : σ →₀ ℕ) : coeff d (fun _ ↦ (1 : R) : MvPowerSeries σ R) = 1 := rfl
  have hD : (Function.support c).Finite :=
    (coeff_subst_finite ha (fun _ ↦ 1 : MvPowerSeries σ R) e).subset fun d hd ↦ by
      simpa [Function.mem_support, h1, c] using hd
  have hsub (f : MvPowerSeries σ R) :
      coeff e (f.subst a) = ∑ d ∈ hD.toFinset, c d * coeff d f := by
    rw [coeff_subst ha]
    exact (finsum_eq_sum_of_support_subset _ <| Function.support_subset_iff'.mpr <| by
      simp +contextual [c]).trans (Finset.sum_congr rfl fun d _ ↦ mul_comm _ _)
  have hW : vecCoeff (fun i ↦ (v i).subst a) (hv'.subst ha).coeff_zero e =
      ∑ d ∈ hD.toFinset, c d • vecCoeff v hv'.coeff_zero d := by
    ext i
    simp [hsub]
  rw [coeff_mapVecCoeff, hW, hsub]
  simp [coeff_mapVecCoeff]

end CommRing

end MvPowerSeries
