/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.MvPowerSeries.Substitution

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

open Function Filter

variable [CommRing R] {f : σ → τ} (hf : Tendsto f cofinite cofinite)

include hf

/-- Rename all the variables in a multivariable power series. -/
def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R :=
  substAlgHom (HasSubst.X_comp hf)

theorem rename_C (r : R) : rename hf (C σ R r) = C τ R r := by
  simp [rename, c_eq_algebraMap]

@[simp]
theorem rename_X (i : σ) : rename hf (X i : MvPowerSeries σ R) = X (f i) := by
  simp [rename, HasSubst.X_comp hf]

theorem rename_coe (P : MvPolynomial σ R) : rename hf (P : MvPowerSeries σ R) = P.rename f := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rename_C]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP => simp [hP]

theorem rename_monomial (n : σ →₀ ℕ) (r : R) :
    rename hf (monomial R n r : MvPowerSeries σ R) = monomial R (n.mapDomain f) r := by
  rw [← MvPolynomial.coe_monomial, rename_coe, MvPolynomial.rename_monomial,
    MvPolynomial.coe_monomial]

open WithPiTopology in
@[fun_prop]
theorem continuous_rename [UniformSpace R] [DiscreteUniformity R] :
    Continuous (rename (R := R) hf) := by
  simp [rename, HasSubst.X_comp hf, continuous_subst (R := R) (S := R) (HasSubst.X_comp hf)]

variable [CommRing S] (φ : R →+* S)

open WithPiTopology in
theorem map_rename (F : MvPowerSeries σ R) :
    map τ φ (rename hf F) = rename hf (map σ φ F) := by
  have h1 := RingHom.comp_apply (map τ φ) (rename hf).toRingHom F
  have h2 := RingHom.comp_apply (rename hf).toRingHom (map σ φ) F
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2
  rw [← h1, ← h2]
  let _ : UniformSpace R := ⊥
  let _ : UniformSpace S := ⊥
  congr
  apply RingHom.coe_inj
  apply Continuous.ext_on (MvPolynomial.toMvPowerSeries_isDenseInducing ).dense
  · simp only [RingHom.coe_comp, RingHom.coe_coe]
    fun_prop
  · simp only [RingHom.coe_comp, RingHom.coe_coe]
    fun_prop
  · simp only [RingHom.coe_comp, RingHom.coe_coe, Set.eqOn_range]
    ext1 F
    simp [rename_coe, ← MvPolynomial.coe_map, MvPolynomial.map_rename]

lemma map_comp_rename :
    (map τ φ).comp (rename hf).toRingHom = (rename hf).toRingHom.comp (map σ φ) :=
  RingHom.ext fun p ↦ map_rename hf φ p

open WithPiTopology in
@[simp]
theorem rename_rename {g : τ → α} (hg : Tendsto g cofinite cofinite) (F : MvPowerSeries σ R) :
    rename hg (rename hf F) = rename (hg.comp hf) F := by
  have := congr_fun
    (subst_comp_subst (S := R) (T := R) (HasSubst.X_comp hf) (HasSubst.X_comp hg)) F
  simp only [comp_apply] at this
  simp [rename, this, HasSubst.X_comp hg]

lemma rename_comp_rename {g : τ → α} (hg : Tendsto g cofinite cofinite) :
    (rename (R := R) hg).comp (rename hf) = rename (hg.comp hf) :=
  AlgHom.ext fun F ↦ rename_rename hf hg F

omit hf

@[simp]
theorem rename_id : rename tendsto_id = AlgHom.id R (MvPowerSeries σ R) := by
  ext1 F
  simp [rename, ← MvPowerSeries.map_algebraMap_eq_subst_X]

lemma rename_id_apply (F : MvPowerSeries σ R) : rename tendsto_id F = F := by
  simp

open WithPiTopology in
theorem coeff_rename_mapDomain (hf : Function.Injective f) (F : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff R (n.mapDomain f) (rename hf.tendsto_cofinite F) = coeff R n F := by
  classical
  have h1 := LinearMap.comp_apply (coeff R (n.mapDomain f))
    (rename hf.tendsto_cofinite).toLinearMap F
  simp only [AlgHom.toLinearMap_apply] at h1
  rw [← h1]
  congr
  apply LinearMap.coe_injective
  let _ : UniformSpace R := ⊥
  apply Continuous.ext_on (MvPolynomial.toMvPowerSeries_isDenseInducing ).dense
  · simp only [LinearMap.coe_comp]
    apply Continuous.comp
    · fun_prop
    · exact continuous_rename hf.tendsto_cofinite
  · fun_prop
  · simp only [LinearMap.coe_comp, Set.eqOn_range]
    ext F
    simp [rename_coe, hf]

theorem rename_injective (hf : Function.Injective f) :
    Function.Injective (rename hf.tendsto_cofinite : MvPowerSeries σ R → MvPowerSeries τ R) := by
  intro F₁ F₂ h
  ext n
  rw [← coeff_rename_mapDomain hf, ← coeff_rename_mapDomain hf, h]

end Rename

end MvPowerSeries

end
