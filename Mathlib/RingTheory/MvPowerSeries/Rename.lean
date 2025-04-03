/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Renaming variables of power series.

This file establishes the `rename` operation on multivariate power series,
which modifies the set of variables.

Renaming only makes sense if `f : σ → τ` satisfies `Tendsto f cofinite cofinite` (since
`X_1 + X_2 + ...` is a power series in `ℤ⟦X_1, X_2,...⟧`). To avoid having to write this
assumption everywhere we work with `[hf : Fact (Tendsto f cofinite cofinite)]`. Note that this holds
if `f` is injective (`Injective.tendsto_cofinite`) or if `σ` is a `Fintype` (we set up a local
instance to take care of this case).


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

local instance [Fintype σ] (f : σ → τ) : Fact (Tendsto f cofinite cofinite) := ⟨by simp⟩

variable [CommRing R] (f : σ → τ) [hf : Fact (Tendsto f cofinite cofinite)]

local instance {g : τ → α} [hg : Fact (Tendsto g cofinite cofinite)] :
  Fact (Tendsto (g ∘ f) cofinite cofinite) := ⟨hg.out.comp hf.out⟩

local instance : Fact (Tendsto (id : σ → σ) cofinite cofinite) := ⟨tendsto_id⟩

/-- Rename all the variables in a multivariable power series. -/
def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R :=
  substAlgHom (HasSubst.X_comp hf.out)

theorem rename_C (r : R) : rename f (C σ R r) = C τ R r := by
  simp [rename, c_eq_algebraMap]

@[simp]
theorem rename_X (i : σ) : rename f (X i : MvPowerSeries σ R) = X (f i) := by
  simp [rename, HasSubst.X_comp hf.out]

theorem rename_coe (P : MvPolynomial σ R) : rename f (P : MvPowerSeries σ R) = P.rename f := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rename_C]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP => simp [hP]

theorem rename_monomial (n : σ →₀ ℕ) (r : R) :
    rename f (monomial R n r : MvPowerSeries σ R) = monomial R (n.mapDomain f) r := by
  rw [← MvPolynomial.coe_monomial, rename_coe, MvPolynomial.rename_monomial,
    MvPolynomial.coe_monomial]

open WithPiTopology in
@[fun_prop]
theorem continuous_rename [UniformSpace R] [DiscreteUniformity R] :
    Continuous (rename (R := R) f) := by
  simp [rename, HasSubst.X_comp hf.out, continuous_subst (R := R) (S := R) (HasSubst.X_comp hf.out)]

variable [CommRing S] (φ : R →+* S)

open WithPiTopology in
theorem map_rename (F : MvPowerSeries σ R) :
    map τ φ (rename f F) = rename f (map σ φ F) := by
  have h1 := RingHom.comp_apply (map τ φ) (rename f).toRingHom F
  have h2 := RingHom.comp_apply (rename f).toRingHom (map σ φ) F
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
    (map τ φ).comp (rename f).toRingHom = (rename f).toRingHom.comp (map σ φ) :=
  RingHom.ext fun p ↦ map_rename f φ p

open WithPiTopology in
@[simp]
theorem rename_rename (g : τ → α) [hg : Fact (Tendsto g cofinite cofinite)]
    (F : MvPowerSeries σ R) :
    rename g (rename f F) = rename (g.comp f) F := by
  have := congr_fun
    (subst_comp_subst (S := R) (T := R) (HasSubst.X_comp hf.out) (HasSubst.X_comp hg.out)) F
  simp only [comp_apply] at this
  simp [rename, this, HasSubst.X_comp hg.out]

lemma rename_comp_rename (g : τ → α) [hg : Fact (Tendsto g cofinite cofinite)] :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  AlgHom.ext fun F ↦ rename_rename f g F

@[simp]
theorem rename_id : rename id = AlgHom.id R (MvPowerSeries σ R) := by
  ext1 F
  simp [rename, ← MvPowerSeries.map_algebraMap_eq_subst_X]

lemma rename_id_apply (F : MvPowerSeries σ R) : rename id F = F := by
  simp

open WithPiTopology in
theorem coeff_rename_mapDomain {f : σ → τ} (hf : Function.Injective f) (F : MvPowerSeries σ R)
    (n : σ →₀ ℕ) :
    haveI : Fact (Tendsto f cofinite cofinite) := ⟨hf.tendsto_cofinite⟩
    coeff R (n.mapDomain f) (rename f F) = coeff R n F := by
  have : Fact (Tendsto f cofinite cofinite) := ⟨hf.tendsto_cofinite⟩
  have h1 := LinearMap.comp_apply (coeff R (n.mapDomain f)) (rename f).toLinearMap F
  simp only [AlgHom.toLinearMap_apply] at h1
  rw [← h1]
  congr
  apply LinearMap.coe_injective
  let _ : UniformSpace R := ⊥
  apply Continuous.ext_on (MvPolynomial.toMvPowerSeries_isDenseInducing ).dense
  · simp only [LinearMap.coe_comp]
    apply Continuous.comp
    · fun_prop
    · exact continuous_rename f
  · fun_prop
  · simp only [LinearMap.coe_comp, Set.eqOn_range]
    ext F
    simp [rename_coe, hf]

theorem rename_injective {f : σ → τ} (hf : Function.Injective f) :
    haveI : Fact (Tendsto f cofinite cofinite) := ⟨hf.tendsto_cofinite⟩
    Function.Injective (rename f : MvPowerSeries σ R → MvPowerSeries τ R) := by
  intro F₁ F₂ h
  ext n
  rw [← coeff_rename_mapDomain hf, ← coeff_rename_mapDomain hf, h]

end Rename

end MvPowerSeries

end
