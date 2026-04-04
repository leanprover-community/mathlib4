/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Equivalences between power series rings

This file establishes a number of equivalences between power series rings,
based on equivalences between the underlying types.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPowerSeries σ R` which mathematicians might call `X^s`.

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPowerSeries σ R`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/

@[expose] public section

noncomputable section

open PowerSeries Set Function Finsupp Filter

universe u v w x

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
variable {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ τ : Type*} {f : PowerSeries R} (i : σ) (r : R)

section Map

namespace MvPowerSeries

variable (σ) [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃]

/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
@[simps apply]
def mapEquiv [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    MvPowerSeries σ S₁ ≃+* MvPowerSeries σ S₂ :=
  { map (e : S₁ →+* S₂) with
    toFun := map (e : S₁ →+* S₂)
    invFun := map (e.symm : S₂ →+* S₁)
    left_inv := map_leftInverse e.left_inv
    right_inv := map_rightInverse e.right_inv }

@[simp]
theorem mapEquiv_refl : mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.ext_iff.mpr (congrFun rfl)

@[simp]
theorem mapEquiv_symm (e : S₁ ≃+* S₂) : (mapEquiv σ e).symm = mapEquiv σ e.symm := rfl

@[simp]
theorem mapEquiv_trans (e : S₁ ≃+* S₂)
    (f : S₂ ≃+* S₃) : (mapEquiv σ e).trans (mapEquiv σ f) = mapEquiv σ (e.trans f) :=
  RingEquiv.ext fun p => by
    simp only [RingEquiv.coe_trans, comp_apply, mapEquiv_apply, RingEquiv.coe_ringHom_trans,
      map_map]

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
def mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPowerSeries σ A₁ ≃ₐ[R] MvPowerSeries σ A₂ :=
  { mapAlgHom (e : A₁ →ₐ[R] A₂), mapEquiv σ (e : A₁ ≃+* A₂) with toFun := map (e : A₁ →+* A₂) }

@[simp]
theorem mapAlgEquiv_refl : mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext (AlgEquiv.congr_fun rfl ·)

@[simp]
theorem mapAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm := rfl

@[simp]
theorem mapAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (mapAlgEquiv σ e).trans (mapAlgEquiv σ f) = mapAlgEquiv σ (e.trans f) := by
  ext
  simp only [AlgEquiv.trans_apply, mapAlgEquiv_apply, map_map]
  rfl

end MvPowerSeries

end Map

section toMvPowerSeries

namespace PowerSeries

/-- Given a power series p(X) ∈ R⟦X⟧ and an index i, we may view it as a
multivariate power series p(X_i) ∈ R⟦X_1, ..., X_n⟧.
-/
noncomputable
def toMvPowerSeries : PowerSeries R →ₐ[R] MvPowerSeries σ R :=
  MvPowerSeries.rename (fun _ => i)

theorem toMvPowerSeries_apply : f.toMvPowerSeries i = f.rename (fun _ => i) := rfl

theorem toMvPowerSeries_C : (C r).toMvPowerSeries i = MvPowerSeries.C r := by
  have : C r = MvPowerSeries.C r := rfl
  rw [toMvPowerSeries_apply, this, MvPowerSeries.rename_C]

theorem toMvPowerSeries_X : X.toMvPowerSeries i = MvPowerSeries.X i (R := R) := by
  rw [toMvPowerSeries_apply, X, MvPowerSeries.rename_X]

theorem toMvPowerSeries_injective (i : σ) : Function.Injective (toMvPowerSeries (R := R) i) :=
  MvPowerSeries.rename_injective (Embedding.punit i)

section CommRing

variable {R : Type*} [CommRing R] {f : PowerSeries R} (i : σ) (r : R) (p : R⟦X⟧)

theorem toMvPowerSeries_eq_subst : f.toMvPowerSeries i = f.subst (MvPowerSeries.X i) := by
  rw [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst, comp_def, subst]

theorem HasSubst.toMvPowerSeries (hf : f.constantCoeff = 0) :
    MvPowerSeries.HasSubst (f.toMvPowerSeries · (σ := σ)) (S := R) where
  const_coeff := by simp_all [constantCoeff, toMvPowerSeries_apply]
  coeff_zero d := Set.Finite.subset (Finite.of_fintype ↥d.support) fun s => by classical
    contrapose
    simp only [SetLike.mem_coe, mem_support_iff, Decidable.not_not, mem_setOf_eq]
    have : (MvPowerSeries.subst (MvPowerSeries.X (R := R) ∘ fun x ↦ s) f)
      = f.subst (MvPowerSeries.X s) := rfl
    intro hd
    rw [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst, this, coeff_subst (HasSubst.X _),
      finsum_eq_zero_of_forall_eq_zero]
    intro n
    by_cases! hn : n = 0
    · simp [hn, hf]
    have : d ≠ single s n := ne_iff.mpr ⟨s, by simp [hd, hn.symm]⟩
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg this, smul_zero]

theorem toMvPowerSeries_val {a : σ → MvPowerSeries τ R} (i : σ)
    (ha : MvPowerSeries.HasSubst a) : (f.toMvPowerSeries i).subst a = f.subst (a i) := by
  rw [toMvPowerSeries_eq_subst, subst, MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X _)) ha, MvPowerSeries.subst_X ha, subst]

end CommRing

end PowerSeries

variable (f : σ → τ) [TendstoCofinite f] (a : σ) (p : R⟦X⟧)

@[simp]
lemma MvPowerSeries.rename_comp_toMvPowerSeries :
    (rename (R := R) f).comp (PowerSeries.toMvPowerSeries a)
      = PowerSeries.toMvPowerSeries (f a) := by
  ext
  simp [toMvPowerSeries_apply, comp_def]

@[simp]
lemma MvPowerSeries.rename_toMvPowerSeries :
    (p.toMvPowerSeries a).rename f = p.toMvPowerSeries (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPowerSeries ..) p

end toMvPowerSeries
