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

variable {σ τ : Type*} {f : PowerSeries R} (i : σ) (r : R)

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
