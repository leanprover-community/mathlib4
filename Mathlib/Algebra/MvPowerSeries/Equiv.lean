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

open PowerSeries Set Function Finsupp AddMonoidAlgebra

universe u v w x

variable {R : Type u} [CommRing R] {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

section toMvPowerSeries

namespace PowerSeries

variable {σ τ : Type*} {f : PowerSeries R} (i : σ) (r : R)

/-- Given a power series p(X) ∈ R⟦X⟧ and an index i, we may view it as a
multivariate power series p(X_i) ∈ R⟦X_1, ..., X_n⟧.
-/
noncomputable
def toMvPowerSeries : PowerSeries R →ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.X i)

@[simp]
theorem toMvPowerSeries_apply :
    f.toMvPowerSeries i = f.subst (MvPowerSeries.X i) := by
  rw [toMvPowerSeries, coe_substAlgHom]

theorem HasSubst.toMvPowerSeries [Finite σ] (hf : f.constantCoeff = 0) :
    MvPowerSeries.HasSubst (f.toMvPowerSeries · (σ := σ)) (S := R) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by
    rw [toMvPowerSeries_apply, constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ hf]

theorem toMvPowerSeries_val {a : σ → MvPowerSeries τ R} (i : σ)
    (ha : MvPowerSeries.HasSubst a) : (f.toMvPowerSeries i).subst a = f.subst (a i) := by
  simp_rw [toMvPowerSeries_apply, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X i)) ha, MvPowerSeries.subst_X ha]

theorem toMvPowerSeries_C : (C r).toMvPowerSeries i = MvPowerSeries.C r := by
  rw [toMvPowerSeries_apply, subst_C]

theorem toMvPowerSeries_X : X.toMvPowerSeries i = MvPowerSeries.X i (R := R) := by
  rw [toMvPowerSeries_apply, subst_X (HasSubst.X i)]

lemma toMvPowerSeries_eq_rename_comp (i : σ) :
    toMvPowerSeries (R := R) i = (MvPowerSeries.rename (fun _ : Unit ↦ i)) := by
  ext f : 1
  simp only [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst]
  rfl

lemma toMvPowerSeries_injective (i : σ) :
    Function.Injective (toMvPowerSeries (R := R) i) := by
  rw [toMvPowerSeries_eq_rename_comp]
  exact MvPowerSeries.rename_injective (Embedding.punit i) (R := R)

-- @[simp]
-- lemma MvPolynomial.eval_comp_toMvPolynomial (f : σ → R) (i : σ) :
--     (eval f).comp (toMvPolynomial (R := R) i) = Polynomial.evalRingHom (f i) := by
--   ext <;> simp

-- @[simp]
-- lemma MvPolynomial.eval_toMvPolynomial (f : σ → R) (i : σ) (p : R[X]) :
--     eval f (p.toMvPolynomial i) = Polynomial.eval (f i) p :=
--   DFunLike.congr_fun (eval_comp_toMvPolynomial ..) p

-- @[simp]
-- lemma MvPolynomial.aeval_comp_toMvPolynomial (f : σ → S) (i : σ) :
--     (aeval (R := R) f).comp (toMvPolynomial i) = Polynomial.aeval (f i) := by
--   ext
--   simp

-- @[simp]
-- lemma MvPolynomial.aeval_toMvPolynomial (f : σ → S) (i : σ) (p : R[X]) :
--     aeval f (p.toMvPolynomial i) = Polynomial.aeval (f i) p :=
--   DFunLike.congr_fun (aeval_comp_toMvPolynomial ..) p

-- @[simp]
-- lemma MvPolynomial.rename_comp_toMvPolynomial (f : σ → τ) (a : σ) :
--     (rename (R := R) f).comp (Polynomial.toMvPolynomial a) = Polynomial.toMvPolynomial (f a) := by
--   ext
--   simp

-- @[simp]
-- lemma MvPolynomial.rename_toMvPolynomial (f : σ → τ) (a : σ) (p : R[X]) :
--     (rename (R := R) f) (p.toMvPolynomial a) = p.toMvPolynomial (f a) :=
--   DFunLike.congr_fun (rename_comp_toMvPolynomial ..) p

-- #check MvPowerSeries.rename

/- TODO: some API related to rename. -/

end PowerSeries

end toMvPowerSeries
