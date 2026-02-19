/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!

# PowerSeries and AdicCompletion

-/

@[expose] public section

variable {R : Type*} [CommRing R] {σ : Type*} [Finite σ]

--set_option backward.isDefEq.respectTransparency false

def MvPolynomial.quotientEquivMvPowerSeriesAux (n : ℕ) :
    ((MvPolynomial σ R) ⧸ (Ideal.span (Set.range (MvPolynomial.X (σ := σ) (R := R)))) ^ n) →ₐ[R]
    ((MvPowerSeries σ R) ⧸ (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) ^ n) :=
  Ideal.quotientMapₐ _ (MvPolynomial.coeToMvPowerSeries.algHom R) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    apply Ideal.pow_right_mono
    simp only [Ideal.map_le_iff_le_comap, Ideal.span_le, Ideal.coe_comap]
    intro f hf
    rcases hf with ⟨i, hi⟩
    simpa [← hi] using Ideal.mem_span_range_self )

def MvPolynomial.quotientEquivMvPowerSeries (n : ℕ) :
    ((MvPolynomial σ R) ⧸ Ideal.span (Set.range (MvPolynomial.X (σ := σ) (R := R)))) ≃ₐ[R]
    ((MvPowerSeries σ R) ⧸ Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) := by
  sorry

def MvPowerSeries.evalAdicCompletion {S : Type*} [CommRing S] (I : Ideal S)
    (f : R →+* S) (g : σ → S) (rle : Set.range g ≤ I) :
    MvPowerSeries σ R →+* AdicCompletion I S := by
  sorry
