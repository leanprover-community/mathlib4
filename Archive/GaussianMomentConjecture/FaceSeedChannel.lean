/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ConstantTermRelations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

/-!
# Extracting a concrete balanced channel from a nonzero face seed

The DvdK input supplies nonvanishing of a finite constant-term sum.  The
height-normalization layer needs an actual multiplicity vector on that face
as its reference channel.  This file makes the elementary finite-sum
extraction explicit.
-/

open MvPolynomial Finset

namespace GMC2.FaceSeedChannel

/-- A nonzero evaluated constant-term relation contains a nonzero balanced
summand.  In particular, it supplies a concrete mass-`m` reference channel
whose total charge is zero. -/
theorem exists_nonzero_balanced_channel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ) (m : ℕ)
    (hseed : MvPolynomial.aeval c
      (GMC2.ConstantTermRelations.constantTermRelation q m) ≠ 0) :
    ∃ r : ι → ℕ,
      r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m ∧
      GMC2.ConstantTermRelations.totalCharge q r = 0 ∧
      (Nat.multinomial Finset.univ r : ℂ) * ∏ i, c i ^ r i ≠ 0 := by
  rw [GMC2.ConstantTermRelations.aeval_constantTermRelation] at hseed
  obtain ⟨r, hr, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hseed
  by_cases hbalanced : GMC2.ConstantTermRelations.totalCharge q r = 0
  · refine ⟨r, hr, hbalanced, ?_⟩
    simpa only [if_pos hbalanced] using hterm
  · simp only [if_neg hbalanced] at hterm
    exact (hterm rfl).elim

end GMC2.FaceSeedChannel
