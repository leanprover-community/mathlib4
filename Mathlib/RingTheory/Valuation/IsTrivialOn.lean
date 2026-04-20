/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Valuation.Basic


/-!
# Basic lemmas on valuations that are trivial over a base ring

In what follows, we consider a `K`-algebra `L` and a valuation `v` over `L` which is trivial on `K`.

## Main results
* `valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`: Let `p` be a polynomial
over `K` evaluated at an element of `L`. We have the equality `v (p.aeval w) = v w ^ p.natDegree`.
* `Valuation.transcendental_of_lt_one`: If `y : L` is such that `y ≠ 0` and `v y < 1`,
then it is transcendental over `K`.
Note that this means that any non zero element of the maximal ideal of `v.valuationSubring` is
transcendental over `K`.
-/

@[expose] public section

variable (K : Type*) [CommRing K]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Field

variable (L : Type*) [Field L] [Algebra K L] {v : Valuation L Γ} [hv : v.IsTrivialOn K]

open Polynomial

/--
For a `K`-algebra `L` and a valuation `v` over `L` which is trivial on `K`.
If `y : L` is such that `y ≠ 0` and `v y < 1`, then it is transcendental over `K`. -/
theorem Valuation.transcendental_of_lt_one (y : L) (h0 : y ≠ 0)
    (hy : v y < 1) : Transcendental K y := by
  simp_all only [ne_eq, Transcendental]
  by_contra!
  rw [val_lt_one_iff _ (by contrapose! h0; aesop)] at hy
  replace ha : IsAlgebraic K y := .algebraMap this
  rw [← IsAlgebraic.inv_iff] at ha
  obtain ⟨p, hpnt, hp⟩ := ha
  suffices v y⁻¹ ^ p.natDegree = 0 by simp_all
  rw [← valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ _ hy] <;> simp_all

end Field
