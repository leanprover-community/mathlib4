/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.Minpoly.Bounds

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# Baire spaces and algebraic normed extensions

A perfect algebraic normed extension of a complete nontrivially normed field is a Baire space
if and only if it is finite-dimensional over the base field, and is complete if and only if it
is finite-dimensional.

## Main results

* `minpoly.isClosed_setOf_natDegree_le`: degree sublevel sets are closed.
* `minpoly.bddAbove_natDegree_of_baireSpace`: a Baire algebraic normed extension has bounded
  degrees of minimal polynomials.
* `PerfectField.finiteDimensional_of_baireSpace`: a Baire algebraic normed extension into a
  perfect field is finite-dimensional.
* `baireSpace_iff_finiteDimensional`: a perfect algebraic normed extension is a Baire space
  if and only if it is finite-dimensional over the complete base field.
* `completeSpace_iff_finiteDimensional`: a perfect algebraic normed extension is complete
  if and only if it is finite-dimensional over the complete base field.

## Proof strategy

Finite linear independence is an open condition, so degree sublevel sets are closed. Baire's
theorem gives one such set with nonempty interior. Scaling and translation then give a global
degree bound, which implies finite-dimensionality when the extension field is perfect.

## Tags

Baire space, algebraic extension, perfect field, complete field, minimal polynomial
-/

public section

open IntermediateField Set

section NormedExtension

variable (K E : Type*) [NontriviallyNormedField K] [CompleteSpace K]
  [NormedField E] [NormedAlgebra K E] [Algebra.IsAlgebraic K E]

/-- In an algebraic normed extension of a complete field, the set of elements whose minimal
polynomial has degree at most `n` is closed. -/
theorem minpoly.isClosed_setOf_natDegree_le (n : ℕ) :
    IsClosed {x : E | (minpoly K x).natDegree ≤ n} := by
  convert (isOpen_setOfPred_linearIndependent (𝕜 := K) (E := E) (ι := Fin (n + 1))
    |>.preimage (continuous_pi fun i : Fin (n + 1) ↦
      continuous_pow (i : ℕ))).isClosed_compl using 1
  ext x
  simp [linearIndependent_pow_iff (Algebra.IsIntegral.isIntegral (R := K) x)]

/-- A Baire algebraic normed extension of a complete field has bounded degrees of minimal
polynomials. -/
theorem minpoly.bddAbove_natDegree_of_baireSpace [BaireSpace E] :
    BddAbove (Set.range fun x : E ↦ (minpoly K x).natDegree) := by
  obtain ⟨n, a, ha⟩ := nonempty_interior_of_iUnion_of_closed
    (minpoly.isClosed_setOf_natDegree_le K E) (by
      ext x
      simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨_, le_rfl⟩)
  refine ⟨(minpoly K a).natDegree * n, forall_mem_range.2 fun x ↦ ?_⟩
  -- Translate a small nonzero multiple of x into the interior of a degree sublevel set.
  obtain ⟨c, hc, hx⟩ := (dense_compl_singleton (0 : K)).exists_mem_open
    (isOpen_interior.preimage (by fun_prop : Continuous fun c : K ↦ a + c • x))
    ⟨0, by simpa using ha⟩
  refine (minpoly.natDegree_le_mul_of_mem_adjoin_pair
    (Algebra.IsIntegral.isIntegral a) (Algebra.IsIntegral.isIntegral (a + c • x)) ?_).trans
      (Nat.mul_le_mul_left _ (interior_subset hx))
  simpa [smul_smul, show c ≠ 0 from hc] using K⟮a, a + c • x⟯.smul_mem
    (K⟮a, a + c • x⟯.sub_mem (mem_adjoin_pair_right K a (a + c • x))
      (mem_adjoin_pair_left K a (a + c • x))) (x := c⁻¹)

variable [PerfectField E]

/-- A Baire algebraic normed extension of a complete field is finite-dimensional if the extension
field is perfect. -/
instance (priority := low) PerfectField.finiteDimensional_of_baireSpace
    [BaireSpace E] : FiniteDimensional K E :=
  PerfectField.finiteDimensional_of_bddAbove_natDegree_minpoly K E
    (minpoly.bddAbove_natDegree_of_baireSpace K E)

/-- A perfect algebraic normed extension of a complete field is a Baire space if and only if
it is finite-dimensional over the base field. -/
theorem baireSpace_iff_finiteDimensional :
    BaireSpace E ↔ FiniteDimensional K E :=
  ⟨fun _ ↦ PerfectField.finiteDimensional_of_baireSpace K E,
   fun _ ↦ have := FiniteDimensional.completeSpace K E; inferInstance⟩

/-- A perfect algebraic normed extension of a complete field is complete if and only if
it is finite-dimensional over the base field. -/
theorem completeSpace_iff_finiteDimensional :
    CompleteSpace E ↔ FiniteDimensional K E :=
  ⟨fun _ ↦ PerfectField.finiteDimensional_of_baireSpace K E,
   fun _ ↦ FiniteDimensional.completeSpace K E⟩

end NormedExtension
