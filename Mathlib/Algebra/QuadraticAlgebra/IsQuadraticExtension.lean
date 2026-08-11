/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.Trace.Basic

/-!
# Quadratic algebras and quadratic extensions

This file relates the concrete construction `QuadraticAlgebra R a b` to the predicate
`Algebra.IsQuadraticExtension`: a `QuadraticAlgebra` is a quadratic extension of `R`, and
conversely every commutative quadratic extension is isomorphic to a `QuadraticAlgebra`.

## Main results

* `QuadraticAlgebra.instIsQuadraticExtension`: a `QuadraticAlgebra` is a quadratic extension;
* `Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra`: every commutative quadratic
  extension is isomorphic to some `QuadraticAlgebra R a b`.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommSemiring R] {a b : R}

/-- A quadratic algebra is a quadratic extension. -/
instance instIsQuadraticExtension [StrongRankCondition R] :
    Algebra.IsQuadraticExtension R (QuadraticAlgebra R a b) where
  finrank_eq_two' := finrank_eq_two a b

/-- A `QuadraticAlgebra ℚ a b` which is a field is a quadratic extension of `ℚ`
(for its field `Algebra ℚ`-structure). -/
-- Needed in addition to `instIsQuadraticExtension`: when `QuadraticAlgebra ℚ a b` is a field, its
-- `Algebra ℚ`-structure is inferred as `algebraRat`, which is not defeq to `instAlgebra` (they
-- agree only up to the `Algebra ℚ` subsingleton), so the instance above no longer applies.
instance instIsQuadraticExtensionRat {a b : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    Algebra.IsQuadraticExtension ℚ (QuadraticAlgebra ℚ a b) where
  finrank_eq_two' := finrank_eq_two a b

end QuadraticAlgebra

namespace Algebra

open QuadraticAlgebra

variable {R A : Type*} [CommRing R] [StrongRankCondition R] [CommRing A] [Algebra R A]
  [IsQuadraticExtension R A]

/-- Every quadratic extension `A / R` is isomorphic to `QuadraticAlgebra R a b` for some `a, b`. -/
theorem IsQuadraticExtension.exists_algEquiv_quadraticAlgebra :
    ∃ (a b : R), Nonempty (A ≃ₐ[R] QuadraticAlgebra R a b) := by
  have : Nontrivial R := nontrivial_of_invariantBasisNumber R
  have : Nontrivial A := Module.nontrivial_of_finrank_pos
    (by rw [IsQuadraticExtension.finrank_eq_two R A]; norm_num)
  obtain ⟨e, he⟩ := Module.Free.exists_basis_apply_zero_eq
    (IsQuadraticExtension.finrank_eq_two R A) Module.Free.exists_linearMap_apply_one_eq_one
  refine ⟨-Algebra.norm R (e 1), Algebra.trace R A (e 1),
    ⟨(AlgEquiv.ofBijective (QuadraticAlgebra.lift ⟨(e 1), ?_⟩) ?_).symm⟩⟩
  · simpa [← sq, ← Algebra.algebraMap_eq_smul_one, neg_add_eq_sub]
      using IsQuadraticExtension.sq_eq_trace_smul_sub_norm R (e 1)
  · refine ⟨(lift_injective_iff _).mpr ?_, (lift_surjective_iff _).mpr ?_⟩
    · rw [show ![1, e 1] = e by ext i; fin_cases i <;> simp [he]]
      exact e.linearIndependent
    · rw [← Algebra.toSubmodule_eq_top, ← top_le_iff, ← e.span_eq, Submodule.span_le]
      simp [Set.range_subset_iff, he]

end Algebra
