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
conversely every quadratic extension is isomorphic to a `QuadraticAlgebra`.

## Main results

* `QuadraticAlgebra.instIsQuadraticExtension`: a `QuadraticAlgebra` is a quadratic extension;
* `Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra`: every quadratic extension of a
  commutative ring is isomorphic to some `QuadraticAlgebra R a b`.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommSemiring R] {a b : R}

/-- A quadratic algebra is a quadratic extension. -/
instance instIsQuadraticExtension [StrongRankCondition R] :
    Algebra.IsQuadraticExtension R (QuadraticAlgebra R a b) where
  finrank_eq_two' := finrank_eq_two a b

end QuadraticAlgebra

namespace Algebra

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
  · refine ⟨?_, ?_⟩
    · rw [QuadraticAlgebra.lift_injective_iff]
      have : ![(1 : A), e 1] = ⇑e := by ext i; fin_cases i <;> simp [he]
      rw [this]
      exact e.linearIndependent
    · rw [QuadraticAlgebra.lift_surjective_iff]
      refine Algebra.eq_top_iff.mpr fun x ↦ ?_
      rw [← e.sum_repr x, Fin.sum_univ_two, he]
      exact add_mem (Subalgebra.smul_mem _ (one_mem _) _)
        (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton R (e 1)) _)

end Algebra
