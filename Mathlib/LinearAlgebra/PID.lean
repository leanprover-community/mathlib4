/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Linear maps of modules with coefficients in a principal ideal domain

Since a submodule of a free module over a PID is free, certain constructions which are often
developed only for vector spaces may be generalised to any module with coefficients in a PID.

This file is a location for such results and exists to avoid making large parts of the linear
algebra import hierarchy have to depend on the theory of PIDs.

## Main results:
 * `LinearMap.trace_restrict_eq_of_forall_mem`

-/

open BigOperators

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Free R M]

/-- If a linear endomorphism of a (finite, free) module `M` takes values in a submodule `p ⊆ M`,
then the trace of its restriction to `p` is equal to its trace on `M`. -/
lemma trace_restrict_eq_of_forall_mem [IsDomain R] [IsPrincipalIdealRing R]
    (p : Submodule R M) (f : M →ₗ[R] M)
    (hf : ∀ x, f x ∈ p) (hf' : ∀ x ∈ p, f x ∈ p := fun x _ ↦ hf x) :
    trace R p (f.restrict hf') = trace R M f := by
  let ι := Module.Free.ChooseBasisIndex R M
  -- ⊢ ↑(trace R { x // x ∈ p }) (restrict f hf') = ↑(trace R M) f
  obtain ⟨n, snf : Basis.SmithNormalForm p ι n⟩ := p.smithNormalForm (Module.Free.chooseBasis R M)
  -- ⊢ ↑(trace R { x // x ∈ p }) (restrict f hf') = ↑(trace R M) f
  rw [trace_eq_matrix_trace R snf.bM, trace_eq_matrix_trace R snf.bN]
  -- ⊢ Matrix.trace (↑(toMatrix snf.bN snf.bN) (restrict f hf')) = Matrix.trace (↑( …
  set A : Matrix (Fin n) (Fin n) R := toMatrix snf.bN snf.bN (f.restrict hf')
  -- ⊢ Matrix.trace A = Matrix.trace (↑(toMatrix snf.bM snf.bM) f)
  set B : Matrix ι ι R := toMatrix snf.bM snf.bM f
  -- ⊢ Matrix.trace A = Matrix.trace B
  have aux : ∀ i, B i i ≠ 0 → i ∈ Set.range snf.f := fun i hi ↦ by
    contrapose! hi; exact snf.repr_eq_zero_of_nmem_range ⟨_, (hf _)⟩ hi
  change ∑ i, A i i = ∑ i, B i i
  -- ⊢ ∑ i : Fin n, A i i = ∑ i : ι, B i i
  rw [← Finset.sum_filter_of_ne (p := fun j ↦ j ∈ Set.range snf.f) (by simpa using aux)]
  -- ⊢ ∑ i : Fin n, A i i = ∑ x in Finset.filter (fun j => j ∈ Set.range ↑snf.f) Fi …
  simp
  -- 🎉 no goals

end LinearMap
