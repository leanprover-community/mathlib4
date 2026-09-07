/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Idempotent continuous linear maps

In this file, we study the idempotent elements (`IsIdempotentElem`) of the ring `M →L[R] M` of
continuous endomorphisms of a topological `R`-module `M`.

## Main statements

* `ContinuousLinearMap.isIdempotentElem_toLinearMap_iff`: `T` is idempotent as an element of
  `M →L[R] M` if and only if it is such as an element of `M →ₗ[R] M`;
* `ContinuousLinearMap.IsIdempotentElem.ext_iff`: idempotent elements of `M →L[R] M` are determined
  by their range and kernel;
* `ContinuousLinearMap.IsIdempotentElem.commute_iff`: a continuous linear map `S` commutes with
  an idempotent `T` if and only if the range and kernel of `T` are `S`-invariant;
* `ContinuousLinearMap.IsIdempotentElem.isCLosed_range`: an idempotent continuous linear map
  has closed range.

Further results can be found in the `Mathlib/Topology/Algebra/Module/Complement.lean` module, where
we show that idempotent elements of `M →L[R] M` are precisely the projections associated to
topological complement submodules.
-/

@[expose] public section

namespace ContinuousLinearMap

@[grind =]
theorem isIdempotentElem_toLinearMap_iff {R M : Type*} [Semiring R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] {f : M →L[R] M} :
    IsIdempotentElem f.toLinearMap ↔ IsIdempotentElem f := by
  simp only [IsIdempotentElem, Module.End.mul_eq_comp, ← toLinearMap_comp, mul_def, coe_inj]

alias ⟨_, IsIdempotentElem.toLinearMap⟩ := isIdempotentElem_toLinearMap_iff

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

namespace IsIdempotentElem

/-- Idempotent operators are equal iff their range and kernels are. -/
lemma ext_iff {p q : M →L[R] M}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p = q ↔ p.range = q.range ∧ p.ker = q.ker := by
  simpa using LinearMap.IsIdempotentElem.ext_iff hp.toLinearMap hq.toLinearMap

alias ⟨_, ext⟩ := IsIdempotentElem.ext_iff

/-- `range f` is invariant under `T` if and only if `f ∘L T ∘L f = T ∘L f`,
for idempotent `f`. -/
lemma range_mem_invtSubmodule_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    f.range ∈ Module.End.invtSubmodule T ↔ f ∘L T ∘L f = T ∘L f := by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_range_mem_invtSubmodule,
  range_mem_invtSubmodule⟩ := IsIdempotentElem.range_mem_invtSubmodule_iff

/-- `ker f` is invariant under `T` if and only if `f ∘L T ∘L f = f ∘L T`,
for idempotent `f`. -/
lemma ker_mem_invtSubmodule_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    f.ker ∈ Module.End.invtSubmodule T ↔ f ∘L T ∘L f = f ∘L T := by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_ker_mem_invtSubmodule,
  ker_mem_invtSubmodule⟩ := IsIdempotentElem.ker_mem_invtSubmodule_iff

/-- An idempotent operator `f` commutes with `T` if and only if
both `range f` and `ker f` are invariant under `T`. -/
lemma commute_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    Commute f T ↔ (f.range ∈ Module.End.invtSubmodule T ∧ f.ker ∈ Module.End.invtSubmodule T) := by
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff (T := T) hf.toLinearMap

variable [IsTopologicalAddGroup M]

/-- An idempotent operator `f` commutes with a unit operator `T` if and only if
`T (range f) = range f` and `T (ker f) = ker f`. -/
theorem commute_iff_of_isUnit {f T : M →L[R] M} (hT : IsUnit T)
    (hf : IsIdempotentElem f) :
    Commute f T ↔ f.range.map (T : M →ₗ[R] M) = f.range ∧ f.ker.map (T : M →ₗ[R] M) = f.ker := by
  have := hT.map ContinuousLinearMap.toLinearMapRingHom
  lift T to (M →L[R] M)ˣ using hT
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff_of_isUnit this hf.toLinearMap

@[deprecated (since := "2025-12-27")] alias range_eq_ker :=
  LinearMap.IsIdempotentElem.range_eq_ker
@[deprecated (since := "2025-12-27")] alias ker_eq_range :=
  LinearMap.IsIdempotentElem.ker_eq_range

theorem isClosed_range [T1Space M] {p : M →L[R] M}
    (hp : IsIdempotentElem p) : IsClosed (p.range : Set M) :=
  LinearMap.IsIdempotentElem.range_eq_ker hp.toLinearMap ▸ isClosed_ker (.id R M - p)

end IsIdempotentElem

end ContinuousLinearMap
