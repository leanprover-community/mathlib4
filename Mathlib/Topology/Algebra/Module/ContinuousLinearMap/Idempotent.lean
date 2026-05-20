/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Idempotent continuous linear maps
-/

@[expose] public section

namespace ContinuousLinearMap

@[grind =]
theorem isIdempotentElem_toLinearMap_iff {R M : Type*} [Semiring R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] {f : M →L[R] M} :
    IsIdempotentElem f.toLinearMap ↔ IsIdempotentElem f := by
  simp only [IsIdempotentElem, Module.End.mul_eq_comp, ← coe_comp, mul_def, coe_inj]

alias ⟨_, IsIdempotentElem.toLinearMap⟩ := isIdempotentElem_toLinearMap_iff

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

/-- Idempotent operators are equal iff their range and kernels are. -/
lemma IsIdempotentElem.ext_iff {p q : M →L[R] M}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p = q ↔ p.range = q.range ∧ p.ker = q.ker := by
  simpa using LinearMap.IsIdempotentElem.ext_iff hp.toLinearMap hq.toLinearMap

alias ⟨_, IsIdempotentElem.ext⟩ := IsIdempotentElem.ext_iff

/-- `range f` is invariant under `T` if and only if `f ∘L T ∘L f = T ∘L f`,
for idempotent `f`. -/
lemma IsIdempotentElem.range_mem_invtSubmodule_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    f.range ∈ Module.End.invtSubmodule T ↔ f ∘L T ∘L f = T ∘L f := by
  simpa [← ContinuousLinearMap.coe_comp] using
    LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨IsIdempotentElem.conj_eq_of_range_mem_invtSubmodule,
  IsIdempotentElem.range_mem_invtSubmodule⟩ := IsIdempotentElem.range_mem_invtSubmodule_iff

/-- `ker f` is invariant under `T` if and only if `f ∘L T ∘L f = f ∘L T`,
for idempotent `f`. -/
lemma IsIdempotentElem.ker_mem_invtSubmodule_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    f.ker ∈ Module.End.invtSubmodule T ↔ f ∘L T ∘L f = f ∘L T := by
  simpa [← ContinuousLinearMap.coe_comp] using
    LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨IsIdempotentElem.conj_eq_of_ker_mem_invtSubmodule,
  IsIdempotentElem.ker_mem_invtSubmodule⟩ := IsIdempotentElem.ker_mem_invtSubmodule_iff

/-- An idempotent operator `f` commutes with `T` if and only if
both `range f` and `ker f` are invariant under `T`. -/
lemma IsIdempotentElem.commute_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    Commute f T ↔ (f.range ∈ Module.End.invtSubmodule T ∧ f.ker ∈ Module.End.invtSubmodule T) := by
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← coe_comp] using
    LinearMap.IsIdempotentElem.commute_iff (T := T) hf.toLinearMap

variable [IsTopologicalAddGroup M]

/-- An idempotent operator `f` commutes with a unit operator `T` if and only if
`T (range f) = range f` and `T (ker f) = ker f`. -/
theorem IsIdempotentElem.commute_iff_of_isUnit {f T : M →L[R] M} (hT : IsUnit T)
    (hf : IsIdempotentElem f) :
    Commute f T ↔ f.range.map (T : M →ₗ[R] M) = f.range ∧ f.ker.map (T : M →ₗ[R] M) = f.ker := by
  have := hT.map ContinuousLinearMap.toLinearMapRingHom
  lift T to (M →L[R] M)ˣ using hT
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← ContinuousLinearMap.coe_comp] using
    LinearMap.IsIdempotentElem.commute_iff_of_isUnit this hf.toLinearMap

@[deprecated (since := "2025-12-27")] alias IsIdempotentElem.range_eq_ker :=
  LinearMap.IsIdempotentElem.range_eq_ker
@[deprecated (since := "2025-12-27")] alias IsIdempotentElem.ker_eq_range :=
  LinearMap.IsIdempotentElem.ker_eq_range

theorem IsIdempotentElem.isClosed_range [T1Space M] {p : M →L[R] M}
    (hp : IsIdempotentElem p) : IsClosed (p.range : Set M) :=
  LinearMap.IsIdempotentElem.range_eq_ker hp.toLinearMap ▸ isClosed_ker (.id R M - p)

end ContinuousLinearMap
