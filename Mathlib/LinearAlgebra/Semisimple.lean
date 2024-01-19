/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Order.CompleteSublattice
import Mathlib.Data.Polynomial.Module
import Mathlib.RingTheory.SimpleModule

/-!
# Semisimple linear endomorphisms

TODO explain

-/

open Set Function Module Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace LinearMap -- Or should we use `Module.End`?

variable (f : M →ₗ[R] M)

/-- A linear endomorphism of an `R`-module `M` is called semisimple if the induced `R[X]`-module
structure on `M` is semisimple. This is equivalent to saying that every `f`-invariant `R`-submodule
of `M` has an `f`-invariant complement: see `LinearMap.isSemisimple_iff`. -/
protected abbrev IsSemisimple := IsSemisimpleModule R[X] (AEval' f)

lemma isSemisimple_iff :
    f.IsSemisimple ↔ ∀ p : Submodule R M, p ≤ p.comap f → ∃ q, q ≤ q.comap f ∧ IsCompl p q := by
  set s := (AEval.comapSubmodule R M f).range
  have h : s = {p : Submodule R M | p ≤ p.comap f} := AEval.range_comapSubmodule R M f
  let e := CompleteLatticeHom.toOrderIsoRangeOfInjective _ (AEval.injective_comapSubmodule R M f)
  simp_rw [LinearMap.IsSemisimple, IsSemisimpleModule, e.complementedLattice_iff,
    s.isComplemented_iff, ← SetLike.mem_coe, h, mem_setOf_eq]

-- TODO Zero map, identity are semisimple (when `IsSemisimpleModule R M`, e.g., over division ring).

-- TODO generalized eigenspaces are eigenspaces + minpoly characterisation

end LinearMap
