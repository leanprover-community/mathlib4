/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Conformal Linear Maps

A continuous linear map between `R`-normed spaces `X` and `Y` `IsConformalMap` if it is
a nonzero multiple of a linear isometry.

## Main definitions

* `IsConformalMap`: the main definition of conformal linear maps

## Main results

* The conformality of the composition of two conformal linear maps, the identity map
  and multiplications by nonzero constants as continuous linear maps
* `isConformalMap_of_subsingleton`: all continuous linear maps on singleton spaces are conformal

See `Analysis.InnerProductSpace.ConformalLinearMap` for
* `isConformalMap_iff`: a map between inner product spaces is conformal
  iff it preserves inner products up to a fixed scalar factor.


## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
-/


noncomputable section

open Function LinearIsometry ContinuousLinearMap

/-- A continuous linear map `f'` is said to be conformal if it's
a nonzero multiple of a linear isometry. -/
def IsConformalMap {R : Type*} {X Y : Type*} [NormedField R] [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] [NormedSpace R X] [NormedSpace R Y] (f' : X →L[R] Y) :=
  ∃ c ≠ (0 : R), ∃ li : X →ₗᵢ[R] Y, f' = c • li.toContinuousLinearMap

variable {R M N G M' : Type*} [NormedField R] [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  [SeminormedAddCommGroup G] [NormedSpace R M] [NormedSpace R N] [NormedSpace R G]
  [NormedAddCommGroup M'] [NormedSpace R M'] {f : M →L[R] N} {g : N →L[R] G} {c : R}

theorem isConformalMap_id : IsConformalMap (.id R M) :=
  ⟨1, one_ne_zero, id, by simp⟩

theorem IsConformalMap.smul (hf : IsConformalMap f) {c : R} (hc : c ≠ 0) :
    IsConformalMap (c • f) := by
  rcases hf with ⟨c', hc', li, rfl⟩
  exact ⟨c * c', mul_ne_zero hc hc', li, smul_smul _ _ _⟩

theorem isConformalMap_const_smul (hc : c ≠ 0) : IsConformalMap (c • .id R M) :=
  isConformalMap_id.smul hc

protected theorem LinearIsometry.isConformalMap (f' : M →ₗᵢ[R] N) :
    IsConformalMap f'.toContinuousLinearMap :=
  ⟨1, one_ne_zero, f', (one_smul _ _).symm⟩

@[nontriviality]
theorem isConformalMap_of_subsingleton [Subsingleton M] (f' : M →L[R] N) : IsConformalMap f' :=
  ⟨1, one_ne_zero, ⟨0, fun x => by simp [Subsingleton.elim x 0]⟩, Subsingleton.elim _ _⟩

namespace IsConformalMap

theorem comp (hg : IsConformalMap g) (hf : IsConformalMap f) : IsConformalMap (g.comp f) := by
  rcases hf with ⟨cf, hcf, lif, rfl⟩
  rcases hg with ⟨cg, hcg, lig, rfl⟩
  refine ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, ?_⟩
  rw [smul_comp, comp_smul, mul_smul]
  rfl

protected theorem injective {f : M' →L[R] N} (h : IsConformalMap f) : Function.Injective f := by
  rcases h with ⟨c, hc, li, rfl⟩
  exact (smul_right_injective _ hc).comp li.injective

theorem ne_zero [Nontrivial M'] {f' : M' →L[R] N} (hf' : IsConformalMap f') : f' ≠ 0 := by
  rintro rfl
  rcases exists_ne (0 : M') with ⟨a, ha⟩
  exact ha (hf'.injective rfl)

end IsConformalMap
