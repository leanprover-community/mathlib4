/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Some lemmas about linear functionals on division rings

This file proves some results on linear functionals on division semirings.

## Main results

* `LinearMap.surjective_iff_ne_zero`: a linear functional `f` is surjective iff `f ≠ 0`.
* `LinearMap.range_smulRight_apply`: for a nonzero linear functional `f` and element `x`,
the range of `f.smulRight x` is the span of the set `{x}`.
-/

namespace LinearMap
variable {R M M₁ : Type*} [AddCommMonoid M] [AddCommMonoid M₁]

theorem surjective_iff_ne_zero [DivisionSemiring R] [Module R M] {f : M →ₗ[R] R} :
    Function.Surjective f ↔ f ≠ 0 := by
  refine ⟨ne_zero_of_surjective, fun hf z ↦ ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by simpa [Ne, LinearMap.ext_iff] using hf
  exact ⟨(z * (f y)⁻¹) • y, by simp [hy]⟩

protected alias ⟨_, surjective⟩ := surjective_iff_ne_zero

theorem range_smulRight_apply_of_surjective [Semiring R] [Module R M] [Module R M₁]
    {f : M →ₗ[R] R} (hf : Function.Surjective f) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} := Submodule.ext fun z ↦ by
  simp_rw [mem_range, smulRight_apply, Submodule.mem_span_singleton]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨f w, hw ▸ rfl⟩, fun ⟨w, hw⟩ ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hf w
  exact ⟨y, hw⟩

theorem range_smulRight_apply [DivisionSemiring R] [Module R M] [Module R M₁]
    {f : M →ₗ[R] R} (hf : f ≠ 0) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} :=
  range_smulRight_apply_of_surjective (f.surjective hf) x

end LinearMap
