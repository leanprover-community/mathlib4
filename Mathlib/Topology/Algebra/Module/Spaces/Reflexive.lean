/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Reflexive topological vector spaces

A topological vector space `E` over a normed field `𝕜` is reflexive if the canonical map
`StrongDual.inclusionInDoubleDualₗ 𝕜 E` from `E` to its strong bidual
`StrongDual 𝕜 (StrongDual 𝕜 E)`, which sends `x` to the evaluation at `x`, is a homeomorphism.
The strong dual carries the topology of uniform convergence on bounded sets.

This is a topological notion, different from the algebraic notion `Module.IsReflexive`, which asks
for the canonical map to the algebraic double dual `Module.Dual 𝕜 (Module.Dual 𝕜 E)` to be
bijective. For example, an infinite-dimensional Hilbert space is reflexive in the topological sense
but not in the algebraic sense. A finite-dimensional normed space is reflexive in both senses: see
`FiniteDimensional.isReflexive` and `Module.instIsReflexiveOfFiniteOfProjective`.

For normed spaces, see `Mathlib.Analysis.Normed.Module.DoubleDual`.

## Main definitions

* `StrongDual.inclusionInDoubleDualₗ`: the canonical map from a topological vector space to its
  strong bidual, as a linear map.
* `StrongDual.IsReflexive`: a topological vector space is reflexive if
  `StrongDual.inclusionInDoubleDualₗ` is a homeomorphism.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]
-/

@[expose] public section

namespace StrongDual

variable (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E]

/-- The canonical map from a topological vector space `E` to its strong bidual, which sends `x` to
the evaluation at `x`, as a linear map. This is the topological analogue of `Module.Dual.eval`.
For a normed space, this is the linear map underlying `NormedSpace.inclusionInDoubleDual`. -/
def inclusionInDoubleDualₗ : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  ContinuousLinearMap.applyₗ 𝕜 (.id 𝕜)

variable {𝕜 E} in
@[simp]
lemma inclusionInDoubleDualₗ_apply (x : E) (f : StrongDual 𝕜 E) :
    inclusionInDoubleDualₗ 𝕜 E x f = f x := rfl

/-- A topological vector space `E` is reflexive if the canonical map
`StrongDual.inclusionInDoubleDualₗ 𝕜 E` from `E` to its strong bidual is a homeomorphism.

This is not the algebraic notion `Module.IsReflexive`, which concerns the algebraic double dual. -/
class IsReflexive : Prop where
  isHomeomorph_inclusionInDoubleDualₗ : IsHomeomorph (inclusionInDoubleDualₗ 𝕜 E)

end StrongDual
