/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.Star

/-!
# Star structures on bounded continuous functions

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

open Topology Bornology NNReal uniformity UniformConvergence RCLike BoundedContinuousFunction

open Set Filter Metric Function

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

namespace BoundedContinuousFunction

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of bounded
continuous functions from `α` to `β`, by using the star operation pointwise.

If `𝕜` is normed field and a ⋆-ring over which `β` is a normed algebra and a
star module, then the space of bounded continuous functions from `α` to `β`
is a star module.

If `β` is a ⋆-ring in addition to being a normed ⋆-group, then `α →ᵇ β`
inherits a ⋆-ring structure.

In summary, if `β` is a C⋆-algebra over `𝕜`, then so is `α →ᵇ β`; note that
completeness is guaranteed when `β` is complete (see
`BoundedContinuousFunction.complete`). -/


section NormedAddCommGroup

variable {𝕜 : Type*} [NormedField 𝕜] [StarRing 𝕜] [TopologicalSpace α] [SeminormedAddCommGroup β]
  [StarAddMonoid β] [NormedStarGroup β]

variable [NormedSpace 𝕜 β] [StarModule 𝕜 β]

instance instStarAddMonoid : StarAddMonoid (α →ᵇ β) where
  star f := f.comp star starNormedAddGroupHom.lipschitz
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

/-- The right-hand side of this equality can be parsed `star ∘ ⇑f` because of the
instance `Pi.instStarForAll`. Upon inspecting the goal, one sees `⊢ ↑(star f) = star ↑f`. -/
@[simp]
theorem coe_star (f : α →ᵇ β) : ⇑(star f) = star (⇑f) := rfl

@[simp]
theorem star_apply (f : α →ᵇ β) (x : α) : star f x = star (f x) := rfl

instance instNormedStarGroup : NormedStarGroup (α →ᵇ β) where
  norm_star_le f := by simp only [norm_eq, star_apply, norm_star, le_of_eq]

instance instStarModule : StarModule 𝕜 (α →ᵇ β) where
  star_smul k f := ext fun x => star_smul k (f x)

end NormedAddCommGroup

section CStarRing

variable [TopologicalSpace α]
variable [NonUnitalNormedRing β] [StarRing β]

instance instStarRing [NormedStarGroup β] : StarRing (α →ᵇ β) where
  __ := instStarAddMonoid
  star_mul f g := ext fun x ↦ star_mul (f x) (g x)

variable [CStarRing β]

instance instCStarRing : CStarRing (α →ᵇ β) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _), norm_le (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    exact norm_coe_le_norm (star f * f) x

end CStarRing

section NormedAlgebra

variable (𝕜 : Type*) [NormedField 𝕜] [TopologicalSpace α]
  [NormedRing β] [NormedAlgebra 𝕜 β] [StarAddMonoid β] [NormedStarGroup β]

/-- The ⋆-algebra-homomorphism forgetting that a bounded continuous function is bounded. -/
@[simps!]
def toContinuousMapStarₐ : (α →ᵇ β) →⋆ₐ[𝕜] C(α, β) := { toContinuousMapₐ 𝕜 with
  map_star' _ := rfl }

@[simp]
theorem coe_toContinuousMapStarₐ (f : α →ᵇ β) : (f.toContinuousMapStarₐ 𝕜 : α → β) = f := rfl

end NormedAlgebra

end BoundedContinuousFunction
