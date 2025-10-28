/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Path
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.ContinuousMap.Interval

/-!
# Paths in uniform spaces

In this file we define a `UniformSpace` structure on `Path`s
between two points in a uniform space
and prove that various functions associated with `Path`s are uniformly continuous.

The uniform space structure is induced from the space of continuous maps `C(I, X)`,
and corresponds to uniform convergence of paths on `I`, see `Path.hasBasis_uniformity`.
-/

open scoped unitInterval Topology Uniformity

variable {X : Type*} [UniformSpace X] {x y z : X}

namespace Path

instance instUniformSpace : UniformSpace (Path x y) :=
  .comap ((↑) : _ → C(I, X)) ContinuousMap.compactConvergenceUniformSpace

theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Path x y → C(I, X)) where
  comap_uniformity := rfl
  injective := ContinuousMap.coe_injective'

theorem uniformContinuous (γ : Path x y) : UniformContinuous γ :=
  CompactSpace.uniformContinuous_of_continuous <| map_continuous _

/-- Given a path `γ`, it extension to the real line `γ.extend : C(ℝ, X)`
is a uniformly continuous function. -/
theorem uniformContinuous_extend (γ : Path x y) : UniformContinuous γ.extend :=
  γ.uniformContinuous.comp <| LipschitzWith.projIcc _ |>.uniformContinuous

/-- The function sending a path `γ` to its extension `γ.extend : ℝ → X`
is uniformly continuous in `γ`. -/
theorem uniformContinuous_extend_left : UniformContinuous (Path.extend : Path x y → C(ℝ, X)) :=
  ContinuousMap.projIccCM.uniformContinuous_comp_left.comp isUniformEmbedding_coe.uniformContinuous

/-- If `{U i | p i}` form a basis of entourages of `X`,
then the entourages `{V i | p i}`, `V i = {(γ₁, γ₂) | ∀ t, (γ₁ t, γ₂ t) ∈ U i}`,
form a basis of entourages of paths between `x` and `y`. -/
theorem _root_.Filter.HasBasis.uniformityPath {ι : Sort*} {p : ι → Prop} {U : ι → Set (X × X)}
    (hU : (𝓤 X).HasBasis p U) :
    (𝓤 (Path x y)).HasBasis p fun i ↦ {γ | ∀ t, (γ.1 t, γ.2 t) ∈ U i} :=
  hU.compactConvergenceUniformity_of_compact.comap _

theorem hasBasis_uniformity :
    (𝓤 (Path x y)).HasBasis (· ∈ 𝓤 X) ({γ | ∀ t, (γ.1 t, γ.2 t) ∈ ·}) :=
  (𝓤 X).basis_sets.uniformityPath

theorem uniformContinuous_symm : UniformContinuous (Path.symm : Path x y → Path y x) :=
  hasBasis_uniformity.uniformContinuous_iff hasBasis_uniformity |>.mpr fun U hU ↦
    ⟨U, hU, fun _ _ h x ↦ h (σ x)⟩

/-- The function `Path.trans` that concatenates two paths `γ₁ : Path x y` and `γ₂ : Path y z`
is uniformly continuous in `(γ₁, γ₂)`. -/
theorem uniformContinuous_trans :
    UniformContinuous (Path.trans : Path x y → Path y z → Path x z).uncurry :=
  hasBasis_uniformity.uniformity_prod hasBasis_uniformity
    |>.uniformContinuous_iff hasBasis_uniformity |>.mpr fun U hU ↦
      ⟨(U, U), ⟨hU, hU⟩, fun ⟨_, _⟩ ⟨_, _⟩ ⟨h₁, h₂⟩ t ↦ by
        by_cases ht : (t : ℝ) ≤ 2⁻¹ <;> simp [Path.trans_apply, ht, h₁ _, h₂ _]⟩

/-- The space of paths between two points in a complete uniform space
is a complete uniform space. -/
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (Path x y) :=
  isUniformEmbedding_coe.completeSpace <| by simpa [Set.EqOn, range_coe]
    using ContinuousMap.isComplete_setOf_eqOn (Function.update (fun _ : I ↦ y) 0 x) {0, 1}

end Path
