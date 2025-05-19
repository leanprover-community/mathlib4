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

/-- Extension of a path to the real line is a uniformly continuous function. -/
theorem uniformContinuous_extend (γ : Path x y) : UniformContinuous γ.extend :=
  γ.uniformContinuous.comp <| LipschitzWith.projIcc _ |>.uniformContinuous

/-- Extension of a path to the real line is uniformly continuous in the path argument. -/
theorem uniformContinuous_extend_left : UniformContinuous (Path.extend : Path x y → _) :=
  have : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩
  ContinuousMap.projIccCM.uniformContinuous_comp_left.comp isUniformEmbedding_coe.uniformContinuous

theorem _root_.Filter.HasBasis.uniformityPath {ι : Sort*} {p : ι → Prop} {U : ι → Set (X × X)}
    (hU : (𝓤 X).HasBasis p U) :
    (𝓤 (Path x y)).HasBasis p fun i ↦ {γ | ∀ t, (γ.1 t, γ.2 t) ∈ U i} :=
  hU.compactConvergenceUniformity_of_compact.comap _

theorem hasBasis_uniformity :
    (𝓤 (Path x y)).HasBasis (· ∈ 𝓤 X) ({γ | ∀ t, (γ.1 t, γ.2 t) ∈ ·}) :=
  (𝓤 X).basis_sets.uniformityPath

theorem uniformContinuous_symm : UniformContinuous (Path.symm : Path x y → _) :=
  hasBasis_uniformity.uniformContinuous_iff hasBasis_uniformity |>.mpr fun U hU ↦
    ⟨U, hU, fun _ _ h x ↦ h (σ x)⟩

theorem uniformContinuous_trans :
    UniformContinuous (Path.trans : Path x y → Path y z → _).uncurry :=
  hasBasis_uniformity.uniformity_prod hasBasis_uniformity
    |>.uniformContinuous_iff hasBasis_uniformity |>.mpr fun U hU ↦
      ⟨(U, U), ⟨hU, hU⟩, fun ⟨_, _⟩ ⟨_, _⟩ ⟨h₁, h₂⟩ t ↦ by
        by_cases ht : (t : ℝ) ≤ 2⁻¹ <;> simp [Path.trans_apply, ht, h₁ _, h₂ _]⟩

instance instCompleteSpace [CompleteSpace X] : CompleteSpace (Path x y) :=
  isUniformEmbedding_coe.completeSpace <| by simpa [Set.EqOn, range_coe]
    using ContinuousMap.isComplete_setOf_eqOn (Function.update (fun _ : I ↦ y) 0 x) {0, 1}

end Path
