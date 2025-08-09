/-
Copyright (c) 2025 Daniel Figueroa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Figueroa
-/
import Mathlib.Dynamics.Flow

/-!
# Topological transitivity of a flow

This file contains results about topologically transitive flows.

## Main results

* `Flow.IsTopologicallyTransitive.of_isFactorOf`: a factor of a topologically transitive flow is
  topologically transitive
-/

namespace Flow

variable {τ : Type*} [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]
  {α : Type*} [TopologicalSpace α] (ϕ : Flow τ α)
  {β : Type*} [TopologicalSpace β] (ψ : Flow τ β)

/-- A flow `ϕ : Flow τ α` is said to be *topologically transitive* if there exists `x : α` whose
orbit `ϕ.orbit x` is dense in `α`. -/
def IsTopologicallyTransitive (ϕ : Flow τ α) : Prop :=
  ∃ x : α, Dense (ϕ.orbit x)

variable {ϕ ψ}

/-- If the continuous map `π : α → β` is a semiconjugacy from flow `ϕ` to flow `ψ` and `ϕ` is
topologically transitive, then `ψ` is topologically transitive. -/
lemma IsTopologicallyTransitive.of_semiconjugacy
    {π : ContinuousMap α β} (hπ : IsSemiconjugacy π ϕ ψ)
    (hϕ : IsTopologicallyTransitive ϕ) : IsTopologicallyTransitive ψ := by
  obtain ⟨x, hx⟩ := hϕ
  refine ⟨π x, dense_iff_inter_open.mpr (fun U hUo hUn ↦ ?_)⟩
  obtain ⟨_, hzU, t, htxz⟩ := dense_iff_inter_open.mp hx (π ⁻¹' U)
    (hUo.preimage π.continuous_toFun) (Set.Nonempty.preimage hUn hπ.surj)
  exact ⟨ψ t (π x), by rwa [← hπ.semiconj t x, congrArg π htxz], ⟨t, rfl⟩⟩

/-- A factor of a topologically transitive flow is topologically transitive. -/
theorem IsTopologicallyTransitive.of_isFactorOf (hψ : ψ.IsFactorOf ϕ)
    (h : IsTopologicallyTransitive ϕ) : IsTopologicallyTransitive ψ :=
  h.of_semiconjugacy hψ.choose_spec

end Flow
