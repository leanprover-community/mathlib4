/-
Copyright (c) 2025 Yueqing Feng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueqing Feng, Lucy Horowitz
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Constructions

/-!
# Main definitions

- `ZeroDimModel`: The model space `Fin 0 → ℝ` for zero-dimensional manifolds.
- `zeroDimManifoldStructure`: Construction of a manifold structure on any discrete countable space.

# Main results

- `exists_chart_at_zeroDim`: Every point in a zero-dimensional manifold has a chart neighborhood
  homeomorphic to the model space.
- `zeroDimManifold_discrete`: Any manifold modeled on `ZeroDimModel` has discrete topology.
- `zeroDimManifold_countable`: Any second-countable zero-dimensional manifold is countable.
-/

open Topology Set

noncomputable section

/-- The model space `Fin 0 → ℝ` for zero-dimensional manifolds. -/

def ZeroDimModel : Type := (Fin 0 → ℝ)
    deriving TopologicalSpace, Unique, Subsingleton

section ZeroDimCharts

variable {M : Type} [TopologicalSpace M] [ChartedSpace ZeroDimModel M]

/-- Every point in a zero-dimensional manifold has a chart neighborhood homeomorphic to the
model space. -/

lemma exists_chart_at (x : M) : ∃ (U : Set M) (_ : U ≃ₜ ZeroDimModel),
  IsOpen U ∧ x ∈ U := by
  let chart := chartAt ZeroDimModel x
  use chart.source
  let g := PartialHomeomorph.toHomeomorphSourceTarget chart
  let y : Unique chart.target := {
    default := ⟨chart x, by exact mem_chart_target ZeroDimModel x⟩
    uniq := by
      intro a
      ext
      apply Subsingleton.elim
  }
  let h : chart.target ≃ₜ ZeroDimModel := Homeomorph.homeomorphOfUnique chart.target ZeroDimModel

  let φ := g.trans h
  constructor
  · constructor
    · exact chart.open_source
    · exact ChartedSpace.mem_chart_source x
  · exact φ

instance : DiscreteTopology ZeroDimModel := Subsingleton.discreteTopology

/-- Any manifold modeled on the zero-dimensional space has discrete topology. -/

theorem zero_dim_manifold_discrete : DiscreteTopology M := by
  rw [← singletons_open_iff_discrete]
  intro a
  rw [← (chartAt ZeroDimModel a).isOpen_image_iff_of_subset_source]
  · apply isOpen_discrete
  · rw [Set.singleton_subset_iff]
    apply ChartedSpace.mem_chart_source

variable [SecondCountableTopology M]

theorem zero_dim_manifold_countable : Countable M := by
  have h : DiscreteTopology M := zero_dim_manifold_discrete
  exact countable_of_Lindelof_of_discrete

end ZeroDimCharts

section DiscreteManifold

variable {M : Type} [TopologicalSpace M] [DiscreteTopology M] [Countable M]

open PUnit

/-- Construction of a zero-dimensional manifold structure on any discrete countable space. -/

def zeroDimMfd : ChartedSpace ZeroDimModel M :=
{ atlas       := Set.univ,
  chartAt     := fun x ↦
  { toFun              := fun _ ↦ (default : ZeroDimModel),
    invFun             := fun _ ↦ x,
    source             := {x},
    target             := Set.univ,
    continuousOn_toFun := by
      simp,
    continuousOn_invFun := by
      exact continuousOn_const,
    left_inv'          := by
      intro y hy; rcases hy with rfl; rfl,
    right_inv'         := by
      intro u hu; simpa using Subsingleton.elim (default : ZeroDimModel) u,
    open_source        := isOpen_discrete _,
    open_target        := isOpen_univ,
    map_source'        := by
      intro y hy; simp,
    map_target'        := by
      intro u hu; simp  },
  mem_chart_source := by
    intro x; simp,
  chart_mem_atlas := by
    intro x; simp }

end DiscreteManifold
end
