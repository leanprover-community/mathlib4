/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.WithZeroTopology
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Extending Valuation to Completion

- Completion of valuation
- Completion of valuative relation
- compatibility IsValuativeTopology
- compatibility Valuation.Compatible

Valued Field should be in another file. Completabletopfield,
-/

open Valuation ValuativeRel IsValuativeTopology UniformSpace MonoidWithZeroHom ValueGroup₀

variable {R K Γ₀ : Type*}

section Valuation

variable [Ring R] [ValuativeRel R] [LinearOrderedCommGroupWithZero Γ₀]

local instance (v : Valuation R Γ₀) : TopologicalSpace (ValueGroup₀ v) :=
  WithZeroTopology.topologicalSpace

section TopologicalSpace

variable [TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]

theorem Valuation.continuous_restrict :
    Continuous v.restrict := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne (v.restrict x) 0 with (h | h)
  · rw [ContinuousAt, h, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, v.mem_nhds_iff]
    use Units.mk0 γ hγ
    simp only [Units.val_mk0, Set.setOf_subset_setOf]
    intro a ha
    calc
    _ ≤ max (v.restrict (a - x)) (v.restrict x) := by simpa using v.restrict.map_add (a - x) x
    _ < γ := by simp [h, ha]
  · rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero h]
    simp_rw [v.restrict_inj]
    apply Valuation.loc_const
    simpa [restrict₀_apply] using h

end TopologicalSpace

section UniformSpace

variable [UniformSpace R] [IsValuativeTopology R] [IsUniformAddGroup R] (v : Valuation R Γ₀) [v.Compatible]

def Valuation.restrtictCompletion : Valuation (Completion R) (ValueGroup₀ v) := sorry

noncomputable
def Valuation.completion (v : Valuation R Γ₀) [v.Compatible] :
    Valuation (Completion R) Γ₀ := v.restrtictCompletion.map (embedding (f := v)) (by sorry)

end UniformSpace

end Valuation

section ValuativeRel

variable [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R] [ValuativeRel R]
  [IsValuativeTopology R]

instance UniformSpace.Completion.valuativeRel : ValuativeRel R := sorry

instance UniformSpace.Completion.isValuativeTopology : IsValuativeTopology R := sorry

end ValuativeRel

section Compatible

variable [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R] [ValuativeRel R]
  [IsValuativeTopology R] [LinearOrderedCommGroupWithZero Γ₀]

-- instance Valuation.compatible_completion (v : Valuation R Γ₀) [v.Compatible] :
--     v.completion.Compatible := sorry

end Compatible
