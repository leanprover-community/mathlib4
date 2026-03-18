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

open Valuation ValuativeRel IsValuativeTopology UniformSpace

variable {R K Γ₀ : Type*}

section Valuation

variable [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R] [ValuativeRel R]
  [IsValuativeTopology R] [LinearOrderedCommGroupWithZero Γ₀]

-- restrict surjective, continuous
-- extends restrict
-- back to Gamma 0 
def Valuation.completion (v : Valuation R Γ₀) [v.Compatible] :
    Valuation (Completion R) Γ₀ := by sorry

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

instance Valuation.compatible_completion (v : Valuation R Γ₀) [v.Compatible] :
    v.completion.Compatible := sorry

end Compatible
