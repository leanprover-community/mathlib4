/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!

# Valuative Relations as Valued

In this temporary file, we provide a helper instance
for `Valued R Γ` derived from a `ValuativeRel R`,
so that downstream files can refer to `ValuativeRel R`,
to facilitate a refactor.

-/

@[expose] public section

namespace IsValuativeTopology

section

/-! ### Alternate constructors -/

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]

open ValuativeRel TopologicalSpace Filter Topology Set

local notation "v" => valuation R

/-- Assuming `ContinuousConstVAdd R R`, we only need to check the neighbourhood of `0` in order to
prove `IsValuativeTopology R`. -/
theorem of_zero [ContinuousConstVAdd R R]
    (h₀ : ∀ s : Set R, s ∈ 𝓝 0 ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { z | v z < γ } ⊆ s) :
    IsValuativeTopology R where
  mem_nhds_iff {s x} := by
    simpa [← vadd_mem_nhds_vadd_iff (t := s) (-x), ← image_vadd, ← image_subset_iff] using
      h₀ ((x + ·) ⁻¹' s)

end

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

open ValuativeRel TopologicalSpace Filter Topology Set

local notation "v" => valuation R

/-- Helper `Valued` instance when `ValuativeTopology R` over a `UniformSpace R`,
for use in porting files from `Valued` to `ValuativeRel`. -/
instance (priority := low) {R : Type*} [CommRing R] [ValuativeRel R] [UniformSpace R]
    [IsUniformAddGroup R] [IsValuativeTopology R] :
    Valued R (ValueGroupWithZero R) where
  «v» := valuation R
  is_topological_valuation := by
    simp_rw [Valuation.restrict_lt_iff_lt_embedding]
    convert mem_nhds_zero_iff (R := R)
    simpa [← Valuation.restrict_lt_iff_lt_embedding] using
      (valuation R).exists_setOf_restrict_le_iff 0 _

lemma v_eq_valuation {R : Type*} [CommRing R] [ValuativeRel R] [UniformSpace R]
    [IsUniformAddGroup R] [IsValuativeTopology R] :
    Valued.v = valuation R := rfl

open WithZeroTopology in
lemma continuous_valuation : Continuous v := by
  simp only [continuous_iff_continuousAt, ContinuousAt]
  rintro x
  by_cases hx : v x = 0
  · simpa [hx, ((valuation R).hasBasis_nhds _).tendsto_iff WithZeroTopology.hasBasis_nhds_zero]
      using fun i hi ↦ ⟨(Units.mk0 i hi).mapEquiv (ValueGroupWithZero.orderMonoidIso (valuation R)),
        fun y ↦ by simp [Valuation.map_sub_of_right_eq_zero _ hx]⟩
  · simpa [((valuation R).hasBasis_nhds _).tendsto_iff (hasBasis_nhds_of_ne_zero hx)]
      using ⟨(Units.mk0 (v x) hx).mapEquiv (ValueGroupWithZero.orderMonoidIso (valuation R)),
        fun _ ↦ by simpa [← (valuation R).restrict_def] using Valuation.map_eq_of_sub_lt _⟩

end IsValuativeTopology

namespace ValuativeRel

@[inherit_doc]
scoped notation "𝒪[" R "]" => Valuation.integer (valuation R)

@[inherit_doc]
scoped notation "𝓂[" K "]" => IsLocalRing.maximalIdeal ↥𝒪[K]

@[inherit_doc]
scoped notation "𝓀[" K "]" => IsLocalRing.ResidueField ↥𝒪[K]

end ValuativeRel
