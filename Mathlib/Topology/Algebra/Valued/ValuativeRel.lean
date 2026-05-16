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

public section

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

/-- Assuming `ContinuousConstVAdd R R`, we only need to check the neighbourhood of `0` in order to
prove `IsValuativeTopology R`. -/
lemma of_hasBasis_zero [ContinuousConstVAdd R R]
    (h : (𝓝 (0 : R)).HasBasis (fun _ ↦ True) fun γ : (ValueGroupWithZero R)ˣ ↦ { x | v x < γ }) :
    IsValuativeTopology R :=
  .of_zero <| by simp [h.mem_iff]

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

variable {R : Type*} [CommRing R] [ValuativeRel R]

-- TODO: should this be generalized to `Valuation.Integers`?

instance : ValuativeRel 𝒪[R] :=
  .ofValuation ((valuation R).comap (Subring.subtype _))

@[simp]
lemma rel_val_integer_iff {x y : 𝒪[R]} :
    (x : R) ≤ᵥ y ↔ x ≤ᵥ y := by
  have hv : (valuation R).Compatible := inferInstance
  simp [hv.rel_iff_le, (Valuation.Compatible.ofValuation _).rel_iff_le]

instance : ValuativeExtension 𝒪[R] R where
  rel_iff_rel := by simp [Algebra.algebraMap_ofSubring_apply]

end ValuativeRel

namespace IsValuativeTopology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]

open ValuativeRel

instance : IsValuativeTopology 𝒪[K] := by
  apply IsValuativeTopology.of_hasBasis_zero
  rw [nhds_subtype_eq_comap]
  refine ((hasBasis_nhds_zero K).comap Subtype.val).to_hasBasis ?_ ?_
  · simp only [Set.preimage_setOf_eq, Set.setOf_subset_setOf, Subtype.forall, true_and,
    forall_const]
    intro r
    rcases lt_or_ge 1 r.val with hr | hr
    · use 1
      simp +contextual [← (ValuativeExtension.mapValueGroupWithZero_strictMono (B := K)).lt_iff_lt,
        Algebra.algebraMap_ofSubring_apply, hr.trans']
    · obtain ⟨a, b, hab⟩ := valuation_surjective r.val
      rcases eq_or_ne a 0 with rfl | ha
      · simp [eq_comm] at hab
      -- this is where we use `Field` since we need to construct an element of `𝒪[K]`
      rw [← hab, ← map_div₀] at hr
      refine ⟨Units.mk0 (valuation _ ⟨a / b, hr⟩) ?_, ?_⟩
      · simp [← (ValuativeExtension.mapValueGroupWithZero_strictMono (B := K)).injective.ne_iff,
          Subtype.ext_iff, ha]
      · simp only [Units.val_mk0, lt_iff_le_not_ge, ←
          (Valuation.Compatible.ofValuation _).rel_iff_le, ← hab, ← map_div₀]
        intro _ _
        refine And.imp rel_val_integer_iff.mpr (mt ?_)
        intro h
        exact rel_val_integer_iff.mp h -- not clear where `* ↑1` comes from
  · simp only [Set.preimage_setOf_eq, Set.setOf_subset_setOf, Subtype.forall, true_and,
    forall_const]
    intro r
    use Units.map (ValuativeExtension.mapValueGroupWithZero _ _).toMonoidHom r
    simp only [Units.coe_map, MonoidHom.coe_mk, ZeroHom.toFun_eq_coe,
      MonoidWithZeroHom.toZeroHom_coe, OneHom.coe_mk]
    intro _ _ hxr
    rw [← (ValuativeExtension.mapValueGroupWithZero_strictMono (B := K)).lt_iff_lt]
    simp [Algebra.algebraMap_ofSubring_apply, hxr]

end IsValuativeTopology
