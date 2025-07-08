/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!

# Valuative Relations as Valued

In this temporary file, we provide a helper instance
for `Valued R Γ` derived from a `ValuativeRel R`,
so that downstream files can refer to `ValuativeRel R`,
to facilitate a refactor.

-/

namespace ValuativeRel

variable {R : Type*} [CommRing R]

instance [UniformSpace R] [IsUniformAddGroup R] [ValuativeRel R] [ValuativeTopology R] :
    Valued R (ValueGroupWithZero R) :=
  .mk (valuation R) ValuativeTopology.mem_nhds_iff

end ValuativeRel

namespace ValuativeTopology

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]

open ValuativeRel TopologicalSpace Filter Topology Set

local notation "v" => valuation R

lemma of_hasBasis (h : (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
    fun γ : (ValueGroupWithZero R)ˣ ↦ { x | v x < γ }) :
    ValuativeTopology R :=
  ⟨by simp [h.mem_iff]⟩

variable [ValuativeTopology R]

variable (R) in
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { x | v x < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds_iff]

variable [IsTopologicalAddGroup R]

theorem mem_nhds {s : Set R} {x : R} :
    s ∈ 𝓝 x ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { y | v (y - x) < γ } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R).comap fun y => y - x).mem_iff]

theorem isOpen_ball (r : ValueGroupWithZero R) :
    IsOpen {x | v x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · intro x hx
    rw [mem_nhds]
    simp only [setOf_subset_setOf]
    exact ⟨Units.mk0 _ hr,
      fun y hy => (sub_add_cancel y x).symm ▸ ((v).map_add _ x).trans_lt (max_lt hy hx)⟩

theorem isClosed_ball (r : ValueGroupWithZero R) :
    IsClosed {x | v x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v (Units.mk0 r hr))
      (isOpen_ball _)

theorem isClopen_ball (r : ValueGroupWithZero R) :
    IsClopen {x | v x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

lemma isOpen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr, fun y hy => (sub_add_cancel y x).symm ▸
    le_trans ((v).map_add _ _) (max_le (le_of_lt hy) hx)⟩

theorem isClosed_closedBall (r : ValueGroupWithZero R) :
    IsClosed {x | v x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
  rw [mem_nhds]
  have hx' : v x ≠ 0 := ne_of_gt <| lt_of_le_of_lt zero_le' <| hx
  exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy <| Valuation.map_sub_swap v x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

theorem isClopen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsClopen {x | v x ≤ r} :=
  ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

theorem isClopen_sphere {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsClopen {x | v x = r} := by
  have h : {x : R | v x = r} = {x | v x ≤ r} \ {x | v x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

lemma isOpen_sphere {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x = r} :=
  isClopen_sphere hr |>.isOpen

end ValuativeTopology

namespace ValuativeRel

@[inherit_doc]
scoped notation "𝒪[" R "]" => Valuation.integer (valuation R)

@[inherit_doc]
scoped notation "𝓂[" K "]" => IsLocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓀[" K "]" => IsLocalRing.ResidueField 𝒪[K]

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

namespace ValuativeTopology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [ValuativeTopology K]

open ValuativeRel

instance : ValuativeTopology 𝒪[K] := by
  apply ValuativeTopology.of_hasBasis
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
    exact hxr -- somewhat heavy rfl

end ValuativeTopology
