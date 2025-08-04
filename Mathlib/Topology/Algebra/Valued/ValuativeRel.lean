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

instance [UniformSpace R] [IsUniformAddGroup R] [ValuativeRel R] [IsValuativeTopology R] :
    Valued R (ValueGroupWithZero R) :=
  .mk (valuation R) IsValuativeTopology.mem_nhds_iff

end ValuativeRel

namespace IsValuativeTopology

variable {R : Type*} [CommRing R] [ValuativeRel R]

open ValuativeRel TopologicalSpace Filter Topology Set

lemma of_hasBasis [TopologicalSpace R] (h : (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
    fun γ : (ValueGroupWithZero R)ˣ ↦ { x | (valuation R) x < γ }) :
    IsValuativeTopology R :=
  ⟨by simp [h.mem_iff]⟩

lemma of_hasBasis_pair [TopologicalSpace R]
    (h : (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ rs.1 ∈ posSubmonoid R ∧ rs.2 ∈ posSubmonoid R)
      fun rs  ↦ { x | x * rs.2 <ᵥ rs.1 }) :
    IsValuativeTopology R := by
  refine of_hasBasis (h.to_hasBasis ?_ ?_)
  · rintro ⟨r, s⟩ ⟨hr, hs⟩
    refine ⟨Units.mk0 (.mk r ⟨s, hs⟩) ?_, trivial, ?_⟩
    · simpa using hr
    · simp [valuation]
  · rintro γ -
    obtain ⟨r, s, h⟩ := valuation_surjective γ.val
    by_cases hr : valuation R r = 0
    · simp [hr, eq_comm] at h
    · refine ⟨⟨r, s⟩, ⟨by simpa [valuation_eq_zero_iff] using hr, s.prop⟩, ?_⟩
      simp only [← h, Set.setOf_subset_setOf]
      intro x hx
      rw [lt_div_iff₀ (by simp [zero_lt_iff])]
      simp [valuation, hx]

lemma of_hasBasis_compatible {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] [TopologicalSpace R]
    {v : Valuation R Γ₀} [v.Compatible]
    (h : (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v rs.1 ≠ 0 ∧ v rs.2 ≠ 0)
    fun rs : R × R ↦ { x | v x * v rs.2 < v rs.1 }) :
    IsValuativeTopology R := by
  have : v.IsEquiv (valuation R) := isEquiv _ _
  refine of_hasBasis_pair (h.to_hasBasis ?_ ?_) <;>
  · simp only [this.ne_zero, ne_eq, valuation_eq_zero_iff, posSubmonoid_def, setOf_subset_setOf,
    and_imp, Prod.exists, Prod.forall]
    intro r s hr hs
    refine ⟨r, s, ⟨hr, hs⟩, fun x ↦ ?_⟩
    rw [← map_mul v, ← Valuation.Compatible.rel_lt_iff_lt]
    grind

variable [TopologicalSpace R] [IsValuativeTopology R]

variable (R) in
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { x | valuation _ x < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds_iff]

variable (R) in
lemma hasBasis_nhds_zero_pair :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ rs.1 ∈ posSubmonoid R ∧ rs.2 ∈ posSubmonoid R)
      fun rs  ↦ { x | x * rs.2 <ᵥ rs.1 } := by
  refine (hasBasis_nhds_zero R).to_hasBasis ?_ ?_
  · simp only [posSubmonoid_def, setOf_subset_setOf, Prod.exists, forall_const]
    intro γ
    obtain ⟨r, s, h⟩ := valuation_surjective γ.val
    by_cases hr : valuation R r = 0
    · simp [hr, eq_comm] at h
    · refine ⟨r, s, ⟨by simpa [valuation_eq_zero_iff] using hr, s.prop⟩, ?_⟩
      simp only [← h]
      intro x hx
      rw [lt_div_iff₀ (by simp [zero_lt_iff])]
      simp [valuation, hx]
  · rintro ⟨r, s⟩ ⟨hr, hs⟩
    refine ⟨Units.mk0 (.mk r ⟨s, hs⟩) ?_, trivial, ?_⟩
    · simpa using hr
    · simp [valuation]

lemma hasBasis_nhds_zero_compatible {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v rs.1 ≠ 0 ∧ v rs.2 ≠ 0)
      fun rs : R × R ↦ { x | v x * v rs.2 < v rs.1 } := by
  have : v.IsEquiv (valuation R) := isEquiv _ _
  refine ((hasBasis_nhds_zero_pair R).to_hasBasis ?_ ?_) <;>
  · simp only [this.ne_zero, ne_eq, valuation_eq_zero_iff, posSubmonoid_def, setOf_subset_setOf,
    and_imp, Prod.exists, Prod.forall]
    intro r s hr hs
    refine ⟨r, s, ⟨hr, hs⟩, fun x ↦ ?_⟩
    rw [← map_mul v, ← Valuation.Compatible.rel_lt_iff_lt]
    grind

local notation "v" => valuation R

variable [IsTopologicalAddGroup R]

theorem mem_nhds {s : Set R} {x : R} :
    s ∈ 𝓝 x ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { y | v (y - x) < γ } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R).comap fun y => y - x).mem_iff]

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.mem_nhds := mem_nhds

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

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isOpen_ball := isOpen_ball

theorem isClosed_ball (r : ValueGroupWithZero R) :
    IsClosed {x | v x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v (Units.mk0 r hr))
      (isOpen_ball _)

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClosed_ball := isClosed_ball

theorem isClopen_ball (r : ValueGroupWithZero R) :
    IsClopen {x | v x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClopen_ball := isClopen_ball

lemma isOpen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr, fun y hy => (sub_add_cancel y x).symm ▸
    le_trans ((v).map_add _ _) (max_le (le_of_lt hy) hx)⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isOpen_closedBall := isOpen_closedBall

theorem isClosed_closedBall (r : ValueGroupWithZero R) :
    IsClosed {x | v x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
  rw [mem_nhds]
  have hx' : v x ≠ 0 := ne_of_gt <| lt_of_le_of_lt zero_le' <| hx
  exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy <| Valuation.map_sub_swap v x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClosed_closedBall := isClosed_closedBall

theorem isClopen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsClopen {x | v x ≤ r} :=
  ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClopen_closedBall := isClopen_closedBall

theorem isClopen_sphere {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsClopen {x | v x = r} := by
  have h : {x : R | v x = r} = {x | v x ≤ r} \ {x | v x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClopen_sphere := isClopen_sphere

lemma isOpen_sphere {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x = r} :=
  isClopen_sphere hr |>.isOpen

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isOpen_sphere := isOpen_sphere

end IsValuativeTopology

namespace Valued

variable {R : Type*} [CommRing R] [ValuativeRel R] [UniformSpace R]
  [IsUniformAddGroup R] [IsValuativeTopology R]

/-- Helper `Valued` instance when `ValuativeTopology R` over a `UniformSpace R`,
for use in porting files from `Valued` to `ValuativeRel`. -/
scoped instance : Valued R (ValuativeRel.ValueGroupWithZero R) where
  v := ValuativeRel.valuation R
  is_topological_valuation := IsValuativeTopology.mem_nhds_iff

end Valued

namespace ValuativeRel

@[inherit_doc]
scoped notation "𝒪[" R "]" => Valuation.integer (valuation R)

@[inherit_doc]
scoped notation "𝓂[" K "]" => IsLocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓀[" K "]" => IsLocalRing.ResidueField 𝒪[K]

end ValuativeRel
