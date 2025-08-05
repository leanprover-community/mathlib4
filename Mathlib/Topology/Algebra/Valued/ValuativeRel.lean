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

namespace IsValuativeTopology

section

/-! # Alternate constructors -/

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]

open ValuativeRel TopologicalSpace Filter Topology Set

local notation "v" => valuation R

variable [ContinuousConstVAdd R R]

/-- Assuming `ContinuousConstVAdd R R`, we only need to check the neighbourhood of `0` in order to
prove `IsValuativeTopology R`. -/
theorem of_zero
    (h₀ : ∀ s : Set R, s ∈ 𝓝 0 ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { z | v z < γ } ⊆ s) :
    IsValuativeTopology R where
  mem_nhds_iff {s x} := by
    simpa [← vadd_mem_nhds_vadd_iff (t := s) (-x), ← image_vadd, ← image_subset_iff] using
      h₀ ((x + ·) ⁻¹' s)

/-- Assuming `ContinuousConstVAdd R R`, we only need to check the neighbourhood of `0` in order to
prove `IsValuativeTopology R`. -/
lemma of_hasBasis_zero (h : (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
    fun γ : (ValueGroupWithZero R)ˣ ↦ { x | (valuation R) x < γ }) :
    IsValuativeTopology R :=
  .of_zero <| by simp [h.mem_iff]

lemma of_hasBasis_pair
    (h : (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ rs.1 ∈ posSubmonoid R ∧ rs.2 ∈ posSubmonoid R)
      fun rs  ↦ { x | x * rs.2 <ᵥ rs.1 }) :
    IsValuativeTopology R := by
  refine of_hasBasis_zero (h.to_hasBasis ?_ ?_)
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

lemma of_hasBasis_compatible {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    {v' : Valuation R Γ₀} [v'.Compatible]
    (h : (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v' rs.1 ≠ 0 ∧ v' rs.2 ≠ 0)
    fun rs : R × R ↦ { x | v' x * v' rs.2 < v' rs.1 }) :
    IsValuativeTopology R := by
  refine of_hasBasis_pair ?_
  convert h <;>
  simp [Valuation.Compatible.rel_iff_le («v» := v'), Valuation.Compatible.rel_lt_iff_lt («v» := v')]

lemma of_hasBasis_ne_zero
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [ContinuousConstVAdd F F]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v' : Valuation F Γ₀} [v'.Compatible]
    (h : (𝓝 (0 : F)).HasBasis (fun r ↦ v' r ≠ 0) fun r ↦ { x | v' x < v' r }) :
    IsValuativeTopology F :=
  of_hasBasis_compatible (v' := v') <| h.to_hasBasis
    (fun x hx ↦ ⟨(x, 1), (by simp [hx]), by simp⟩)
    fun ⟨x, y⟩ hxy ↦ ⟨x / y, by simpa using hxy, by simp [lt_div_iff₀ (zero_lt_iff.2 hxy.right)]⟩

end

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

open ValuativeRel TopologicalSpace Filter Topology Set

local notation "v" => valuation R

/-- A version mentioning subtraction. -/
lemma mem_nhds_iff' {s : Set R} {x : R} :
    s ∈ 𝓝 (x : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { z | v (z - x) < γ } ⊆ s := by
  convert mem_nhds_iff (s := s) using 4
  ext z
  simp [neg_add_eq_sub]

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.mem_nhds := mem_nhds_iff'

lemma mem_nhds_zero_iff (s : Set R) : s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { x | v x < γ } ⊆ s := by
  convert IsValuativeTopology.mem_nhds_iff' (x := (0 : R))
  rw [sub_zero]

@[deprecated (since := "2025-08-04")]
alias _root_.ValuativeTopology.mem_nhds_iff := mem_nhds_zero_iff

/-- Helper `Valued` instance when `ValuativeTopology R` over a `UniformSpace R`,
for use in porting files from `Valued` to `ValuativeRel`. -/
instance (priority := low) {R : Type*} [CommRing R] [ValuativeRel R] [UniformSpace R]
    [IsUniformAddGroup R] [IsValuativeTopology R] :
    Valued R (ValueGroupWithZero R) where
  «v» := valuation R
  is_topological_valuation := mem_nhds_zero_iff

theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { z | v (z - x) < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds_iff']

variable (R) in
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { x | v x < γ } := by
  convert hasBasis_nhds (0 : R); rw [sub_zero]

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.hasBasis_nhds_zero := hasBasis_nhds_zero

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
    (v' : Valuation R Γ₀) [v'.Compatible] :
    (𝓝 (0 : R)).HasBasis (fun rs : R × R ↦ v' rs.1 ≠ 0 ∧ v' rs.2 ≠ 0)
      fun rs : R × R ↦ { x | v' x * v' rs.2 < v' rs.1 } := by
  convert hasBasis_nhds_zero_pair R <;>
  simp [Valuation.Compatible.rel_iff_le («v» := v'), Valuation.Compatible.rel_lt_iff_lt («v» := v')]

lemma hasBasis_nhds_zero_ne_zero
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsValuativeTopology F]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v' : Valuation F Γ₀) [v'.Compatible] :
    (𝓝 (0 : F)).HasBasis (fun r ↦ v' r ≠ 0) fun r ↦ { x | v' x < v' r } :=
  (hasBasis_nhds_zero_compatible v').to_hasBasis
    (fun ⟨x, y⟩ hxy ↦ ⟨x / y, by simpa using hxy, by simp [lt_div_iff₀ (zero_lt_iff.2 hxy.2)]⟩)
    fun x hx ↦ ⟨(x, 1), by simp [hx], by simp⟩

variable (R) in
instance (priority := low) isTopologicalAddGroup : IsTopologicalAddGroup R := by
  have cts_add : ContinuousConstVAdd R R :=
    ⟨fun x ↦ continuous_iff_continuousAt.2 fun z ↦
      ((hasBasis_nhds z).tendsto_iff (hasBasis_nhds (x + z))).2 fun γ _ ↦
        ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩⟩
  have basis := hasBasis_nhds_zero R
  refine .of_comm_of_nhds_zero ?_ ?_ fun x₀ ↦ (map_eq_of_inverse (-x₀ + ·) ?_ ?_ ?_).symm
  · exact (basis.prod_self.tendsto_iff basis).2 fun γ _ ↦
      ⟨γ, trivial, fun ⟨_, _⟩ hx ↦ (v).map_add_lt hx.left hx.right⟩
  · exact (basis.tendsto_iff basis).2 fun γ _ ↦ ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩
  · ext; simp
  · simpa [ContinuousAt] using (cts_add.1 x₀).continuousAt (x := (0 : R))
  · simpa [ContinuousAt] using (cts_add.1 (-x₀)).continuousAt (x := x₀)

instance (priority := low) : IsTopologicalRing R :=
  letI := IsTopologicalAddGroup.toUniformSpace R
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  inferInstance

theorem isOpen_ball (r : ValueGroupWithZero R) :
    IsOpen {x | v x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · intro x hx
    rw [mem_nhds_iff']
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
  rw [mem_nhds_iff']
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
  rw [mem_nhds_iff']
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

namespace ValuativeRel

@[inherit_doc]
scoped notation "𝒪[" R "]" => Valuation.integer (valuation R)

@[inherit_doc]
scoped notation "𝓂[" K "]" => IsLocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓀[" K "]" => IsLocalRing.ResidueField 𝒪[K]

end ValuativeRel
