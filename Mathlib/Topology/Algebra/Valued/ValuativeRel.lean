/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.WithZeroTopology
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!

# Valuative Relations as Valued

In this temporary file, we provide a helper instance
for `Valued R Γ` derived from a `ValuativeRel R`,
so that downstream files can refer to `ValuativeRel R`,
to facilitate a refactor.

-/

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)

lemma isSymmetricRel_uniformity_ball_lt (r : Γ₀) :
    IsSymmetricRel { p : R × R | v (p.2 - p.1) < r } := by
  simp [IsSymmetricRel, Valuation.map_sub_swap]

lemma isSymmetricRel_uniformity_ball_le (r : Γ₀) :
    IsSymmetricRel { p : R × R | v (p.2 - p.1) ≤ r } := by
  simp [IsSymmetricRel, Valuation.map_sub_swap]

lemma isTransitiveRel_uniformity_ball_lt (r : Γ₀) :
    IsTransitiveRel { p : R × R | v (p.2 - p.1) < r } := by
  intro _ _ _ h h'
  refine (Valuation.map_add_lt v h h').trans_eq' ?_
  simp

lemma isTransitiveRel_uniformity_ball_le (r : Γ₀) :
    IsTransitiveRel { p : R × R | v (p.2 - p.1) ≤ r } := by
  intro _ _ _ h h'
  refine (Valuation.map_add_le v h h').trans_eq' ?_
  simp

end Valuation

namespace IsValuativeTopology

section

/-! # Alternate constructors -/

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

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]

open ValuativeRel TopologicalSpace Filter Topology Set Uniformity

local notation "v" => valuation R

variable [IsValuativeTopology R]
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

instance (priority := low) : IsTopologicalRing R := by
  convert (valuation R).subgroups_basis.toRingFilterBasis.isTopologicalRing
  rw [TopologicalSpace.ext_iff_nhds]
  intro x
  ext s
  simp [(RingSubgroupsBasis.hasBasis_nhds _ _).mem_iff, mem_nhds_iff, Valuation.ltAddSubgroup,
    neg_add_eq_sub]

/-- A ring with a topological additive structure and a valuative relationship is
a uniform space made up of entourages of the form `{ (x, y) | v (y - x) < γ }`.
However, this is not a global instance to prevent timeouts in typeclass inference,
since otherwise, TC search for `UniformSpace R` will start exploring `ValuativeTopology R`. -/
local instance : UniformSpace R := IsTopologicalAddGroup.toUniformSpace R

open Uniformity in
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True)
    fun γ : (ValueGroupWithZero R)ˣ => { p : R × R | v (p.2 - p.1) < γ } := by
  rw [uniformity_eq_comap_nhds_zero']
  exact (hasBasis_nhds_zero R).comap _

instance (priority := low) : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
instance (priority := low) : IsUltraUniformity R := by
  refine .mk_of_hasBasis hasBasis_uniformity ?_ ?_
  · intros
    ext ⟨x, y⟩
    simp only [preimage_setOf_eq, Prod.snd_swap, Prod.fst_swap, mem_setOf_eq]
    rw [← Valuation.map_neg, neg_sub]
  · intro _ _ _ _ _ h h'
    simp only [mem_setOf_eq] at h h' ⊢
    have := Valuation.map_add_lt _ h h'
    ring_nf at this
    rwa [neg_add_eq_sub] at this

lemma uniformity_ball_lt_mem_uniformity {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    { p : R × R | v (p.2 - p.1) < r } ∈ 𝓤 R := by
  rw [hasBasis_uniformity.mem_iff]
  use Units.mk0 r hr
  simp

lemma uniformity_ball_le_mem_uniformity {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    { p : R × R | v (p.2 - p.1) ≤ r } ∈ 𝓤 R := by
  rw [hasBasis_uniformity.mem_iff]
  rcases le_or_gt 1 r with hr1 | hr1
  · use 1
    simp only [Units.val_one, setOf_subset_setOf, Prod.forall, true_and]
    intro _ _ h
    exact hr1.trans' h.le
  · lift r to (ValueGroupWithZero R)ˣ using IsUnit.mk0 r hr
    use r ^ 2
    simp only [Units.val_pow_eq_pow_val, setOf_subset_setOf, Prod.forall, true_and]
    intro _ _ h
    refine (h.trans ?_).le
    exact pow_lt_self_of_lt_one₀ (by simp) hr1 (by simp)

theorem isOpen_ball (r : ValueGroupWithZero R) :
    IsOpen {x | v x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · convert ((v).isTransitiveRel_uniformity_ball_lt r).isOpen_ball_of_mem_uniformity 0
      (uniformity_ball_lt_mem_uniformity hr)
    simp [UniformSpace.ball]

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isOpen_ball := isOpen_ball

theorem isClosed_ball (r : ValueGroupWithZero R) :
    IsClosed {x | v x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · convert UniformSpace.isClosed_ball_of_isSymmetricRel_of_isTransitiveRel_of_mem_uniformity
      0 ((v).isSymmetricRel_uniformity_ball_lt r) ((v).isTransitiveRel_uniformity_ball_lt r)
      (uniformity_ball_lt_mem_uniformity hr)
    simp [UniformSpace.ball]

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClosed_ball := isClosed_ball

theorem isClopen_ball (r : ValueGroupWithZero R) :
    IsClopen {x | v x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.isClopen_ball := isClopen_ball

lemma isOpen_closedBall {r : ValueGroupWithZero R} (hr : r ≠ 0) :
    IsOpen {x | v x ≤ r} := by
  convert ((v).isTransitiveRel_uniformity_ball_le r).isOpen_ball_of_mem_uniformity 0
    (uniformity_ball_le_mem_uniformity hr)
  simp [UniformSpace.ball]

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

open WithZeroTopology in
lemma continuous_valuation : Continuous v := by
  simp only [continuous_iff_continuousAt, ContinuousAt]
  rintro x
  by_cases hx : v x = 0
  · simpa [hx, (hasBasis_nhds _).tendsto_iff WithZeroTopology.hasBasis_nhds_zero,
      Valuation.map_sub_of_right_eq_zero _ hx] using fun i hi ↦ ⟨.mk0 i hi, fun y ↦ id⟩
  · simpa [(hasBasis_nhds _).tendsto_iff (WithZeroTopology.hasBasis_nhds_of_ne_zero hx)]
      using ⟨.mk0 (v x) hx, fun _ ↦ Valuation.map_eq_of_sub_lt _⟩

end IsValuativeTopology

namespace ValuativeRel

variable {R : Type*} [CommRing R]

@[inherit_doc]
scoped notation "𝒪[" R "]" => Valuation.integer (valuation R)

@[inherit_doc]
scoped notation "𝓂[" K "]" => IsLocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓀[" K "]" => IsLocalRing.ResidueField 𝒪[K]

end ValuativeRel
