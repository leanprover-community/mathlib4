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
  .mk (valuation R) fun s ↦ by convert ValuativeTopology.mem_nhds (x := (0 : R)); rw [sub_zero]

end ValuativeRel

namespace IsValuativeTopology

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

open ValuativeRel TopologicalSpace Filter Topology Set

local notation "v" => valuation R

lemma mem_nhds_iff (s : Set R) : s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { x | valuation _ x < γ } ⊆ s := by
  convert ValuativeTopology.mem_nhds (x := (0 : R))
  rw [sub_zero]

theorem hasBasis_nhds (x : R) :
    (𝓝 (x : R)).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { z | v (z - x) < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds]

variable (R) in
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { x | v x < γ } := by
  convert hasBasis_nhds (0 : R); rw [sub_zero]

instance : ContinuousConstVAdd R R where
  continuous_const_vadd x := continuous_iff_continuousAt.2 fun z ↦
    ((hasBasis_nhds z).tendsto_iff (hasBasis_nhds (x + z))).2 fun γ _ ↦
      ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩
@[deprecated (since := "2025-08-01")]
alias _root_.ValuativeTopology.hasBasis_nhds_zero := hasBasis_nhds_zero

variable [IsTopologicalAddGroup R]

variable (R) in
theorem tendsto_uncurry_add_nhds_zero :
    Tendsto (Function.uncurry (· + ·)) (𝓝 (0 : R) ×ˢ 𝓝 0) (𝓝 0) :=
  ((hasBasis_nhds_zero R).prod_self.tendsto_iff (hasBasis_nhds_zero R)).2 fun γ _ ↦
    ⟨γ, trivial, fun ⟨_, _⟩ hx ↦ (v).map_add_lt hx.left hx.right⟩

variable (R) in
theorem tendsto_neg_nhds_zero :
    Tendsto (fun x ↦ -x) (𝓝 (0 : R)) (𝓝 0) :=
  ((hasBasis_nhds_zero R).tendsto_iff (hasBasis_nhds_zero R)).2 fun γ _ ↦
    ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩

instance : IsTopologicalAddGroup R :=
  .of_comm_of_nhds_zero (tendsto_uncurry_add_nhds_zero R) (tendsto_neg_nhds_zero R) fun x₀ ↦
    Eq.symm <| map_eq_of_inverse (-x₀ + ·) (by ext; simp)
      (by simpa [ContinuousAt] using
        (ContinuousConstVAdd.continuous_const_vadd (x₀ : R)).continuousAt (x := (0 : R)))
      (by simpa [ContinuousAt] using
        (ContinuousConstVAdd.continuous_const_vadd (-x₀ : R)).continuousAt (x := x₀))

instance : IsTopologicalRing R :=
  letI := IsTopologicalAddGroup.toUniformSpace R
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  by infer_instance

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
