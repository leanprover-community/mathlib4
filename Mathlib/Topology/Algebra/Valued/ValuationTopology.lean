/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.UniformFilterBasis
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The topology on a valued ring

In this file, we define the non archimedean topology induced by a valuation on a ring.
The main definition is a `Valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.
-/

open scoped Topology uniformity
open Set Valuation

noncomputable section

universe v u

variable {R : Type u} [Ring R] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
theorem subgroups_basis : RingSubgroupsBasis fun γ : Γ₀ˣ => (v.ltAddSubgroup γ : AddSubgroup R) :=
  { inter := by
      rintro γ₀ γ₁
      use min γ₀ γ₁
      simp only [ltAddSubgroup, Units.min_val, Units.val_le_val, lt_min_iff,
        AddSubgroup.mk_le_mk, setOf_subset_setOf, le_inf_iff, and_imp, imp_self, implies_true,
        forall_const, and_true]
      tauto
    mul := by
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [ltAddSubgroup, AddSubgroup.coe_set_mk, mem_setOf_eq] at r_in s_in
      calc
        (v (r * s) : Γ₀) = v r * v s := Valuation.map_mul _ _ _
        _ < γ₀ * γ₀ := by gcongr <;> exact zero_le'
        _ ≤ γ := mod_cast h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : Γ₀ˣ)
        rintro y _
        change v (x * y) < _
        rw [Valuation.map_mul, Hx, zero_mul]
        exact Units.zero_lt γ
      · use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (x * y) : Γ₀) < γ
        rw [Valuation.map_mul, Hx, mul_comm]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        change v (y * x) < _
        rw [Valuation.map_mul, Hx, mul_zero]
        exact Units.zero_lt γ
      · use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (y * x) : Γ₀) < γ
        rw [Valuation.map_mul, Hx]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

end Valuation

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `Valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `UniformSpace`, `UniformAddGroup`. -/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, UniformAddGroup R where
  v : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x : R | v x < γ } ⊆ s

namespace Valued

/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { v
    toUniformSpace := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
    toUniformAddGroup := @comm_topologicalAddGroup_is_uniform _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      letI := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      exact exists_congr fun γ => by rw [true_and]; rfl }

variable (R Γ₀)
variable [_i : Valued R Γ₀]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { x | v x < (γ : Γ₀) } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]

-- Porting note: Replaced `𝓤 R` with `uniformity R`
theorem hasBasis_uniformity : (uniformity R).HasBasis (fun _ => True)
    fun γ : Γ₀ˣ => { p : R × R | v (p.2 - p.1) < (γ : Γ₀) } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

theorem toUniformSpace_eq :
    toUniformSpace = @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _ :=
  UniformSpace.ext
    ((hasBasis_uniformity R Γ₀).eq_of_same_basis <| v.subgroups_basis.hasBasis_nhds_zero.comap _)

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : Γ₀ˣ, { y | (v (y - x) : Γ₀) < γ } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x | v x < (γ : Γ₀) } ⊆ s := by
  simp only [mem_nhds, sub_zero]

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  use Units.mk0 _ h
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ y_in

instance (priority := 100) : IsTopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : Γ₀ˣ, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), (v (y - x) : Γ₀) < γ := by
  rw [toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis _)
  · rintro h - ⟨γ, rfl⟩
    exact h γ

variable (R)

/-- A ball of a valued ring is open. -/
theorem isOpen_ball (r : Γ₀) : IsOpen (X := R) {x | v x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl|hr
  · simp
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.map_add _ x).trans_lt (max_lt hy hx)⟩

/-- A closed ball of a valued ring is open. -/
theorem isOpen_closedball {r : Γ₀} (hr : r ≠ 0) : IsOpen (X := R) {x | v x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ le_trans (map_add _ _ _) (max_le (le_of_lt hy) hx)⟩

/-- A sphere of a valued ring is open. -/
theorem isOpen_sphere {r : Γ₀} (hr : r ≠ 0) : IsOpen (X := R) {x | v x = r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [mem_setOf_eq, setOf_subset_setOf] at hx ⊢
  refine ⟨Units.mk0 _ hr, fun y hy => (sub_add_cancel y x).symm ▸ ?_⟩
  rwa [v.map_add_eq_of_lt_right]
  simpa [hx] using hy

/-- The unit closed ball of a valued ring is open. -/
theorem integer_isOpen : IsOpen (_i.v.integer : Set R) :=
  isOpen_closedball _ one_ne_zero

/-- The valuation subring of a valued field is open. -/
theorem valuationSubring_isOpen (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsOpen (hv.v.valuationSubring : Set K) :=
  integer_isOpen K

end Valued
