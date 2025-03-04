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

instance {M : Type*} [Monoid M] {r : M → M → Prop}
    [CovariantClass M M (· * ·) r] (N : Submonoid M):
      CovariantClass N N (· * ·) (fun x y ↦ r x y) := ⟨ by
  rintro ⟨m, _⟩ ⟨n₁, _⟩ ⟨n₂, _⟩
  simpa only [Submonoid.mk_mul_mk] using CovariantClass.elim m ⟩

instance {M : Type*} [Monoid M] [LT M]
    [CovariantClass M M (· * ·) (· < ·)] (N : Submonoid M):
      CovariantClass N N (· * ·) (fun x y ↦ x < y) := ⟨ by
  rintro ⟨m, _⟩ ⟨n₁, _⟩ ⟨n₂, _⟩
  simp only [Subtype.mk_lt_mk, Submonoid.mk_mul_mk]
  exact fun a ↦ mul_lt_mul_left' a m
  ⟩

/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
theorem subgroups_basis :
    RingSubgroupsBasis fun γ : v.rangeGroup => (v.ltAddSubgroup γ : AddSubgroup R) :=
  { inter := by
      intro γ₀ γ₁
      use min γ₀ γ₁
      simp only [LinearOrderedCommGroup.min_def, Subtype.mk_le_mk, le_inf_iff]
      refine ⟨fun a ha ↦ ?_ , fun a ha ↦ ?_⟩ <;>
      split_ifs at ha with ha1 <;>
      try exact ha
      try apply lt_of_lt_of_le ha
      · exact le_of_lt <| lt_of_not_ge ha1
      · exact lt_of_lt_of_le ha ha1
    mul := by
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [SetLike.mem_coe, mem_ltAddSubgroup_iff, _root_.map_mul]
      apply lt_of_lt_of_le (mul_lt_mul₀ r_in s_in) h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        change v (x * y) < _
        simp only [_root_.map_mul, Hx, zero_mul, Units.zero_lt]
      · use ⟨γx, mem_rangeGroup v Hx⟩⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        simp only [mem_preimage, SetLike.mem_coe, mem_ltAddSubgroup_iff, _root_.map_mul]
        rw [Hx, mul_comm]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        change v (y * x) < _
        rw [Valuation.map_mul, Hx, mul_zero]
        exact @Units.zero_lt Γ₀ _ γ
      · use ⟨γx, mem_rangeGroup v Hx⟩⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        simp only [mem_preimage, SetLike.mem_coe, mem_ltAddSubgroup_iff, _root_.map_mul, Hx]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

end Valuation

/-- A valued ring is a ring that comes equipped with a distinguished group-valued valuation.
The class `Valued` is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `UniformSpace`, `UniformAddGroup`. -/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, UniformAddGroup R where
  v : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔
    ∃ γ ∈ v.rangeGroup, { x : R | v x < γ } ⊆ s

namespace Valued

/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { v
    toUniformSpace := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
    toUniformAddGroup := @uniformAddGroup_of_addCommGroup _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      letI := @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      simp only [true_and, Subtype.exists, exists_prop]
      exact rfl.to_iff
      }

variable (R Γ₀)
variable [_i : Valued R Γ₀]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : _i.v.rangeGroup => { x | v x < (γ : Γ₀ˣ) } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]

-- Porting note: Replaced `𝓤 R` with `uniformity R`
theorem hasBasis_uniformity : (uniformity R).HasBasis (fun _ => True)
    fun γ : _i.v.rangeGroup => { p : R × R | v (p.2 - p.1) < (γ : Γ₀ˣ) } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

theorem toUniformSpace_eq :
    toUniformSpace = @IsTopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _ :=
  UniformSpace.ext
    ((hasBasis_uniformity R Γ₀).eq_of_same_basis <| v.subgroups_basis.hasBasis_nhds_zero.comap _)

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : _i.v.rangeGroup,
    { y | v (y - x) < (γ : Γ₀ˣ) } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔
    ∃ γ : _i.v.rangeGroup, { x | _i.v x < (γ : Γ₀ˣ) } ⊆ s := by
  simp only [mem_nhds, sub_zero]

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  use ⟨_, (mem_rangeGroup v rfl : Units.mk0 _ h ∈ _i.v.rangeGroup)⟩
  intro y
  exact Valuation.map_eq_of_sub_lt _

instance (priority := 100) : IsTopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : _i.v.rangeGroup, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), v (y - x) < (γ : Γ₀ˣ) := by
  rw [toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis _)
  · rintro h - ⟨γ, rfl⟩
    exact h γ

variable (R)

/-- The unit ball of a valued ring is open. -/
theorem integer_isOpen : IsOpen (_i.v.integer : Set R) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  exact ⟨1,
    fun y hy => (sub_add_cancel y x).symm ▸ le_trans (map_add _ _ _) (max_le (le_of_lt hy) hx)⟩

/-- The valuation subring of a valued field is open. -/
theorem valuationSubring_isOpen (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsOpen (hv.v.valuationSubring : Set K) :=
  integer_isOpen K

end Valued
