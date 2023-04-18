/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.valuation
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Nonarchimedean.Bases
import Mathbin.Topology.Algebra.UniformFilterBasis
import Mathbin.RingTheory.Valuation.Basic

/-!
# The topology on a valued ring

In this file, we define the non archimedean topology induced by a valuation on a ring.
The main definition is a `valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.
-/


open Classical Topology uniformity

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
      simp [Valuation.ltAddSubgroup] <;> tauto
    mul := by
      rintro γ
      cases' exists_square_le γ with γ₀ h
      use γ₀
      rintro - ⟨r, s, r_in, s_in, rfl⟩
      calc
        (v (r * s) : Γ₀) = v r * v s := Valuation.map_mul _ _ _
        _ < γ₀ * γ₀ := (mul_lt_mul₀ r_in s_in)
        _ ≤ γ := by exact_mod_cast h
        
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : Γ₀ˣ)
        rintro y (y_in : (v y : Γ₀) < 1)
        change v (x * y) < _
        rw [Valuation.map_mul, Hx, MulZeroClass.zero_mul]
        exact Units.zero_lt γ
      · simp only [image_subset_iff, set_of_subset_set_of, preimage_set_of_eq, Valuation.map_mul]
        use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (x * y) : Γ₀) < γ
        rw [Valuation.map_mul, Hx, mul_comm]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y (y_in : (v y : Γ₀) < 1)
        change v (y * x) < _
        rw [Valuation.map_mul, Hx, MulZeroClass.mul_zero]
        exact Units.zero_lt γ
      · use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (y * x) : Γ₀) < γ
        rw [Valuation.map_mul, Hx]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }
#align valuation.subgroups_basis Valuation.subgroups_basis

end Valuation

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `uniform_space`, `uniform_add_group`. -/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, UniformAddGroup R where
  V : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x : R | v x < γ } ⊆ s
#align valued Valued

attribute [nolint dangerous_instance] Valued.toUniformSpace

namespace Valued

/-- Alternative `valued` constructor for use when there is no preferred `uniform_space`
structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { V
    toUniformSpace := @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
    to_uniformAddGroup := @comm_topologicalAddGroup_is_uniform _ _ v.subgroups_basis.topology _
    is_topological_valuation :=
      by
      letI := @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [filter.has_basis_iff.mp v.subgroups_basis.has_basis_nhds_zero s]
      exact exists_congr fun γ => by simpa }
#align valued.mk' Valued.mk'

variable (R Γ₀) [_i : Valued R Γ₀]

include _i

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { x | v x < (γ : Γ₀) } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]
#align valued.has_basis_nhds_zero Valued.hasBasis_nhds_zero

theorem hasBasis_uniformity :
    (𝓤 R).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { p : R × R | v (p.2 - p.1) < (γ : Γ₀) } :=
  by
  rw [uniformity_eq_comap_nhds_zero]
  exact (has_basis_nhds_zero R Γ₀).comap _
#align valued.has_basis_uniformity Valued.hasBasis_uniformity

theorem toUniformSpace_eq :
    toUniformSpace = @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _ :=
  uniformSpace_eq
    ((hasBasis_uniformity R Γ₀).eq_of_same_basis <| v.subgroups_basis.hasBasis_nhds_zero.comap _)
#align valued.to_uniform_space_eq Valued.toUniformSpace_eq

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : Γ₀ˣ, { y | (v (y - x) : Γ₀) < γ } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_set_of_eq, exists_true_left,
    ((has_basis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]
#align valued.mem_nhds Valued.mem_nhds

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x | v x < (γ : Γ₀) } ⊆ s := by
  simp only [mem_nhds, sub_zero]
#align valued.mem_nhds_zero Valued.mem_nhds_zero

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x :=
  by
  rw [mem_nhds]
  rcases units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩
  use γ
  rw [hx]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ y_in
#align valued.loc_const Valued.loc_const

instance (priority := 100) : TopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » M) -/
theorem cauchy_iff {F : Filter R} :
    Cauchy F ↔
      F.ne_bot ∧ ∀ γ : Γ₀ˣ, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), (v (y - x) : Γ₀) < γ :=
  by
  rw [to_uniform_space_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [valued.v.subgroups_basis.mem_add_group_filter_basis_iff]
  constructor
  · intro h γ
    exact h _ (valued.v.subgroups_basis.mem_add_group_filter_basis _)
  · rintro h - ⟨γ, rfl⟩
    exact h γ
#align valued.cauchy_iff Valued.cauchy_iff

end Valued

