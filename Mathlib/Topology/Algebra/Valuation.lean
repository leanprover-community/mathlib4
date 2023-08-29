/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.UniformFilterBasis
import Mathlib.RingTheory.Valuation.Basic

#align_import topology.algebra.valuation from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# The topology on a valued ring

In this file, we define the non archimedean topology induced by a valuation on a ring.
The main definition is a `Valued` type class which equips a ring with a valuation taking
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
      -- ⊢ ∃ k, ltAddSubgroup v k ≤ ltAddSubgroup v γ₀ ⊓ ltAddSubgroup v γ₁
      use min γ₀ γ₁
      -- ⊢ ltAddSubgroup v (min γ₀ γ₁) ≤ ltAddSubgroup v γ₀ ⊓ ltAddSubgroup v γ₁
      simp [Valuation.ltAddSubgroup]
      -- ⊢ ∀ (a : R), ↑v a < ↑γ₀ → ↑v a < ↑γ₁ → ↑v a < ↑γ₀
      tauto
      -- 🎉 no goals
    mul := by
      rintro γ
      -- ⊢ ∃ j, ↑(ltAddSubgroup v j) * ↑(ltAddSubgroup v j) ⊆ ↑(ltAddSubgroup v γ)
      cases' exists_square_le γ with γ₀ h
      -- ⊢ ∃ j, ↑(ltAddSubgroup v j) * ↑(ltAddSubgroup v j) ⊆ ↑(ltAddSubgroup v γ)
      use γ₀
      -- ⊢ ↑(ltAddSubgroup v γ₀) * ↑(ltAddSubgroup v γ₀) ⊆ ↑(ltAddSubgroup v γ)
      rintro - ⟨r, s, r_in, s_in, rfl⟩
      -- ⊢ (fun x x_1 => x * x_1) r s ∈ ↑(ltAddSubgroup v γ)
      calc
        (v (r * s) : Γ₀) = v r * v s := Valuation.map_mul _ _ _
        _ < γ₀ * γ₀ := (mul_lt_mul₀ r_in s_in)
        _ ≤ γ := by exact_mod_cast h
    leftMul := by
      rintro x γ
      -- ⊢ ∃ j, ↑(ltAddSubgroup v j) ⊆ (fun x_1 => x * x_1) ⁻¹' ↑(ltAddSubgroup v γ)
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      -- ⊢ ∃ j, ↑(ltAddSubgroup v j) ⊆ (fun x_1 => x * x_1) ⁻¹' ↑(ltAddSubgroup v γ)
      · use (1 : Γ₀ˣ)
        -- ⊢ ↑(ltAddSubgroup v 1) ⊆ (fun x_1 => x * x_1) ⁻¹' ↑(ltAddSubgroup v γ)
        rintro y _
        -- ⊢ y ∈ (fun x_1 => x * x_1) ⁻¹' ↑(ltAddSubgroup v γ)
        change v (x * y) < _
        -- ⊢ ↑v (x * y) < ↑γ
        rw [Valuation.map_mul, Hx, zero_mul]
        -- ⊢ 0 < ↑γ
        exact Units.zero_lt γ
        -- 🎉 no goals
      · use γx⁻¹ * γ
        -- ⊢ ↑(ltAddSubgroup v (γx⁻¹ * γ)) ⊆ (fun x_1 => x * x_1) ⁻¹' ↑(ltAddSubgroup v γ)
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        -- ⊢ y ∈ (fun x_1 => x * x_1) ⁻¹' ↑(ltAddSubgroup v γ)
        change (v (x * y) : Γ₀) < γ
        -- ⊢ ↑v (x * y) < ↑γ
        rw [Valuation.map_mul, Hx, mul_comm]
        -- ⊢ ↑v y * ↑γx < ↑γ
        rw [Units.val_mul, mul_comm] at vy_lt
        -- ⊢ ↑v y * ↑γx < ↑γ
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
        -- 🎉 no goals
    rightMul := by
      rintro x γ
      -- ⊢ ∃ j, ↑(ltAddSubgroup v j) ⊆ (fun x_1 => x_1 * x) ⁻¹' ↑(ltAddSubgroup v γ)
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      -- ⊢ ∃ j, ↑(ltAddSubgroup v j) ⊆ (fun x_1 => x_1 * x) ⁻¹' ↑(ltAddSubgroup v γ)
      · use 1
        -- ⊢ ↑(ltAddSubgroup v 1) ⊆ (fun x_1 => x_1 * x) ⁻¹' ↑(ltAddSubgroup v γ)
        rintro y _
        -- ⊢ y ∈ (fun x_1 => x_1 * x) ⁻¹' ↑(ltAddSubgroup v γ)
        change v (y * x) < _
        -- ⊢ ↑v (y * x) < ↑γ
        rw [Valuation.map_mul, Hx, mul_zero]
        -- ⊢ 0 < ↑γ
        exact Units.zero_lt γ
        -- 🎉 no goals
      · use γx⁻¹ * γ
        -- ⊢ ↑(ltAddSubgroup v (γx⁻¹ * γ)) ⊆ (fun x_1 => x_1 * x) ⁻¹' ↑(ltAddSubgroup v γ)
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        -- ⊢ y ∈ (fun x_1 => x_1 * x) ⁻¹' ↑(ltAddSubgroup v γ)
        change (v (y * x) : Γ₀) < γ
        -- ⊢ ↑v (y * x) < ↑γ
        rw [Valuation.map_mul, Hx]
        -- ⊢ ↑v y * ↑γx < ↑γ
        rw [Units.val_mul, mul_comm] at vy_lt
        -- ⊢ ↑v y * ↑γx < ↑γ
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }
        -- 🎉 no goals
#align valuation.subgroups_basis Valuation.subgroups_basis

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
#align valued Valued

-- Porting note: removed
--attribute [nolint dangerous_instance] Valued.toUniformSpace

namespace Valued

/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { v
    toUniformSpace := @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
    toUniformAddGroup := @comm_topologicalAddGroup_is_uniform _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      letI := @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
      -- ⊢ ∀ (s : Set R), s ∈ 𝓝 0 ↔ ∃ γ, {x | ↑v x < ↑γ} ⊆ s
      intro s
      -- ⊢ s ∈ 𝓝 0 ↔ ∃ γ, {x | ↑v x < ↑γ} ⊆ s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      -- ⊢ (∃ i, True ∧ ↑(ltAddSubgroup v i) ⊆ s) ↔ ∃ γ, {x | ↑v x < ↑γ} ⊆ s
      exact exists_congr fun γ => by rw [true_and]; rfl }
      -- 🎉 no goals
#align valued.mk' Valued.mk'

variable (R Γ₀)
variable [_i : Valued R Γ₀]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { x | v x < (γ : Γ₀) } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]
  -- 🎉 no goals
#align valued.has_basis_nhds_zero Valued.hasBasis_nhds_zero

-- Porting note: Replaced `𝓤 R` with `uniformity R`
theorem hasBasis_uniformity : (uniformity R).HasBasis (fun _ => True)
    fun γ : Γ₀ˣ => { p : R × R | v (p.2 - p.1) < (γ : Γ₀) } := by
  rw [uniformity_eq_comap_nhds_zero]
  -- ⊢ Filter.HasBasis (Filter.comap (fun x => x.snd - x.fst) (𝓝 0)) (fun x => True …
  exact (hasBasis_nhds_zero R Γ₀).comap _
  -- 🎉 no goals
#align valued.has_basis_uniformity Valued.hasBasis_uniformity

theorem toUniformSpace_eq :
    toUniformSpace = @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _ :=
  UniformSpace.ext
    ((hasBasis_uniformity R Γ₀).eq_of_same_basis <| v.subgroups_basis.hasBasis_nhds_zero.comap _)
#align valued.to_uniform_space_eq Valued.toUniformSpace_eq

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : Γ₀ˣ, { y | (v (y - x) : Γ₀) < γ } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_setOf_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]
#align valued.mem_nhds Valued.mem_nhds

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x | v x < (γ : Γ₀) } ⊆ s := by
  simp only [mem_nhds, sub_zero]
  -- 🎉 no goals
#align valued.mem_nhds_zero Valued.mem_nhds_zero

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  -- ⊢ ∃ γ, {y | ↑v (y - x) < ↑γ} ⊆ {y | ↑v y = ↑v x}
  rcases Units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩
  -- ⊢ ∃ γ, {y | ↑v (y - x) < ↑γ} ⊆ {y | ↑v y = ↑v x}
  use γ
  -- ⊢ {y | ↑v (y - x) < ↑γ} ⊆ {y | ↑v y = ↑v x}
  rw [hx]
  -- ⊢ {y | ↑v (y - x) < ↑v x} ⊆ {y | ↑v y = ↑v x}
  intro y y_in
  -- ⊢ y ∈ {y | ↑v y = ↑v x}
  exact Valuation.map_eq_of_sub_lt _ y_in
  -- 🎉 no goals
#align valued.loc_const Valued.loc_const

instance (priority := 100) : TopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : Γ₀ˣ, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), (v (y - x) : Γ₀) < γ := by
  rw [toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  -- ⊢ (Filter.NeBot F ∧ ∀ (U : Set R), U ∈ RingFilterBasis.toAddGroupFilterBasis → …
  apply and_congr Iff.rfl
  -- ⊢ (∀ (U : Set R), U ∈ RingFilterBasis.toAddGroupFilterBasis → ∃ M, M ∈ F ∧ ∀ ( …
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  -- ⊢ (∀ (U : Set R), (∃ i, U = ↑(ltAddSubgroup v i)) → ∃ M, M ∈ F ∧ ∀ (x : R), x  …
  constructor
  -- ⊢ (∀ (U : Set R), (∃ i, U = ↑(ltAddSubgroup v i)) → ∃ M, M ∈ F ∧ ∀ (x : R), x  …
  · intro h γ
    -- ⊢ ∃ M, M ∈ F ∧ ∀ (x : R), x ∈ M → ∀ (y : R), y ∈ M → ↑v (y - x) < ↑γ
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis _)
    -- 🎉 no goals
  · rintro h - ⟨γ, rfl⟩
    -- ⊢ ∃ M, M ∈ F ∧ ∀ (x : R), x ∈ M → ∀ (y : R), y ∈ M → y - x ∈ ↑(ltAddSubgroup v …
    exact h γ
    -- 🎉 no goals
#align valued.cauchy_iff Valued.cauchy_iff

end Valued
