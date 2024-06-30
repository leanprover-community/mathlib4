/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Center

#align_import group_theory.subgroup.basic from "leanprover-community/mathlib"@"4be589053caf347b899a494da75410deb55fb3ef"

/-!
# Centers of subgroups

-/


open Function
open Int

variable {G : Type*} [Group G]

namespace Subgroup

variable (G)

/-- The center of a group `G` is the set of elements that commute with everything in `G` -/
@[to_additive
      "The center of an additive group `G` is the set of elements that commute with
      everything in `G`"]
def center : Subgroup G :=
  { Submonoid.center G with
    carrier := Set.center G
    inv_mem' := Set.inv_mem_center }
#align subgroup.center Subgroup.center
#align add_subgroup.center AddSubgroup.center

@[to_additive]
theorem coe_center : ↑(center G) = Set.center G :=
  rfl
#align subgroup.coe_center Subgroup.coe_center
#align add_subgroup.coe_center AddSubgroup.coe_center

@[to_additive (attr := simp)]
theorem center_toSubmonoid : (center G).toSubmonoid = Submonoid.center G :=
  rfl
#align subgroup.center_to_submonoid Subgroup.center_toSubmonoid
#align add_subgroup.center_to_add_submonoid AddSubgroup.center_toAddSubmonoid

instance center.isCommutative : (center G).IsCommutative :=
  ⟨⟨fun a b => Subtype.ext (b.2.comm a).symm⟩⟩
#align subgroup.center.is_commutative Subgroup.center.isCommutative

/-- For a group with zero, the center of the units is the same as the units of the center. -/
@[simps! apply_val_coe symm_apply_coe_val]
def centerUnitsEquivUnitsCenter (G₀ : Type*) [GroupWithZero G₀] :
    Subgroup.center (G₀ˣ) ≃* (Submonoid.center G₀)ˣ where
  toFun := MonoidHom.toHomUnits <|
    { toFun := fun u ↦ ⟨(u : G₀ˣ),
      (Submonoid.mem_center_iff.mpr (fun r ↦ by
          rcases eq_or_ne r 0 with (rfl | hr)
          · rw [mul_zero, zero_mul]
          exact congrArg Units.val <| (u.2.comm <| Units.mk0 r hr).symm))⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  invFun u := unitsCenterToCenterUnits G₀ u
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' := map_mul _

variable {G}

@[to_additive]
theorem mem_center_iff {z : G} : z ∈ center G ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
#align subgroup.mem_center_iff Subgroup.mem_center_iff
#align add_subgroup.mem_center_iff AddSubgroup.mem_center_iff

instance decidableMemCenter (z : G) [Decidable (∀ g, g * z = z * g)] : Decidable (z ∈ center G) :=
  decidable_of_iff' _ mem_center_iff
#align subgroup.decidable_mem_center Subgroup.decidableMemCenter

@[to_additive]
instance centerCharacteristic : (center G).Characteristic := by
  refine characteristic_iff_comap_le.mpr fun ϕ g hg => ?_
  rw [mem_center_iff]
  intro h
  rw [← ϕ.injective.eq_iff, ϕ.map_mul, ϕ.map_mul]
  exact (hg.comm (ϕ h)).symm
#align subgroup.center_characteristic Subgroup.centerCharacteristic
#align add_subgroup.center_characteristic AddSubgroup.centerCharacteristic

theorem _root_.CommGroup.center_eq_top {G : Type*} [CommGroup G] : center G = ⊤ := by
  rw [eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  exact mul_comm y x
#align comm_group.center_eq_top CommGroup.center_eq_top

/-- A group is commutative if the center is the whole group -/
def _root_.Group.commGroupOfCenterEqTop (h : center G = ⊤) : CommGroup G :=
  { (_ : Group G) with
    mul_comm := by
      rw [eq_top_iff'] at h
      intro x y
      apply Subgroup.mem_center_iff.mp _ x
      exact h y
  }
#align group.comm_group_of_center_eq_top Group.commGroupOfCenterEqTop

variable {H : Subgroup G}

section Normalizer

@[to_additive]
theorem center_le_normalizer : center G ≤ H.normalizer := fun x hx y => by
  simp [← mem_center_iff.mp hx y, mul_assoc]
#align subgroup.center_le_normalizer Subgroup.center_le_normalizer
#align add_subgroup.center_le_normalizer AddSubgroup.center_le_normalizer

end Normalizer

end Subgroup

namespace IsConj

variable {M : Type*} [Monoid M]

theorem eq_of_left_mem_center {g h : M} (H : IsConj g h) (Hg : g ∈ Set.center M) : g = h := by
  rcases H with ⟨u, hu⟩; rwa [← u.mul_left_inj, Hg.comm u]
#align is_conj.eq_of_left_mem_center IsConj.eq_of_left_mem_center

theorem eq_of_right_mem_center {g h : M} (H : IsConj g h) (Hh : h ∈ Set.center M) : g = h :=
  (H.symm.eq_of_left_mem_center Hh).symm
#align is_conj.eq_of_right_mem_center IsConj.eq_of_right_mem_center

end IsConj

namespace ConjClasses

theorem mk_bijOn (G : Type*) [Group G] :
    Set.BijOn ConjClasses.mk (↑(Subgroup.center G)) (noncenter G)ᶜ := by
  refine ⟨fun g hg ↦ ?_, fun x hx y _ H ↦ ?_, ?_⟩
  · simp only [mem_noncenter, Set.compl_def, Set.mem_setOf, Set.not_nontrivial_iff]
    intro x hx y hy
    simp only [mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj] at hx hy
    rw [hx.eq_of_right_mem_center hg, hy.eq_of_right_mem_center hg]
  · rw [mk_eq_mk_iff_isConj] at H
    exact H.eq_of_left_mem_center hx
  · rintro ⟨g⟩ hg
    refine ⟨g, ?_, rfl⟩
    simp only [mem_noncenter, Set.compl_def, Set.mem_setOf, Set.not_nontrivial_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro h
    rw [← mul_inv_eq_iff_eq_mul]
    refine hg ?_ mem_carrier_mk
    rw [mem_carrier_iff_mk_eq]
    apply mk_eq_mk_iff_isConj.mpr
    rw [isConj_comm, isConj_iff]
    exact ⟨h, rfl⟩

end ConjClasses

assert_not_exists Multiset
assert_not_exists Ring
