/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Submonoid.Centralizer

#align_import group_theory.subgroup.basic from "leanprover-community/mathlib"@"4be589053caf347b899a494da75410deb55fb3ef"

/-!
# Centralizers of subgroups
-/


open Function
open Int

variable {G : Type*} [Group G]

namespace Subgroup

variable {H K : Subgroup G}

/-- The `centralizer` of `H` is the subgroup of `g : G` commuting with every `h : H`. -/
@[to_additive
      "The `centralizer` of `H` is the additive subgroup of `g : G` commuting with every `h : H`."]
def centralizer (s : Set G) : Subgroup G :=
  { Submonoid.centralizer s with
    carrier := Set.centralizer s
    inv_mem' := Set.inv_mem_centralizer }
#align subgroup.centralizer Subgroup.centralizer
#align add_subgroup.centralizer AddSubgroup.centralizer

@[to_additive]
theorem mem_centralizer_iff {g : G} {s : Set G} : g ∈ centralizer s ↔ ∀ h ∈ s, h * g = g * h :=
  Iff.rfl
#align subgroup.mem_centralizer_iff Subgroup.mem_centralizer_iff
#align add_subgroup.mem_centralizer_iff AddSubgroup.mem_centralizer_iff

@[to_additive]
theorem mem_centralizer_iff_commutator_eq_one {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, h * g * h⁻¹ * g⁻¹ = 1 := by
  simp only [mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]
#align subgroup.mem_centralizer_iff_commutator_eq_one Subgroup.mem_centralizer_iff_commutator_eq_one
#align add_subgroup.mem_centralizer_iff_commutator_eq_zero AddSubgroup.mem_centralizer_iff_commutator_eq_zero

@[to_additive]
theorem centralizer_univ : centralizer Set.univ = center G :=
  SetLike.ext' (Set.centralizer_univ G)
#align subgroup.centralizer_univ Subgroup.centralizer_univ
#align add_subgroup.centralizer_univ AddSubgroup.centralizer_univ

@[to_additive]
theorem le_centralizer_iff : H ≤ centralizer K ↔ K ≤ centralizer H :=
  ⟨fun h x hx _y hy => (h hy x hx).symm, fun h x hx _y hy => (h hy x hx).symm⟩
#align subgroup.le_centralizer_iff Subgroup.le_centralizer_iff
#align add_subgroup.le_centralizer_iff AddSubgroup.le_centralizer_iff

@[to_additive]
theorem center_le_centralizer (s) : center G ≤ centralizer s :=
  Set.center_subset_centralizer s
#align subgroup.center_le_centralizer Subgroup.center_le_centralizer
#align add_subgroup.center_le_centralizer AddSubgroup.center_le_centralizer

@[to_additive]
theorem centralizer_le {s t : Set G} (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Submonoid.centralizer_le h
#align subgroup.centralizer_le Subgroup.centralizer_le
#align add_subgroup.centralizer_le AddSubgroup.centralizer_le

@[to_additive (attr := simp)]
theorem centralizer_eq_top_iff_subset {s : Set G} : centralizer s = ⊤ ↔ s ⊆ center G :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset
#align subgroup.centralizer_eq_top_iff_subset Subgroup.centralizer_eq_top_iff_subset
#align add_subgroup.centralizer_eq_top_iff_subset AddSubgroup.centralizer_eq_top_iff_subset

@[to_additive]
instance Centralizer.characteristic [hH : H.Characteristic] :
    (centralizer (H : Set G)).Characteristic := by
  refine Subgroup.characteristic_iff_comap_le.mpr fun ϕ g hg h hh => ϕ.injective ?_
  rw [map_mul, map_mul]
  exact hg (ϕ h) (Subgroup.characteristic_iff_le_comap.mp hH ϕ hh)
#align subgroup.subgroup.centralizer.characteristic Subgroup.Centralizer.characteristic
#align add_subgroup.subgroup.centralizer.characteristic AddSubgroup.Centralizer.characteristic

@[to_additive]
theorem le_centralizer_iff_isCommutative : K ≤ centralizer K ↔ K.IsCommutative :=
  ⟨fun h => ⟨⟨fun x y => Subtype.ext (h y.2 x x.2)⟩⟩,
    fun h x hx y hy => congr_arg Subtype.val (h.1.1 ⟨y, hy⟩ ⟨x, hx⟩)⟩
#align subgroup.le_centralizer_iff_is_commutative Subgroup.le_centralizer_iff_isCommutative
#align add_subgroup.le_centralizer_iff_is_commutative AddSubgroup.le_centralizer_iff_isCommutative

variable (H)

@[to_additive]
theorem le_centralizer [h : H.IsCommutative] : H ≤ centralizer H :=
  le_centralizer_iff_isCommutative.mpr h
#align subgroup.le_centralizer Subgroup.le_centralizer
#align add_subgroup.le_centralizer AddSubgroup.le_centralizer

end Subgroup
