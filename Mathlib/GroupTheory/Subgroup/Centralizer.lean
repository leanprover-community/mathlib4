/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Submonoid.Centralizer

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

@[to_additive]
theorem mem_centralizer_iff {g : G} {s : Set G} : g ∈ centralizer s ↔ ∀ h ∈ s, h * g = g * h :=
  Iff.rfl

@[to_additive]
theorem mem_centralizer_iff_commutator_eq_one {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, h * g * h⁻¹ * g⁻¹ = 1 := by
  simp only [mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]

@[to_additive]
theorem centralizer_univ : centralizer Set.univ = center G :=
  SetLike.ext' (Set.centralizer_univ G)

@[to_additive]
theorem le_centralizer_iff : H ≤ centralizer K ↔ K ≤ centralizer H :=
  ⟨fun h x hx _y hy => (h hy x hx).symm, fun h x hx _y hy => (h hy x hx).symm⟩

@[to_additive]
theorem center_le_centralizer (s) : center G ≤ centralizer s :=
  Set.center_subset_centralizer s

@[to_additive]
theorem centralizer_le {s t : Set G} (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Submonoid.centralizer_le h

@[to_additive (attr := simp)]
theorem centralizer_eq_top_iff_subset {s : Set G} : centralizer s = ⊤ ↔ s ⊆ center G :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[to_additive]
instance Centralizer.characteristic [hH : H.Characteristic] :
    (centralizer (H : Set G)).Characteristic := by
  refine Subgroup.characteristic_iff_comap_le.mpr fun ϕ g hg h hh => ϕ.injective ?_
  rw [map_mul, map_mul]
  exact hg (ϕ h) (Subgroup.characteristic_iff_le_comap.mp hH ϕ hh)

@[to_additive]
theorem le_centralizer_iff_isCommutative : K ≤ centralizer K ↔ K.IsCommutative :=
  ⟨fun h => ⟨⟨fun x y => Subtype.ext (h y.2 x x.2)⟩⟩,
    fun h x hx y hy => congr_arg Subtype.val (h.1.1 ⟨y, hy⟩ ⟨x, hx⟩)⟩

variable (H)

@[to_additive]
theorem le_centralizer [h : H.IsCommutative] : H ≤ centralizer H :=
  le_centralizer_iff_isCommutative.mpr h

end Subgroup
