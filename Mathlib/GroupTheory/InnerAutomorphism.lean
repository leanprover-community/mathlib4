/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The inner automorphism group

The *inner automorphisms* of a group `G` are the automorphisms of the form `MulAut.conj g`,
conjugation by an element `g : G`. They form a subgroup of `MulAut G`, namely the range of
`MulAut.conj`, which is normal: the conjugate of an inner automorphism by any automorphism is
again inner (`MulAut.conj_conj`).

## Main definitions

* `MulAut.inner G` : the subgroup of `MulAut G` of inner automorphisms, i.e. the range of
  `MulAut.conj`.
* `MulAut.innerCongr` : the isomorphism of inner automorphism groups induced by `G ≃* H`.

## Main results

* `MulAut.normal_inner` : `MulAut.inner G` is a normal subgroup of `MulAut G`. This is the
  foundational fact behind the outer automorphism group `MulAut G ⧸ MulAut.inner G`.
* `MulAut.inner_eq_bot_iff` : `MulAut.inner G` is trivial iff `G` is commutative.

Since the kernel of `MulAut.conj` is the center (`Subgroup.ker_conj`), the first isomorphism
theorem gives the standard isomorphism `MulAut.inner G ≃* G ⧸ Subgroup.center G`; this is not
stated as a separate declaration.
-/

@[expose] public section

namespace MulAut


/-- The **inner automorphism group** of a multiplicative group `G`: the subgroup of `MulAut G`
consisting of the automorphisms given by conjugation, i.e. the range of `MulAut.conj`. -/
@[to_additive
/-- The **inner automorphism group** of an additive group `G`: the subgroup of `AddAut G` consisting
of the automorphisms given by conjugation, i.e. the range of `AddAut.addConj`. -/]
def inner (G : Type*) [Group G] : Subgroup (MulAut G) := conj.range

variable {G : Type*} [Group G]

@[to_additive (attr := simp)] theorem range_conj : conj.range = inner G := rfl

@[to_additive]
theorem mem_inner_iff {f : MulAut G} : f ∈ inner G ↔ ∃ g : G, conj g = f := MonoidHom.mem_range

@[to_additive]
theorem conj_mem_inner {g : G} : conj g ∈ inner G := ⟨g, rfl⟩

/-- The inner automorphism group is normal in the full automorphism group. -/
@[to_additive /-- The inner automorphism group is normal in the full automorphism group. -/]
instance normal_inner : (inner G).Normal where
  conj_mem _ := fun ⟨g, hg⟩ h ↦ hg ▸ ⟨h g, (conj_conj h g).symm⟩

@[to_additive]
theorem inner_eq_bot_iff : inner G = ⊥ ↔ IsMulCommutative G :=
  MonoidHom.range_eq_bot_iff.trans conj_eq_one_iff

@[to_additive (attr := simp)]
theorem inner_eq_bot [IsMulCommutative G] : inner G = ⊥ := by
  simpa [inner_eq_bot_iff]

variable {H : Type*} [Group H]

@[to_additive]
theorem map_inner_congr (e : G ≃* H) : (inner G).map (MulAut.congr e) = inner H := by
  rw [← range_conj, MonoidHom.map_range, congr_comp_conj, MonoidHom.range_comp,
    e.range_eq_top, Subgroup.map_top, range_conj]

/-- An isomorphism `G ≃* H` induces an isomorphism of their inner automorphism groups. -/
@[to_additive (attr := simps!)
/-- An isomorphism `G ≃* H` induces an isomorphism of their inner automorphism groups. -/]
def innerCongr (e : G ≃* H) : inner G ≃* inner H :=
  ((MulAut.congr e).subgroupMap (inner G)).trans (MulEquiv.subgroupCongr (map_inner_congr e))

end MulAut
