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

* `MulAut.inner_normal` : `MulAut.inner G` is a normal subgroup of `MulAut G`. This is the
  foundational fact behind the outer automorphism group `MulAut G ⧸ MulAut.inner G`.
* `MulAut.inner_eq_bot_iff` : `MulAut.inner G` is trivial iff `G` is commutative.
-/

@[expose] public section

namespace MulAut

variable (G : Type*) [Group G]

/-- The **inner automorphism group** of a multiplicative group `G`: the subgroup of `MulAut G`
  consisting of the automorphisms given by conjugation, i.e. the range of `MulAut.conj`. -/
@[to_additive /-- The **inner automorphism group** of an additive group `G`: the subgroup of
`AddAut G` consisting of the automorphisms given by conjugation, i.e. the range of
`AddAut.addConj`. -/]
def inner : Subgroup (MulAut G) := (conj (G := G)).range

variable {G}

@[to_additive (attr := simp)]
theorem mem_inner_iff {f : MulAut G} : f ∈ inner G ↔ ∃ g : G, conj g = f := MonoidHom.mem_range

@[to_additive]
theorem conj_mem_inner {g : G} : conj g ∈ inner G := ⟨g, rfl⟩

/-- Conjugating an element of `inner G` by any automorphism stays in `inner G`. -/
@[to_additive]
theorem conj_apply_mem_inner (h : MulAut G) {f : MulAut G} (hf : f ∈ inner G) :
    conj h f ∈ inner G := by
  obtain ⟨g, rfl⟩ := mem_inner_iff.mp hf
  exact conj_conj h g ▸ conj_mem_inner

/-- An automorphism conjugate of `f` is inner iff `f` is. -/
@[to_additive]
theorem conj_mem_iff (h f : MulAut G) : conj h f ∈ inner G ↔ f ∈ inner G :=
  ⟨fun hf => by
    have H := conj_apply_mem_inner h⁻¹ hf
    rwa [← mul_apply, ← map_mul, inv_mul_cancel, map_one, one_apply] at H,
  conj_apply_mem_inner h⟩

/-- The inner automorphism group is normal in the full automorphism group. -/
@[to_additive /-- The inner automorphism group is normal in the full automorphism group. -/]
instance inner_normal : (inner G).Normal where
  conj_mem _ hn h := conj_apply_mem_inner h hn

@[to_additive]
theorem inner_eq_bot_iff : inner G = ⊥ ↔ IsMulCommutative G :=
  MonoidHom.range_eq_bot_iff.trans conj_eq_one_iff

@[to_additive (attr := simp)]
theorem inner_eq_bot [IsMulCommutative G] : inner G = ⊥ := by
  simpa [inner_eq_bot_iff]

variable {H : Type*} [Group H]

@[to_additive]
theorem map_inner_congr (e : G ≃* H) : (inner G).map (MulAut.congr e) = inner H := by
  ext φ
  simp only [Subgroup.mem_map, mem_inner_iff, MonoidHom.coe_ofClass, exists_exists_eq_and]
  exact e.exists_congr (Eq.congr_left <| congr_conj e ·)

/-- An isomorphism `G ≃* H` induces an isomorphism of their inner automorphism groups. -/
@[to_additive
/-- An isomorphism `G ≃* H` induces an isomorphism of their inner automorphism groups. -/]
def innerCongr (e : G ≃* H) : inner G ≃* inner H :=
  ((MulAut.congr e).subgroupMap (inner G)).trans (MulEquiv.subgroupCongr (map_inner_congr e))

end MulAut
