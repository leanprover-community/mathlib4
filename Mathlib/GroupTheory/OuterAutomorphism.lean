/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.GroupTheory.InnerAutomorphism
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# The outer automorphism group

The *outer automorphism group* of a group `G` is the quotient of its automorphism group by the
inner automorphisms, `MulAut G ⧸ MulAut.inner G`. It is a group because `MulAut.inner G` is
normal (`MulAut.inner_normal`).

## Main definitions

* `MulAut.Outer G` : the outer automorphism group `MulAut G ⧸ MulAut.inner G`.
* `MulAut.Outer.of` : the canonical projection `MulAut G →* MulAut.Outer G`.
* `MulAut.Outer.congr` : the isomorphism of outer automorphism groups induced by `G ≃* H`.
* `MulAut.innerMulEquivQuotientCenter` : the isomorphism `MulAut.inner G ≃* G ⧸ Z(G)`.

## Main results

* `MulAut.inner_eq_top_iff` : every automorphism of `G` is inner (`MulAut.inner G = ⊤`) iff the
  outer automorphism group is trivial.
-/

@[expose] public section

universe u

namespace MulAut
variable {G : Type*} [Group G]

/-- The inner automorphism group is isomorphic to `G ⧸ Z(G)`. -/
@[to_additive /-- The inner automorphism group is isomorphic to `G ⧸ Z(G)`. -/]
noncomputable def innerMulEquivQuotientCenter : inner G ≃* G ⧸ Subgroup.center G :=
  (QuotientGroup.quotientKerEquivRange conj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq Subgroup.ker_conj)

/-- The **outer automorphism group** of a multiplicative group `G`. -/
@[to_additive /-- The **outer automorphism group** of an additive group `G`. -/]
def Outer (G : Type u) [Group G] : Type u := MulAut G ⧸ inner G

@[to_additive]
instance (G : Type*) [Group G] : Group (Outer G) := inferInstanceAs (Group (MulAut G ⧸ inner G))

/-- The canonical projection from `MulAut G` to the outer automorphism group `Outer G`. -/
@[to_additive /-- The canonical projection from `AddAut G` to the outer automorphism group. -/]
def Outer.of : MulAut G →* Outer G := QuotientGroup.mk' (inner G)

@[to_additive]
theorem Outer.of_surjective : Function.Surjective ⇑(Outer.of (G := G)) :=
  QuotientGroup.mk'_surjective _

@[to_additive (attr := simp)]
theorem Outer.ker_of : (Outer.of (G := G)).ker = inner G := QuotientGroup.ker_mk' _

@[to_additive]
theorem inner_eq_top_iff : inner G = ⊤ ↔ Subsingleton (Outer G) :=
  QuotientGroup.subsingleton_iff.symm

@[to_additive (attr := simp)]
theorem inner_eq_top [Subsingleton (Outer G)] : inner G = ⊤ := by
  simpa [inner_eq_top_iff]

/-- If `G` is commutative, the outer automorphism group is the full automorphism group. -/
@[to_additive /-- If `G` is commutative, the outer automorphism group is the full automorphism
group. -/]
def outerMulEquivOfIsMulCommutative [IsMulCommutative G] :
    Outer G ≃* MulAut G :=
  (QuotientGroup.quotientMulEquivOfEq inner_eq_bot).trans QuotientGroup.quotientBot

/-- If the outer automorphism group is trivial, the inner automorphism group is the full
automorphism group. -/
@[to_additive /-- If the outer automorphism group is trivial, the inner automorphism group is the
  full automorphism group. -/]
def innerMulEquivOfOuterSubsingleton [Subsingleton (Outer G)] :
    inner G ≃* MulAut G :=
  (MulEquiv.subgroupCongr inner_eq_top).trans Subgroup.topEquiv

/-- An isomorphism `G ≃* H` induces an isomorphism of their outer automorphism groups. -/
@[to_additive
/-- An isomorphism `G ≃* H` induces an isomorphism of their outer automorphism groups. -/]
def Outer.congr {H : Type*} [Group H] (e : G ≃* H) : Outer G ≃* Outer H :=
  QuotientGroup.congr (inner G) (inner H) (MulAut.congr e) (map_inner_congr e)

end MulAut
