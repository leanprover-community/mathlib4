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
normal (`MulAut.normal_inner`).

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

@[to_additive (attr := simp)]
theorem coe_innerMulEquivQuotientCenter_symm (g : G) :
    ↑((innerMulEquivQuotientCenter (G := G)).symm ↑g) = conj g := rfl

@[to_additive (attr := simp)]
theorem innerMulEquivQuotientCenter_conj (g : G) :
    innerMulEquivQuotientCenter ⟨conj g, conj_mem_inner⟩ = ↑g := by
  have h : (⟨conj g, conj_mem_inner⟩ : inner G) = (innerMulEquivQuotientCenter (G := G)).symm ↑g :=
    Subtype.ext (coe_innerMulEquivQuotientCenter_symm g).symm
  rw [h, MulEquiv.apply_symm_apply]

/-- The **outer automorphism group** of a multiplicative group `G`. -/
@[to_additive /-- The **outer automorphism group** of an additive group `G`. -/]
def Outer (G : Type u) [Group G] : Type u := MulAut G ⧸ inner G

@[to_additive]
instance (G : Type*) [Group G] : Group (Outer G) := inferInstanceAs (Group (MulAut G ⧸ inner G))

/-- The canonical projection from `MulAut G` to the outer automorphism group `Outer G`. -/
@[to_additive
/-- The canonical projection from `AddAut G` to the outer automorphism group. -/]
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
def outerEquivMulAut [IsMulCommutative G] :
    Outer G ≃* MulAut G :=
  (QuotientGroup.quotientMulEquivOfEq inner_eq_bot).trans QuotientGroup.quotientBot

@[to_additive (attr := simp)]
theorem outerEquivMulAut_of [IsMulCommutative G] (f : MulAut G) :
    outerEquivMulAut (Outer.of f) = f := rfl

@[to_additive (attr := simp)]
theorem outerEquivMulAut_symm_apply [IsMulCommutative G] (f : MulAut G) :
    (outerEquivMulAut (G := G)).symm f = Outer.of f := rfl

/-- If the outer automorphism group is trivial, the inner automorphism group is the full
automorphism group. -/
@[to_additive (attr := simps!)
/-- If the outer automorphism group is trivial, the inner automorphism group is the
  full automorphism group. -/]
def innerEquivMulAut [Subsingleton (Outer G)] :
    inner G ≃* MulAut G :=
  (MulEquiv.subgroupCongr inner_eq_top).trans Subgroup.topEquiv

/-- An isomorphism `G ≃* H` induces an isomorphism of their outer automorphism groups. -/
@[to_additive
/-- An isomorphism `G ≃* H` induces an isomorphism of their outer automorphism groups. -/]
def Outer.congr {H : Type*} [Group H] (e : G ≃* H) : Outer G ≃* Outer H :=
  QuotientGroup.congr (inner G) (inner H) (MulAut.congr e) (map_inner_congr e)

@[to_additive (attr := simp)]
theorem Outer.congr_of {H : Type*} [Group H] (e : G ≃* H) (f : MulAut G) :
    Outer.congr e (Outer.of f) = Outer.of (MulAut.congr e f) := rfl

@[to_additive (attr := simp)]
theorem Outer.congr_symm_of {H : Type*} [Group H] (e : G ≃* H) (f : MulAut H) :
    (Outer.congr e).symm (Outer.of f) = Outer.of (MulAut.congr e.symm f) := rfl

end MulAut
