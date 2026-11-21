/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.GroupTheory.InnerAutomorphism
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The outer automorphism group

The *outer automorphism group* of a group `G` is the quotient of its automorphism group by the
inner automorphisms, `MulAut G ⧸ MulAut.inner G`. It is a group because `MulAut.inner G` is
normal (`MulAut.normal_inner`).

## Main definitions

* `MulAut.Outer G` : the outer automorphism group `MulAut G ⧸ MulAut.inner G`.
* `MulAut.Outer.of` : the canonical projection `MulAut G →* MulAut.Outer G`.
* `MulAut.Outer.congr` : the isomorphism of outer automorphism groups induced by `G ≃* H`.

## Main results

* `MulAut.inner_eq_top_iff` : every automorphism of `G` is inner (`MulAut.inner G = ⊤`) iff the
  outer automorphism group is trivial.
-/

@[expose] public section

namespace MulAut
variable {G : Type*} [Group G]

/-- The **outer automorphism group** of a multiplicative group `G`. -/
@[to_additive /-- The **outer automorphism group** of an additive group `G`. -/]
abbrev Outer (G : Type*) [Group G] := MulAut G ⧸ inner G

/-- The canonical projection from `MulAut G` to the outer automorphism group. -/
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
theorem inner_eq_top [Subsingleton (Outer G)] : inner G = ⊤ :=
  inner_eq_top_iff.mpr ‹_›

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
