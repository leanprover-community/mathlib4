/-
Copyright (c) 2026 Osman Safa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Osman Safa
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Basic results on the abelianization

This file contains basic results about the abelianization of a group, building on
the definitions in `Mathlib.GroupTheory.Abelianization.Defs`.

## Main definitions

* `Group.Abelianization.quotientMulEquiv`: for a normal subgroup `N` of `G`, the
  abelianization of `G ⧸ N` is isomorphic to the quotient of the abelianization of `G` by the
  image of `N`.
-/

@[expose] public section

assert_not_exists Cardinal Field

namespace Group.Abelianization

universe u

-- Let `G` be a group and `N` a normal subgroup of `G`.
variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

/-- Abelianizing a quotient `G ⧸ N` is the same as abelianizing `G`
and then quotienting by the image of `N`. -/
@[to_additive
/-- Abelianizing a quotient `G ⧸ N` is the same as abelianizing `G`
and then quotienting by the image of `N`. -/]
def quotientMulEquiv : Abelianization (G ⧸ N) ≃* Abelianization G ⧸ N.map of :=
 MonoidHom.toMulEquiv
    (lift <| QuotientGroup.lift N ((QuotientGroup.mk' _).comp of) <| fun _ h ↦
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map_of_mem of h))
    (QuotientGroup.lift _ (map (QuotientGroup.mk' N)) <| fun y ⟨x, hx, hxy⟩ ↦
      hxy ▸ (congrArg of ((QuotientGroup.eq_one_iff _).mpr hx)).trans (map_one of))
    (by ext; rfl) 
    (by ext; rfl)

@[to_additive (attr := simp)]
theorem quotientMulEquiv_of_mk (x : G) :
    quotientMulEquiv N (of (x : G ⧸ N)) = (of x : Abelianization G ⧸ N.map of) :=
  rfl

@[to_additive (attr := simp)]
theorem quotientMulEquiv_symm_mk_of (x : G) :
    (quotientMulEquiv N).symm (of x : Abelianization G ⧸ N.map of) = of (x : G ⧸ N) :=
  rfl

end Group.Abelianization
