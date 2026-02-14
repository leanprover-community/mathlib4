/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# MulAction of quotient group on fixed points

Given a `MulAction` of a group `G` on `A` and a normal subgroup `H` of `G`,
there is a `MulAction` of the quotient group `G ⧸ H` on `fixedPoints H A`.

-/

@[expose] public section

namespace MulAction

variable {G : Type*} [Group G] {A : Type*} [MulAction G A]

variable {H : Subgroup G} [H.Normal]

instance : MulAction (G ⧸ H) (fixedPoints H A) :=
  ofEndHom <|
    QuotientGroup.lift H (toEndHom : G →* Function.End (fixedPoints H A))
    (fun g hg ↦ by funext a; ext; exact a.2 ⟨g, hg⟩)

@[simp]
lemma coe_quotient_smul_fixedPoints (g : G) (a : fixedPoints H A) :
    (g : G ⧸ H) • a = g • a := rfl

@[simp]
lemma quotient_out_smul_fixedPoints (g : G ⧸ H) (a : fixedPoints H A) :
    g.out • a = g • a := by
  conv_rhs => rw [← g.out_eq]
  rfl

end MulAction
