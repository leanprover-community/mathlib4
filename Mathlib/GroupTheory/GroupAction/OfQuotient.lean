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
# MonoidAction and MulDistribMulAction of quotient group on fixed points

Given a `MonoidAction`/`MulDistribMulAction` of a group `G` on `A` and a normal subgroup `H` of `G`,
there is a `MonoidAction`/`MulDistribMulAction` of the quotient group `G ⧸ H` on `fixedPoints H A`.

-/

public section

namespace MonoidAction

variable {G : Type*} [Group G] {A : Type*} [MonoidAction G A]

variable {H : Subgroup G} [H.Normal]

instance : MonoidAction (G ⧸ H) (fixedPoints H A) :=
  ofEndHom <|
    QuotientGroup.lift H (toEndHom : G →* Function.End (fixedPoints H A))
    (fun g hg ↦ by funext a; ext; exact a.2 ⟨g, hg⟩)

@[simp]
lemma coe_quotient_smul_fixedPoints (g : G) (a : fixedPoints H A) :
    (g : G ⧸ H) • a = g • a := rfl

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.coe_quotient_smul_fixedPoints := coe_quotient_smul_fixedPoints

@[simp]
lemma quotient_out_smul_fixedPoints (g : G ⧸ H) (a : fixedPoints H A) :
    g.out • a = g • a := by
  conv_rhs => rw [← g.out_eq]
  rfl

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.quotient_out_smul_fixedPoints := quotient_out_smul_fixedPoints

end MonoidAction

namespace MulDistribMulAction

open MonoidAction

variable {G : Type*} [Group G] {A : Type*} [Monoid A] [MulDistribMulAction G A]

variable {H : Subgroup G} [H.Normal]

instance : MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H A) where
  __ := (inferInstance : MonoidAction (G ⧸ H) (fixedPoints H A))
  smul_mul g a b := g.induction_on fun g ↦ Subtype.ext (smul_mul g a.1 b.1)
  smul_one g := g.induction_on fun g ↦ Subtype.ext (smul_one g)

open scoped FixedPoints

variable {α : Type*} [Group α] [MulDistribMulAction G α]

instance : MulDistribMulAction (G ⧸ H) (FixedPoints.subgroup H α) :=
  inferInstanceAs <| MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H α)

end MulDistribMulAction
