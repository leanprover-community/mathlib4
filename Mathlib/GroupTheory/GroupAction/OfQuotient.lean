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

variable {H : Subgroup G}

lemma smul_fixedPoints_eq_of_quotient_eq
    (g₁ g₂ : G) (hg : (g₁ : G ⧸ H) = g₂) (a : fixedPoints H A) :
    g₁ • (a : A) = g₂ • a := by
  rw [← eq_inv_smul_iff, ← mul_smul]
  symm; exact a.prop ⟨g₁⁻¹ * g₂, QuotientGroup.eq.mp hg⟩

instance [hH : H.Normal] :
    MulAction (G ⧸ H) (fixedPoints H A) :=
  ofEndHom <|
    QuotientGroup.lift H (toEndHom : G →* Function.End (fixedPoints H A))
    (fun x hx => by sorry)--simpa [toEndHom, smul_fixedPoints_eq_of_quotient_eq x 1] using hx)
  /- one_smul a := by
    ext; rw [← one_smul G (a : A)]; rfl
  mul_smul x y a := by
    have := smul_fixedPoints_eq_of_quotient_eq (x * y).out (x.out * y.out) (by simp) a
    ext; sorry; -/

@[simp]
lemma coe_quotient_smul_fixedPoints [H.Normal]
    (g : G) (a : fixedPoints H A) :
    (((g : G ⧸ H) • a) :) = g • (a : A) := rfl

lemma quotient_smul_fixedPoints_def [H.Normal]
    (g : G ⧸ H) (a : fixedPoints H A) :
    g • a = g.out • a := by
  ext; simpa using coe_quotient_smul_fixedPoints g.out a

end MulAction
