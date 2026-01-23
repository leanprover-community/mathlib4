/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# MulAction of quotient group on fixed points

Given a `MulAction` of `G` on `A` and a normal subgroup `H` of `G`,
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

noncomputable instance [hH : H.Normal] :
    MulAction (G ⧸ H) (fixedPoints H A) where
  smul g a := g.out • a
  one_smul a := by
    have := smul_fixedPoints_eq_of_quotient_eq
      (1 : G ⧸ H).out (1 : G) (by simp) a
    ext; simpa
  mul_smul x y a := by
    have := smul_fixedPoints_eq_of_quotient_eq
      (x * y).out (x.out * y.out) (by simp) a
    ext; simpa [mul_smul]

@[simp]
lemma coe_quotient_smul_fixedPoints [H.Normal]
    (g : G) (a : fixedPoints H A) :
    (((g : G ⧸ H) • a) :) = g • (a : A) :=
  smul_fixedPoints_eq_of_quotient_eq (g : G ⧸ H).out g (by simp) a

end MulAction
