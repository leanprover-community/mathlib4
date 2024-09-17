/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.CharP.Defs

/-!

# Some normal forms of elliptic curves

This file defines some normal forms of Weierstrass equations of elliptic curves.
See [silverman2009], section III.1 and Appendix A.

## Main definitions

- ...

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, normal form

-/

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
variable {K : Type*} [Field K] (E : EllipticCurve K)

namespace WeierstrassCurve

/-! ### Normal forms of characteristic different from two -/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2, if its $a_1$ and $a_3$
coefficients are zero. In other words it is $Y^2 = X^3 + a_2X^2 + a_4X + a_6$. -/
@[mk_iff]
structure IsCharNeTwoNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0

namespace IsCharNeTwoNF

variable {W} (self : W.IsCharNeTwoNF)
include self

theorem b₂ : W.b₂ = 4 * W.a₂ := by
  simp_rw [WeierstrassCurve.b₂, self.a₁]
  ring1

theorem b₄ : W.b₄ = 2 * W.a₄ := by
  simp_rw [WeierstrassCurve.b₄, self.a₃]
  ring1

theorem b₆ : W.b₆ = 4 * W.a₆ := by
  simp_rw [WeierstrassCurve.b₆, self.a₃]
  ring1

theorem b₈ : W.b₈ = 4 * W.a₂ * W.a₆ - W.a₄ ^ 2 := by
  simp_rw [WeierstrassCurve.b₈, self.a₁, self.a₃]
  ring1

theorem c₄ : W.c₄ = 16 * W.a₂ ^ 2 - 48 * W.a₄ := by
  simp_rw [WeierstrassCurve.c₄, self.b₂, self.b₄]
  ring1

theorem c₆ : W.c₆ = -64 * W.a₂ ^ 3 + 288 * W.a₂ * W.a₄ - 864 * W.a₆ := by
  simp_rw [WeierstrassCurve.c₆, self.b₂, self.b₄, self.b₆]
  ring1

theorem Δ : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ + 16 * W.a₂ ^ 2 * W.a₄ ^ 2 - 64 * W.a₄ ^ 3
    - 432 * W.a₆ ^ 2 + 288 * W.a₂ * W.a₄ * W.a₆ := by
  simp_rw [WeierstrassCurve.Δ, self.b₂, self.b₄, self.b₆, self.b₈]
  ring1

end IsCharNeTwoNF

section VariableChange

variable [Invertible (2 : R)]

/-- This is an explicit change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2, provided that 2 is invertible in the ring. -/
@[simps]
def vcToCharNeTwoNF : VariableChange R where
  u := 1
  r := 0
  s := ⅟2 * -W.a₁
  t := ⅟2 * -W.a₃

theorem vcToCharNeTwoNF_spec :
    (W.variableChange W.vcToCharNeTwoNF).IsCharNeTwoNF := by
  constructor <;> simp [← mul_assoc]

theorem exists_variableChange_isCharNeTwoNF :
    ∃ C : VariableChange R, (W.variableChange C).IsCharNeTwoNF :=
  ⟨_, W.vcToCharNeTwoNF_spec⟩

end VariableChange

/-! ### Normal forms of characteristic different from two or three -/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2 or 3, if its $a_1$, $a_2$
and $a_3$ coefficients are zero. In other words it is $Y^2 = X^3 + a_4X + a_6$.

This is also the normal form of characteristic = 3 and j = 0. -/
@[mk_iff]
structure IsCharNeTwoThreeNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0

namespace IsCharNeTwoThreeNF

variable {W} (self : W.IsCharNeTwoThreeNF)
include self

theorem isCharNeTwoNF : W.IsCharNeTwoNF := ⟨self.a₁, self.a₃⟩

theorem b₂ : W.b₂ = 0 := by
  simp_rw [WeierstrassCurve.b₂, self.a₁, self.a₂]
  ring1

theorem b₄ : W.b₄ = 2 * W.a₄ := self.isCharNeTwoNF.b₄

theorem b₆ : W.b₆ = 4 * W.a₆ := self.isCharNeTwoNF.b₆

theorem b₈ : W.b₈ = -W.a₄ ^ 2 := by
  simp_rw [WeierstrassCurve.b₈, self.a₁, self.a₂, self.a₃]
  ring1

theorem c₄ : W.c₄ = -48 * W.a₄ := by
  simp_rw [WeierstrassCurve.c₄, self.b₂, self.b₄]
  ring1

theorem c₆ : W.c₆ = -864 * W.a₆ := by
  simp_rw [WeierstrassCurve.c₆, self.b₂, self.b₄, self.b₆]
  ring1

theorem Δ : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  simp_rw [WeierstrassCurve.Δ, self.b₂, self.b₄, self.b₆, self.b₈]
  ring1

theorem Δ_of_char_three [CharP R 3] : W.Δ = -W.a₄ ^ 3 := by
  rw [self.Δ]
  linear_combination (-21 * W.a₄ ^ 3 - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

end IsCharNeTwoThreeNF

namespace IsCharNeTwoThreeNF

variable {E} (self : E.IsCharNeTwoThreeNF)
include self

theorem j : E.j = 6912 * E.a₄ ^ 3 / (4 * E.a₄ ^ 3 + 27 * E.a₆ ^ 2) := by
  have h := E.Δ'.ne_zero
  rw [E.coe_Δ', self.Δ] at h
  rw [EllipticCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, E.coe_Δ',
    self.c₄, self.Δ, div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

theorem j_of_char_three [CharP K 3] : E.j = 0 := by
  rw [self.j]
  have : (6912 : K) = 0 := by linear_combination 2304 * CharP.cast_eq_zero K 3
  simp [this]

end IsCharNeTwoThreeNF

section VariableChange

variable [Invertible (2 : R)] [Invertible (3 : R)]

/-- This is an explicit change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2 or 3, provided that 2 and 3 are invertible in the ring. -/
def vcToCharNeTwoThreeNF : VariableChange R :=
  ⟨1, ⅟3 * -(W.variableChange W.vcToCharNeTwoNF).a₂, 0, 0⟩ * W.vcToCharNeTwoNF

theorem vcToCharNeTwoThreeNF_spec :
    (W.variableChange W.vcToCharNeTwoThreeNF).IsCharNeTwoThreeNF := by
  rw [vcToCharNeTwoThreeNF]; erw [variableChange_comp]
  have H := W.vcToCharNeTwoNF_spec
  set W' := W.variableChange W.vcToCharNeTwoNF
  constructor <;> simp [H.a₁, H.a₃]

theorem exists_variableChange_isCharNeTwoThreeNF :
    ∃ C : VariableChange R, (W.variableChange C).IsCharNeTwoThreeNF :=
  ⟨_, W.vcToCharNeTwoThreeNF_spec⟩

end VariableChange

end WeierstrassCurve
