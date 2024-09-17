/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!

# Some normal forms of elliptic curves

This file defines some normal forms of Weierstrass equations of elliptic curves.

## Main definitions

- ...

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, normal form

-/

universe u

variable {R : Type u}

namespace WeierstrassCurve

variable (W : WeierstrassCurve R)

/-! ### Normal forms of characteristic ≠ 2
-/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2, if its `a₁` and `a₃` are zero.
In other words it is $Y^2 = X^3 + a_2X^2 + a_4X + a_6$. -/
@[mk_iff]
structure IsNormalFormOfCharNeTwo [Zero R] : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0

section VariableChange

variable [CommRing R] [Invertible (2 : R)]

/-- This is an explicit change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2, provided that 2 is invertible in the ring. -/
@[simps]
def variableChangeToNormalFormOfCharNeTwo : VariableChange R where
  u := 1
  r := 0
  s := ⅟2 * -W.a₁
  t := ⅟2 * -W.a₃

theorem variableChangeToNormalFormOfCharNeTwo_spec :
    (W.variableChange (W.variableChangeToNormalFormOfCharNeTwo)).IsNormalFormOfCharNeTwo := by
  constructor <;> simp [← mul_assoc]

theorem exists_variableChange_isNormalFormOfCharNeTwo :
    ∃ C : VariableChange R, (W.variableChange C).IsNormalFormOfCharNeTwo :=
  ⟨_, W.variableChangeToNormalFormOfCharNeTwo_spec⟩

end VariableChange

namespace IsNormalFormOfCharNeTwo

variable {W}
variable [CommRing R] (self : W.IsNormalFormOfCharNeTwo)
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

end IsNormalFormOfCharNeTwo

end WeierstrassCurve
