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
variable {K : Type*} [Field K] (W₁ : WeierstrassCurve K) (E : EllipticCurve K)

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

theorem c₄_of_char_three [CharP R 3] : W.c₄ = 0 := by
  rw [self.c₄]
  linear_combination (-16 * W.a₄) * CharP.cast_eq_zero R 3

theorem c₆_of_char_three [CharP R 3] : W.c₆ = 0 := by
  rw [self.c₆]
  linear_combination (-288 * W.a₆) * CharP.cast_eq_zero R 3

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
  simp [EllipticCurve.j, self.c₄_of_char_three]

end IsCharNeTwoThreeNF

section VariableChange

variable [Invertible (2 : R)] [Invertible (3 : R)]

/-- This is a change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2 or 3, provided that 2 and 3 are invertible in the ring.
It is the composition of an explicit change of variables with `vcToCharNeTwoNF`. -/
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

/-! ### Normal forms of characteristic three and j not equal to zero -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3 and j ≠ 0, if its $a_1$, $a_3$
and $a_4$ coefficients are zero. In other words it is $Y^2 = X^3 + a_2X^2 + a_6$. -/
@[mk_iff]
structure IsCharThreeJNeZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

namespace IsCharThreeJNeZeroNF

variable {W} (self : W.IsCharThreeJNeZeroNF)
include self

theorem isCharNeTwoNF : W.IsCharNeTwoNF := ⟨self.a₁, self.a₃⟩

theorem b₂ : W.b₂ = 4 * W.a₂ := self.isCharNeTwoNF.b₂

theorem b₄ : W.b₄ = 0 := by
  simpa [self.a₄] using self.isCharNeTwoNF.b₄

theorem b₆ : W.b₆ = 4 * W.a₆ := self.isCharNeTwoNF.b₆

theorem b₈ : W.b₈ = 4 * W.a₂ * W.a₆ := by
  simpa [self.a₄] using self.isCharNeTwoNF.b₈

theorem c₄ : W.c₄ = 16 * W.a₂ ^ 2 := by
  simpa [self.a₄] using self.isCharNeTwoNF.c₄

theorem c₆ : W.c₆ = -64 * W.a₂ ^ 3 - 864 * W.a₆ := by
  simpa [self.a₄] using self.isCharNeTwoNF.c₆

theorem Δ : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ - 432 * W.a₆ ^ 2 := by
  simpa [self.a₄] using self.isCharNeTwoNF.Δ

theorem c₄_of_char_three [CharP R 3] : W.c₄ = W.a₂ ^ 2 := by
  rw [self.c₄]
  linear_combination (5 * W.a₂ ^ 2) * CharP.cast_eq_zero R 3

theorem c₆_of_char_three [CharP R 3] : W.c₆ = -W.a₂ ^ 3 := by
  rw [self.c₆]
  linear_combination (-21 * W.a₂ ^ 3 - 288 * W.a₆) * CharP.cast_eq_zero R 3

theorem Δ_of_char_three [CharP R 3] : W.Δ = -W.a₂ ^ 3 * W.a₆ := by
  rw [self.Δ]
  linear_combination (-21 * W.a₂ ^ 3 * W.a₆ - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

end IsCharThreeJNeZeroNF

namespace IsCharThreeJNeZeroNF

variable {E} (self : E.IsCharThreeJNeZeroNF)
include self

theorem j_of_char_three [CharP K 3] : E.j = -E.a₂ ^ 3 / E.a₆ := by
  have h := E.Δ'.ne_zero
  rw [E.coe_Δ', self.Δ_of_char_three] at h
  rw [EllipticCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, E.coe_Δ',
    self.c₄_of_char_three, self.Δ_of_char_three, div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

theorem j_ne_zero_of_char_three [CharP K 3] : E.j ≠ 0 := by
  rw [self.j_of_char_three, div_ne_zero_iff]
  have h := E.Δ'.ne_zero
  rw [E.coe_Δ', self.Δ_of_char_three] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

end IsCharThreeJNeZeroNF

/-! ### Normal forms of characteristic three -/

/-- A `WeierstrassCurve` is in normal form of characteristic 3, if it is
$Y^2 = X^3 + a_2X^2 + a_6$ (`IsCharThreeJNeZeroNF`) or
$Y^2 = X^3 + a_4X + a_6$ (`IsCharNeTwoThreeNF`). -/
def IsCharThreeNF : Prop := W.IsCharThreeJNeZeroNF ∨ W.IsCharNeTwoThreeNF

namespace IsCharThreeNF

variable {W} (self : W.IsCharThreeNF)
include self

theorem isCharNeTwoNF : W.IsCharNeTwoNF :=
  match self with
  | Or.inl h | Or.inr h => h.isCharNeTwoNF

end IsCharThreeNF

section VariableChange

variable [CharP R 3] [CharP K 3]

/-- For a `WeierstrassCurve` defined over a ring of characteristic 3,
there is an explicit change of variables, which changes it to $Y^2 = X^3 + a_4X + a_6$
(`IsCharNeTwoThreeNF`) if its j is zero.
This is in fact given by `vcToCharNeTwoNF`. -/
def vcToCharThreeJZeroNF : VariableChange R :=
  have h : (2 : R) * 2 = 1 := by linear_combination 1 * CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  W.vcToCharNeTwoNF

/-- For a `WeierstrassCurve` defined over a field of characteristic 3,
there is an explicit change of variables of it to `IsCharThreeNF`, that is,
$Y^2 = X^3 + a_2X^2 + a_6$ (`IsCharThreeJNeZeroNF`) or
$Y^2 = X^3 + a_4X + a_6$ (`IsCharNeTwoThreeNF`).
It is the composition of an explicit change of variables with `vcToCharThreeJZeroNF`. -/
def vcToCharThreeNF : VariableChange K :=
  ⟨1, (W₁.variableChange W₁.vcToCharThreeJZeroNF).a₄ /
    (W₁.variableChange W₁.vcToCharThreeJZeroNF).a₂, 0, 0⟩ * W₁.vcToCharThreeJZeroNF

lemma vcToCharThreeJZeroNF_a₂ :
    (W.variableChange W.vcToCharThreeJZeroNF).a₂ = W.b₂ := by
  have h : (2 : R) * 2 = 1 := by linear_combination 1 * CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  simp_rw [vcToCharThreeJZeroNF, vcToCharNeTwoNF, variableChange_a₂, inv_one,
    Units.val_one, b₂]
  linear_combination (-W.a₂ - W.a₁ ^ 2) * CharP.cast_eq_zero R 3

theorem vcToCharThreeJZeroNF_spec (hb₂ : W.b₂ = 0) :
    (W.variableChange W.vcToCharThreeJZeroNF).IsCharNeTwoThreeNF := by
  have h : (2 : R) * 2 = 1 := by linear_combination 1 * CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  have H : (W.variableChange W.vcToCharThreeJZeroNF).IsCharNeTwoNF :=
    W.vcToCharNeTwoNF_spec
  exact ⟨H.a₁, hb₂ ▸ W.vcToCharThreeJZeroNF_a₂, H.a₃⟩

theorem vcToCharThreeNF_spec_of_b₂_ne_zero (hb₂ : W₁.b₂ ≠ 0) :
    (W₁.variableChange W₁.vcToCharThreeNF).IsCharThreeJNeZeroNF := by
  have h : (2 : K) * 2 = 1 := by linear_combination 1 * CharP.cast_eq_zero K 3
  letI : Invertible (2 : K) := ⟨2, h, h⟩
  rw [vcToCharThreeNF]; erw [variableChange_comp]
  rw [← vcToCharThreeJZeroNF_a₂] at hb₂
  set W' := W₁.variableChange W₁.vcToCharThreeJZeroNF
  have H : W'.IsCharNeTwoNF := W₁.vcToCharNeTwoNF_spec
  constructor
  · simp [H.a₁]
  · simp [H.a₁, H.a₃]
  · field_simp [hb₂]
    linear_combination (W'.a₄ * W'.a₂ ^ 2 + W'.a₄ ^ 2) * CharP.cast_eq_zero K 3

theorem vcToCharThreeNF_spec_of_b₂_zero (hb₂ : W₁.b₂ = 0) :
    (W₁.variableChange W₁.vcToCharThreeNF).IsCharNeTwoThreeNF := by
  have h : (2 : K) * 2 = 1 := by linear_combination 1 * CharP.cast_eq_zero K 3
  letI : Invertible (2 : K) := ⟨2, h, h⟩
  rw [vcToCharThreeNF, vcToCharThreeJZeroNF_a₂, hb₂, div_zero]
  erw [one_mul]
  exact W₁.vcToCharThreeJZeroNF_spec hb₂

theorem vcToCharThreeNF_spec :
    (W₁.variableChange W₁.vcToCharThreeNF).IsCharThreeNF := by
  by_cases hb₂ : W₁.b₂ = 0
  · exact Or.inr (W₁.vcToCharThreeNF_spec_of_b₂_zero hb₂)
  · exact Or.inl (W₁.vcToCharThreeNF_spec_of_b₂_ne_zero hb₂)

theorem exists_variableChange_isCharThreeNF :
    ∃ C : VariableChange K, (W₁.variableChange C).IsCharThreeNF :=
  ⟨_, W₁.vcToCharThreeNF_spec⟩

end VariableChange

end WeierstrassCurve
