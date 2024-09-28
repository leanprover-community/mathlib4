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

## Main definitions and results

The following normal forms are in [silverman2009], section III.1, page 42.

- `WeierstrassCurve.IsCharNeTwoNF` is a predicate which asserts that a `WeierstrassCurve` is
  of form $Y^2 = X^3 + a_2X^2 + a_4X + a_6$. It is the normal form of characteristic ≠ 2.

  If 2 is invertible in the ring (for example, if it is a field of characteristic ≠ 2),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isCharNeTwoNF`).
  See also `WeierstrassCurve.toCharNeTwoNF` and
  `WeierstrassCurve.toCharNeTwoNF_spec`.

The following normal forms are in [silverman2009], Appendix A, Proposition 1.1.

- `WeierstrassCurve.IsCharNeTwoThreeNF` is a predicate which asserts that a `WeierstrassCurve` is
  of form $Y^2 = X^3 + a_4X + a_6$. It is the normal form of characteristic ≠ 2.
  It is also the normal form of characteristic = 3 and j = 0.

  If 2 and 3 are invertible in the ring (for example, if it is a field of characteristic ≠ 2 or 3),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isCharNeTwoThreeNF`).
  See also `WeierstrassCurve.toCharNeTwoThreeNF` and
  `WeierstrassCurve.toCharNeTwoThreeNF_spec`.

  If the ring is of characteristic = 3 and the $b_2$ of the curve = 0 (for an elliptic curve,
  this is equivalent to j = 0), then there exists a change of variables which will change
  it into such normal form (see `WeierstrassCurve.toCharThreeJZeroNF`
  and `WeierstrassCurve.toCharThreeJZeroNF_spec`).

- `WeierstrassCurve.IsCharThreeJNeZeroNF` is a predicate which asserts that a `WeierstrassCurve` is
  of form $Y^2 = X^3 + a_2X^2 + a_6$. It is the normal form of characteristic = 3 and j ≠ 0.

  If the field is of characteristic = 3 and the $b_2$ of the curve ≠ 0 (for an elliptic curve,
  this is equivalent to j ≠ 0), then there exists a change of variables which will change
  it into such normal form (see `WeierstrassCurve.toCharThreeNF`
  and `WeierstrassCurve.toCharThreeNF_spec_of_b₂_ne_zero`).

- `WeierstrassCurve.IsCharThreeNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form $Y^2 = X^3 + a_2X^2 + a_6$ or $Y^2 = X^3 + a_4X + a_6$.
  It is the normal form of characteristic = 3.

  If the field is of characteristic = 3, then there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isCharThreeNF`).
  See also `WeierstrassCurve.toCharThreeNF` and
  `WeierstrassCurve.toCharThreeNF_spec`.

- `WeierstrassCurve.IsCharTwoJZeroNF` is a predicate which asserts that a `WeierstrassCurve` is
  of form $Y^2 + a_3Y = X^3 + a_4X + a_6$. It is the normal form of characteristic = 2 and j = 0.

  If the ring is of characteristic = 2 and the $a_1$ of the curve = 0 (for an elliptic curve,
  this is equivalent to j = 0), then there exists a change of variables which will change
  it into such normal form (see `WeierstrassCurve.toCharTwoJZeroNF`
  and `WeierstrassCurve.toCharTwoJZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoJNeZeroNF` is a predicate which asserts that a `WeierstrassCurve` is
  of form $Y^2 + XY = X^3 + a_2X^2 + a_6$. It is the normal form of characteristic = 2 and j ≠ 0.

  If the field is of characteristic = 2 and the $a_1$ of the curve ≠ 0 (for an elliptic curve,
  this is equivalent to j ≠ 0), then there exists a change of variables which will change
  it into such normal form (see `WeierstrassCurve.toCharTwoJNeZeroNF`
  and `WeierstrassCurve.toCharTwoJNeZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form $Y^2 + XY = X^3 + a_2X^2 + a_6$ or
  $Y^2 + a_3Y = X^3 + a_4X + a_6$.
  It is the normal form of characteristic = 2.

  If the field is of characteristic = 2, then there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isCharTwoNF`).
  See also `WeierstrassCurve.toCharTwoNF` and
  `WeierstrassCurve.toCharTwoNF_spec`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, normal form

-/

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
variable {K : Type*} [Field K] (W₁ : WeierstrassCurve K) (E : EllipticCurve K)

namespace WeierstrassCurve

/-! ### Normal forms of characteristic ≠ 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2, if its $a_1, a_3 = 0$.
In other words it is $Y^2 = X^3 + a_2X^2 + a_4X + a_6$. -/
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
def toCharNeTwoNF : VariableChange R where
  u := 1
  r := 0
  s := ⅟2 * -W.a₁
  t := ⅟2 * -W.a₃

theorem toCharNeTwoNF_spec :
    (W.variableChange W.toCharNeTwoNF).IsCharNeTwoNF := by
  constructor <;> simp [← mul_assoc]

theorem exists_variableChange_isCharNeTwoNF :
    ∃ C : VariableChange R, (W.variableChange C).IsCharNeTwoNF :=
  ⟨_, W.toCharNeTwoNF_spec⟩

end VariableChange

/-! ### Normal forms of characteristic ≠ 2 or 3 -/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2 or 3, if its $a_1, a_2, a_3 = 0$.
In other words it is $Y^2 = X^3 + a_4X + a_6$.

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
  linear_combination -16 * W.a₄ * CharP.cast_eq_zero R 3

theorem c₆_of_char_three [CharP R 3] : W.c₆ = 0 := by
  rw [self.c₆]
  linear_combination -288 * W.a₆ * CharP.cast_eq_zero R 3

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
It is the composition of an explicit change of variables with `toCharNeTwoNF`. -/
def toCharNeTwoThreeNF : VariableChange R :=
  ⟨1, ⅟3 * -(W.variableChange W.toCharNeTwoNF).a₂, 0, 0⟩ * W.toCharNeTwoNF

theorem toCharNeTwoThreeNF_spec :
    (W.variableChange W.toCharNeTwoThreeNF).IsCharNeTwoThreeNF := by
  rw [toCharNeTwoThreeNF]; erw [variableChange_comp]
  have H := W.toCharNeTwoNF_spec
  set W' := W.variableChange W.toCharNeTwoNF
  constructor <;> simp [H.a₁, H.a₃]

theorem exists_variableChange_isCharNeTwoThreeNF :
    ∃ C : VariableChange R, (W.variableChange C).IsCharNeTwoThreeNF :=
  ⟨_, W.toCharNeTwoThreeNF_spec⟩

end VariableChange

/-! ### Normal forms of characteristic = 3 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3 and j ≠ 0, if its
$a_1, a_3, a_4 = 0$. In other words it is $Y^2 = X^3 + a_2X^2 + a_6$. -/
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
  linear_combination 5 * W.a₂ ^ 2 * CharP.cast_eq_zero R 3

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

/-! ### Normal forms of characteristic = 3 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3, if it is
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

/-- For a `WeierstrassCurve` defined over a ring of characteristic = 3,
there is an explicit change of variables, which changes it to $Y^2 = X^3 + a_4X + a_6$
(`IsCharNeTwoThreeNF`) if its j = 0.
This is in fact given by `toCharNeTwoNF`. -/
def toCharThreeJZeroNF : VariableChange R :=
  have h : (2 : R) * 2 = 1 := by linear_combination 1 * CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  W.toCharNeTwoNF

/-- For a `WeierstrassCurve` defined over a field of characteristic = 3,
there is an explicit change of variables of it to `IsCharThreeNF`, that is,
$Y^2 = X^3 + a_2X^2 + a_6$ (`IsCharThreeJNeZeroNF`) or
$Y^2 = X^3 + a_4X + a_6$ (`IsCharNeTwoThreeNF`).
It is the composition of an explicit change of variables with `toCharThreeJZeroNF`. -/
def toCharThreeNF : VariableChange K :=
  ⟨1, (W₁.variableChange W₁.toCharThreeJZeroNF).a₄ /
    (W₁.variableChange W₁.toCharThreeJZeroNF).a₂, 0, 0⟩ * W₁.toCharThreeJZeroNF

lemma toCharThreeJZeroNF_a₂ :
    (W.variableChange W.toCharThreeJZeroNF).a₂ = W.b₂ := by
  simp_rw [toCharThreeJZeroNF, toCharNeTwoNF, variableChange_a₂, inv_one,
    Units.val_one, b₂]
  linear_combination (-W.a₂ - W.a₁ ^ 2) * CharP.cast_eq_zero R 3

theorem toCharThreeJZeroNF_spec (hb₂ : W.b₂ = 0) :
    (W.variableChange W.toCharThreeJZeroNF).IsCharNeTwoThreeNF := by
  have h : (2 : R) * 2 = 1 := by linear_combination 1 * CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  have H := W.toCharNeTwoNF_spec
  exact ⟨H.a₁, hb₂ ▸ W.toCharThreeJZeroNF_a₂, H.a₃⟩

theorem toCharThreeNF_spec_of_b₂_ne_zero (hb₂ : W₁.b₂ ≠ 0) :
    (W₁.variableChange W₁.toCharThreeNF).IsCharThreeJNeZeroNF := by
  have h : (2 : K) * 2 = 1 := by linear_combination 1 * CharP.cast_eq_zero K 3
  letI : Invertible (2 : K) := ⟨2, h, h⟩
  rw [toCharThreeNF]; erw [variableChange_comp]
  rw [← toCharThreeJZeroNF_a₂] at hb₂
  set W' := W₁.variableChange W₁.toCharThreeJZeroNF
  have H : W'.IsCharNeTwoNF := W₁.toCharNeTwoNF_spec
  constructor
  · simp [H.a₁]
  · simp [H.a₁, H.a₃]
  · field_simp
    linear_combination (W'.a₄ * W'.a₂ ^ 2 + W'.a₄ ^ 2) * CharP.cast_eq_zero K 3

theorem toCharThreeNF_spec_of_b₂_zero (hb₂ : W₁.b₂ = 0) :
    (W₁.variableChange W₁.toCharThreeNF).IsCharNeTwoThreeNF := by
  rw [toCharThreeNF, toCharThreeJZeroNF_a₂, hb₂, div_zero]
  erw [one_mul]
  exact W₁.toCharThreeJZeroNF_spec hb₂

theorem toCharThreeNF_spec :
    (W₁.variableChange W₁.toCharThreeNF).IsCharThreeNF := by
  by_cases hb₂ : W₁.b₂ = 0
  · exact Or.inr (W₁.toCharThreeNF_spec_of_b₂_zero hb₂)
  · exact Or.inl (W₁.toCharThreeNF_spec_of_b₂_ne_zero hb₂)

theorem exists_variableChange_isCharThreeNF :
    ∃ C : VariableChange K, (W₁.variableChange C).IsCharThreeNF :=
  ⟨_, W₁.toCharThreeNF_spec⟩

end VariableChange

/-! ### Normal forms of characteristic = 2 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j ≠ 0, if its $a_1 = 1$,
$a_3, a_4 = 0$. In other words it is $Y^2 + XY = X^3 + a_2X^2 + a_6$. -/
@[mk_iff]
structure IsCharTwoJNeZeroNF : Prop where
  a₁ : W.a₁ = 1
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

-- TODO: move to suitable location ???
theorem b₂_of_char_two [CharP R 2] : W.b₂ = W.a₁ ^ 2 := by
  rw [b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

-- TODO: move to suitable location ???
theorem b₄_of_char_two [CharP R 2] : W.b₄ = W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

-- TODO: move to suitable location ???
theorem b₆_of_char_two [CharP R 2] : W.b₆ = W.a₃ ^ 2 := by
  rw [b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

-- TODO: move to suitable location ???
theorem c₄_of_char_two [CharP R 2] : W.c₄ = W.a₁ ^ 4 := by
  rw [c₄, b₂_of_char_two]
  linear_combination -12 * W.b₄ * CharP.cast_eq_zero R 2

-- TODO: move to suitable location ???
theorem c₆_of_char_two [CharP R 2] : W.c₆ = -W.a₁ ^ 6 := by
  rw [c₆, b₂_of_char_two]
  linear_combination (18 * W.a₁ ^ 2 * W.b₄ - 108 * W.b₆) * CharP.cast_eq_zero R 2

namespace IsCharTwoJNeZeroNF

variable {W} (self : W.IsCharTwoJNeZeroNF)
include self

theorem b₂ : W.b₂ = 1 + 4 * W.a₂ := by
  simp_rw [WeierstrassCurve.b₂, self.a₁]
  ring1

theorem b₄ : W.b₄ = 0 := by
  simp_rw [WeierstrassCurve.b₄, self.a₃, self.a₄]
  ring1

theorem b₆ : W.b₆ = 4 * W.a₆ := by
  simp_rw [WeierstrassCurve.b₆, self.a₃]
  ring1

theorem b₈ : W.b₈ = W.a₆ + 4 * W.a₂ * W.a₆ := by
  simp_rw [WeierstrassCurve.b₈, self.a₁, self.a₃, self.a₄]
  ring1

theorem c₄ : W.c₄ = W.b₂ ^ 2 := by
  simp_rw [WeierstrassCurve.c₄, self.b₄]
  ring1

theorem c₆ : W.c₆ = -W.b₂ ^ 3 - 864 * W.a₆ := by
  simp_rw [WeierstrassCurve.c₆, self.b₄, self.b₆]
  ring1

variable [CharP R 2]

theorem b₂_of_char_two : W.b₂ = 1 := by
  rw [self.b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

theorem b₆_of_char_two : W.b₆ = 0 := by
  rw [self.b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

theorem b₈_of_char_two : W.b₈ = W.a₆ := by
  rw [self.b₈]
  linear_combination 2 * W.a₂ * W.a₆ * CharP.cast_eq_zero R 2

theorem c₄_of_char_two : W.c₄ = 1 := by
  rw [self.c₄, self.b₂_of_char_two]
  ring1

theorem c₆_of_char_two : W.c₆ = 1 := by
  rw [self.c₆, self.b₂_of_char_two]
  linear_combination (-1 - 432 * W.a₆) * CharP.cast_eq_zero R 2

theorem Δ_of_char_two : W.Δ = W.a₆ := by
  simp_rw [WeierstrassCurve.Δ, self.b₂_of_char_two, self.b₄,
    self.b₆_of_char_two, self.b₈_of_char_two]
  linear_combination -W.a₆ * CharP.cast_eq_zero R 2

end IsCharTwoJNeZeroNF

namespace IsCharTwoJNeZeroNF

variable {E} (self : E.IsCharTwoJNeZeroNF)
include self

theorem j_of_char_two [CharP K 2] : E.j = 1 / E.a₆ := by
  rw [EllipticCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, E.coe_Δ',
    self.c₄_of_char_two, self.Δ_of_char_two, one_pow]

theorem j_ne_zero_of_char_two [CharP K 2] : E.j ≠ 0 := by
  rw [self.j_of_char_two, div_ne_zero_iff]
  have h := E.Δ'.ne_zero
  rw [E.coe_Δ', self.Δ_of_char_two] at h
  exact ⟨one_ne_zero, h⟩

end IsCharTwoJNeZeroNF

/-! ### Normal forms of characteristic = 2 and j = 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j = 0, if its
$a_1, a_2 = 0$. In other words it is $Y^2 + a_3Y = X^3 + a_4X + a_6$. -/
@[mk_iff]
structure IsCharTwoJZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0

namespace IsCharTwoJZeroNF

variable {W} (self : W.IsCharTwoJZeroNF)
include self

theorem b₂ : W.b₂ = 0 := by
  simp_rw [WeierstrassCurve.b₂, self.a₁, self.a₂]
  ring1

theorem b₄ : W.b₄ = 2 * W.a₄ := by
  simp_rw [WeierstrassCurve.b₄, self.a₁]
  ring1

theorem b₈ : W.b₈ = -W.a₄ ^ 2 := by
  simp_rw [WeierstrassCurve.b₈, self.a₁, self.a₂]
  ring1

theorem c₄ : W.c₄ = -48 * W.a₄ := by
  simp_rw [WeierstrassCurve.c₄, self.b₂, self.b₄]
  ring1

theorem c₆ : W.c₆ = -216 * W.b₆ := by
  simp_rw [WeierstrassCurve.c₆, self.b₂, self.b₄]
  ring1

theorem Δ : W.Δ = -64 * W.a₄ ^ 3 - 27 * W.b₆ ^ 2 := by
  simp_rw [WeierstrassCurve.Δ, self.b₂, self.b₄]
  ring1

variable [CharP R 2]

theorem b₄_of_char_two : W.b₄ = 0 := by
  rw [self.b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

theorem c₄_of_char_two : W.c₄ = 0 := by
  rw [self.c₄]
  linear_combination -24 * W.a₄ * CharP.cast_eq_zero R 2

theorem c₆_of_char_two : W.c₆ = 0 := by
  rw [self.c₆]
  linear_combination -108 * W.b₆ * CharP.cast_eq_zero R 2

theorem Δ_of_char_two : W.Δ = W.a₃ ^ 4 := by
  rw [self.Δ, W.b₆_of_char_two]
  linear_combination (-32 * W.a₄ ^ 3 - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

end IsCharTwoJZeroNF

namespace IsCharTwoJZeroNF

variable {E} (self : E.IsCharTwoJZeroNF)
include self

theorem j_of_char_two [CharP K 2] : E.j = 0 := by
  simp [EllipticCurve.j, self.c₄_of_char_two]

end IsCharTwoJZeroNF

/-! ### Normal forms of characteristic = 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2, if it is
$Y^2 + XY = X^3 + a_2X^2 + a_6$ (`IsCharTwoJNeZeroNF`) or
$Y^2 + a_3Y = X^3 + a_4X + a_6$ (`IsCharTwoJZeroNF`). -/
def IsCharTwoNF : Prop := W.IsCharTwoJNeZeroNF ∨ W.IsCharTwoJZeroNF

section VariableChange

variable [CharP R 2] [CharP K 2]

/-- For a `WeierstrassCurve` defined over a ring of characteristic = 2,
there is an explicit change of variables, which changes it to $Y^2 + a_3Y = X^3 + a_4X + a_6$
(`IsCharTwoJZeroNF`) if its j = 0. -/
def toCharTwoJZeroNF : VariableChange R := ⟨1, W.a₂, 0, 0⟩

/-- For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables, which changes it to $Y^2 + XY = X^3 + a_2X^2 + a_6$
(`IsCharTwoJNeZeroNF`) if its j ≠ 0. -/
def toCharTwoJNeZeroNF (ha₁ : W₁.a₁ ≠ 0) : VariableChange K :=
  ⟨Units.mk0 _ ha₁, W₁.a₃ / W₁.a₁, 0, (W₁.a₁ ^ 2 * W₁.a₄ + W₁.a₃ ^ 2) / W₁.a₁ ^ 3⟩

theorem toCharTwoJZeroNF_spec (ha₁ : W.a₁ = 0) :
    (W.variableChange W.toCharTwoJZeroNF).IsCharTwoJZeroNF := by
  constructor
  · simp [toCharTwoJZeroNF, ha₁]
  · simp [toCharTwoJZeroNF, show W.a₂ + 3 * W.a₂ = 0 by
      linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2]

theorem toCharTwoJNeZeroNF_spec (ha₁ : W₁.a₁ ≠ 0) :
    (W₁.variableChange (W₁.toCharTwoJNeZeroNF ha₁)).IsCharTwoJNeZeroNF := by
  constructor
  · simp [toCharTwoJNeZeroNF, ha₁]
  · field_simp [toCharTwoJNeZeroNF]
    linear_combination (W₁.a₃ * W₁.a₁ ^ 3 + W₁.a₁ ^ 2 * W₁.a₄ + W₁.a₃ ^ 2) * CharP.cast_eq_zero K 2
  · field_simp [toCharTwoJNeZeroNF]
    linear_combination (W₁.a₁ ^ 4 * W₁.a₃ ^ 2 + W₁.a₁ ^ 5 * W₁.a₃ * W₁.a₂) * CharP.cast_eq_zero K 2

/-- For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `IsCharTwoNF`, that is,
$Y^2 + XY = X^3 + a_2X^2 + a_6$ (`IsCharTwoJNeZeroNF`) or
$Y^2 + a_3Y = X^3 + a_4X + a_6$ (`IsCharTwoJZeroNF`). -/
def toCharTwoNF [DecidableEq K] : VariableChange K :=
  if ha₁ : W₁.a₁ = 0 then W₁.toCharTwoJZeroNF else W₁.toCharTwoJNeZeroNF ha₁

theorem toCharTwoNF_spec [DecidableEq K] :
    (W₁.variableChange W₁.toCharTwoNF).IsCharTwoNF := by
  by_cases ha₁ : W₁.a₁ = 0
  · rw [toCharTwoNF, dif_pos ha₁]
    exact Or.inr (W₁.toCharTwoJZeroNF_spec ha₁)
  · rw [toCharTwoNF, dif_neg ha₁]
    exact Or.inl (W₁.toCharTwoJNeZeroNF_spec ha₁)

open scoped Classical in
theorem exists_variableChange_isCharTwoNF :
    ∃ C : VariableChange K, (W₁.variableChange C).IsCharTwoNF :=
  ⟨_, W₁.toCharTwoNF_spec⟩

end VariableChange

end WeierstrassCurve
