/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!

# Some normal forms of elliptic curves

This file defines some normal forms of Weierstrass equations of elliptic curves.

## Main definitions and results

The following normal forms are in [silverman2009], section III.1, page 42.

- `WeierstrassCurve.IsCharNeTwoNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₂X² + a₄X + a₆`. It is the normal form of characteristic ≠ 2.

  If 2 is invertible in the ring (for example, if it is a field of characteristic ≠ 2),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isCharNeTwoNF`).
  See also `WeierstrassCurve.toCharNeTwoNF` and `WeierstrassCurve.toCharNeTwoNF_spec`.

The following normal forms are in [silverman2009], Appendix A, Proposition 1.1.

- `WeierstrassCurve.IsShortNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₄X + a₆`. It is the normal form of characteristic ≠ 2 or 3, and
  also the normal form of characteristic = 3 and j = 0.

  If 2 and 3 are invertible in the ring (for example, if it is a field of characteristic ≠ 2 or 3),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isShortNF`).
  See also `WeierstrassCurve.toShortNF` and `WeierstrassCurve.toShortNF_spec`.

  If the ring is of characteristic = 3, then for any `WeierstrassCurve` with `b₂ = 0` (for an
  elliptic curve, this is equivalent to j = 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toShortNFOfCharThree`
  and `WeierstrassCurve.toShortNFOfCharThree_spec`).

- `WeierstrassCurve.IsCharThreeJNeZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₂X² + a₆`. It is the normal form of characteristic = 3 and j ≠ 0.

  If the field is of characteristic = 3, then for any `WeierstrassCurve` with `b₂ ≠ 0` (for an
  elliptic curve, this is equivalent to j ≠ 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharThreeNF`
  and `WeierstrassCurve.toCharThreeNF_spec_of_b₂_ne_zero`).

- `WeierstrassCurve.IsCharThreeNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form `Y² = X³ + a₂X² + a₆` or `Y² = X³ + a₄X + a₆`.
  It is the normal form of characteristic = 3.

  If the field is of characteristic = 3, then for any `WeierstrassCurve` there exists a change of
  variables which will change it into such normal form
  (`WeierstrassCurve.exists_variableChange_isCharThreeNF`).
  See also `WeierstrassCurve.toCharThreeNF` and `WeierstrassCurve.toCharThreeNF_spec`.

- `WeierstrassCurve.IsCharTwoJEqZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² + a₃Y = X³ + a₄X + a₆`. It is the normal form of characteristic = 2 and j = 0.

  If the ring is of characteristic = 2, then for any `WeierstrassCurve` with `a₁ = 0` (for an
  elliptic curve, this is equivalent to j = 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharTwoJEqZeroNF`
  and `WeierstrassCurve.toCharTwoJEqZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoJNeZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² + XY = X³ + a₂X² + a₆`. It is the normal form of characteristic = 2 and j ≠ 0.

  If the field is of characteristic = 2, then for any `WeierstrassCurve` with `a₁ ≠ 0` (for an
  elliptic curve, this is equivalent to j ≠ 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharTwoJNeZeroNF`
  and `WeierstrassCurve.toCharTwoJNeZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form `Y² + XY = X³ + a₂X² + a₆` or
  `Y² + a₃Y = X³ + a₄X + a₆`. It is the normal form of characteristic = 2.

  If the field is of characteristic = 2, then for any `WeierstrassCurve` there exists a change of
  variables which will change it into such normal form
  (`WeierstrassCurve.exists_variableChange_isCharTwoNF`).
  See also `WeierstrassCurve.toCharTwoNF` and `WeierstrassCurve.toCharTwoNF_spec`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, normal form

-/

@[expose] public section

variable {R : Type*} [CommRing R] {F : Type*} [Field F] (W : WeierstrassCurve R)

namespace WeierstrassCurve

/-! ## Normal forms of characteristic ≠ 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2, if its `a₁, a₃ = 0`.
In other words it is `Y² = X³ + a₂X² + a₄X + a₆`. -/
@[mk_iff]
class IsCharNeTwoNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0

section Quantity

variable [W.IsCharNeTwoNF]

@[simp]
theorem a₁_of_isCharNeTwoNF : W.a₁ = 0 := IsCharNeTwoNF.a₁

@[simp]
theorem a₃_of_isCharNeTwoNF : W.a₃ = 0 := IsCharNeTwoNF.a₃

@[simp]
theorem b₂_of_isCharNeTwoNF : W.b₂ = 4 * W.a₂ := by
  rw [b₂, a₁_of_isCharNeTwoNF]
  ring1

@[simp]
theorem b₄_of_isCharNeTwoNF : W.b₄ = 2 * W.a₄ := by
  rw [b₄, a₃_of_isCharNeTwoNF]
  ring1

@[simp]
theorem b₆_of_isCharNeTwoNF : W.b₆ = 4 * W.a₆ := by
  rw [b₆, a₃_of_isCharNeTwoNF]
  ring1

@[simp]
theorem b₈_of_isCharNeTwoNF : W.b₈ = 4 * W.a₂ * W.a₆ - W.a₄ ^ 2 := by
  rw [b₈, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring1

@[simp]
theorem c₄_of_isCharNeTwoNF : W.c₄ = 16 * W.a₂ ^ 2 - 48 * W.a₄ := by
  rw [c₄, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF]
  ring1

@[simp]
theorem c₆_of_isCharNeTwoNF : W.c₆ = -64 * W.a₂ ^ 3 + 288 * W.a₂ * W.a₄ - 864 * W.a₆ := by
  rw [c₆, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF, b₆_of_isCharNeTwoNF]
  ring1

@[simp]
theorem Δ_of_isCharNeTwoNF : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ + 16 * W.a₂ ^ 2 * W.a₄ ^ 2 - 64 * W.a₄ ^ 3
    - 432 * W.a₆ ^ 2 + 288 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Δ, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF, b₆_of_isCharNeTwoNF, b₈_of_isCharNeTwoNF]
  ring1

end Quantity

section VariableChange

variable [Invertible (2 : R)]

/-- There is an explicit change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2, provided that 2 is invertible in the ring. -/
@[simps]
def toCharNeTwoNF : VariableChange R := ⟨1, 0, ⅟2 * -W.a₁, ⅟2 * -W.a₃⟩

instance toCharNeTwoNF_spec : (W.toCharNeTwoNF • W).IsCharNeTwoNF := by
  constructor <;> simp [variableChange_a₁, variableChange_a₃]

theorem exists_variableChange_isCharNeTwoNF : ∃ C : VariableChange R, (C • W).IsCharNeTwoNF :=
  ⟨_, W.toCharNeTwoNF_spec⟩

end VariableChange

/-! ## Short normal form -/

/-- A `WeierstrassCurve` is in short normal form, if its `a₁, a₂, a₃ = 0`.
In other words it is `Y² = X³ + a₄X + a₆`.

This is the normal form of characteristic ≠ 2 or 3, and
also the normal form of characteristic = 3 and j = 0. -/
@[mk_iff]
class IsShortNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0

section Quantity

variable [W.IsShortNF]

instance isCharNeTwoNF_of_isShortNF : W.IsCharNeTwoNF := ⟨IsShortNF.a₁, IsShortNF.a₃⟩

theorem a₁_of_isShortNF : W.a₁ = 0 := IsShortNF.a₁

@[simp]
theorem a₂_of_isShortNF : W.a₂ = 0 := IsShortNF.a₂

theorem a₃_of_isShortNF : W.a₃ = 0 := IsShortNF.a₃

theorem b₂_of_isShortNF : W.b₂ = 0 := by
  simp

theorem b₄_of_isShortNF : W.b₄ = 2 * W.a₄ := W.b₄_of_isCharNeTwoNF

theorem b₆_of_isShortNF : W.b₆ = 4 * W.a₆ := W.b₆_of_isCharNeTwoNF

theorem b₈_of_isShortNF : W.b₈ = -W.a₄ ^ 2 := by
  simp

theorem c₄_of_isShortNF : W.c₄ = -48 * W.a₄ := by
  simp

theorem c₆_of_isShortNF : W.c₆ = -864 * W.a₆ := by
  simp

theorem Δ_of_isShortNF : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  rw [Δ_of_isCharNeTwoNF, a₂_of_isShortNF]
  ring1

variable [CharP R 3]

theorem b₄_of_isShortNF_of_char_three : W.b₄ = -W.a₄ := by
  rw [b₄_of_isShortNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

theorem b₆_of_isShortNF_of_char_three : W.b₆ = W.a₆ := by
  rw [b₆_of_isShortNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

theorem c₄_of_isShortNF_of_char_three : W.c₄ = 0 := by
  rw [c₄_of_isShortNF]
  linear_combination -16 * W.a₄ * CharP.cast_eq_zero R 3

theorem c₆_of_isShortNF_of_char_three : W.c₆ = 0 := by
  rw [c₆_of_isShortNF]
  linear_combination -288 * W.a₆ * CharP.cast_eq_zero R 3

theorem Δ_of_isShortNF_of_char_three : W.Δ = -W.a₄ ^ 3 := by
  rw [Δ_of_isShortNF]
  linear_combination (-21 * W.a₄ ^ 3 - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]

theorem j_of_isShortNF : W.j = 6912 * W.a₄ ^ 3 / (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isShortNF] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isShortNF, Δ_of_isShortNF, div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

@[simp]
theorem j_of_isShortNF_of_char_three [CharP F 3] : W.j = 0 := by
  rw [j, c₄_of_isShortNF_of_char_three]; simp

end Quantity

section VariableChange

variable [Invertible (2 : R)] [Invertible (3 : R)]

/-- There is an explicit change of variables of a `WeierstrassCurve` to
a short normal form, provided that 2 and 3 are invertible in the ring.
It is the composition of an explicit change of variables with `WeierstrassCurve.toCharNeTwoNF`. -/
def toShortNF : VariableChange R :=
  ⟨1, ⅟3 * -(W.toCharNeTwoNF • W).a₂, 0, 0⟩ * W.toCharNeTwoNF

instance toShortNF_spec : (W.toShortNF • W).IsShortNF := by
  rw [toShortNF, mul_smul]
  constructor <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃]

theorem exists_variableChange_isShortNF : ∃ C : VariableChange R, (C • W).IsShortNF :=
  ⟨_, W.toShortNF_spec⟩

end VariableChange

/-! ## Normal forms of characteristic = 3 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3 and j ≠ 0, if its
`a₁, a₃, a₄ = 0`. In other words it is `Y² = X³ + a₂X² + a₆`. -/
@[mk_iff]
class IsCharThreeJNeZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

section Quantity

variable [W.IsCharThreeJNeZeroNF]

instance isCharNeTwoNF_of_isCharThreeJNeZeroNF : W.IsCharNeTwoNF :=
  ⟨IsCharThreeJNeZeroNF.a₁, IsCharThreeJNeZeroNF.a₃⟩

theorem a₁_of_isCharThreeJNeZeroNF : W.a₁ = 0 := IsCharThreeJNeZeroNF.a₁

theorem a₃_of_isCharThreeJNeZeroNF : W.a₃ = 0 := IsCharThreeJNeZeroNF.a₃

@[simp]
theorem a₄_of_isCharThreeJNeZeroNF : W.a₄ = 0 := IsCharThreeJNeZeroNF.a₄

theorem b₂_of_isCharThreeJNeZeroNF : W.b₂ = 4 * W.a₂ := W.b₂_of_isCharNeTwoNF

theorem b₄_of_isCharThreeJNeZeroNF : W.b₄ = 0 := by
  simp

theorem b₆_of_isCharThreeJNeZeroNF : W.b₆ = 4 * W.a₆ := W.b₆_of_isCharNeTwoNF

theorem b₈_of_isCharThreeJNeZeroNF : W.b₈ = 4 * W.a₂ * W.a₆ := by
  simp

theorem c₄_of_isCharThreeJNeZeroNF : W.c₄ = 16 * W.a₂ ^ 2 := by
  simp

theorem c₆_of_isCharThreeJNeZeroNF : W.c₆ = -64 * W.a₂ ^ 3 - 864 * W.a₆ := by
  simp

theorem Δ_of_isCharThreeJNeZeroNF : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ - 432 * W.a₆ ^ 2 := by
  simp

variable [CharP R 3]

theorem b₂_of_isCharThreeJNeZeroNF_of_char_three : W.b₂ = W.a₂ := by
  rw [b₂_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

theorem b₆_of_isCharThreeJNeZeroNF_of_char_three : W.b₆ = W.a₆ := by
  rw [b₆_of_isCharThreeJNeZeroNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

theorem b₈_of_isCharThreeJNeZeroNF_of_char_three : W.b₈ = W.a₂ * W.a₆ := by
  rw [b₈_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

theorem c₄_of_isCharThreeJNeZeroNF_of_char_three : W.c₄ = W.a₂ ^ 2 := by
  rw [c₄_of_isCharThreeJNeZeroNF]
  linear_combination 5 * W.a₂ ^ 2 * CharP.cast_eq_zero R 3

theorem c₆_of_isCharThreeJNeZeroNF_of_char_three : W.c₆ = -W.a₂ ^ 3 := by
  rw [c₆_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 - 288 * W.a₆) * CharP.cast_eq_zero R 3

theorem Δ_of_isCharThreeJNeZeroNF_of_char_three : W.Δ = -W.a₂ ^ 3 * W.a₆ := by
  rw [Δ_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 * W.a₆ - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharThreeJNeZeroNF] [CharP F 3]

@[simp]
theorem j_of_isCharThreeJNeZeroNF_of_char_three : W.j = -W.a₂ ^ 3 / W.a₆ := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharThreeJNeZeroNF_of_char_three, Δ_of_isCharThreeJNeZeroNF_of_char_three,
    div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

theorem j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three : W.j ≠ 0 := by
  rw [j_of_isCharThreeJNeZeroNF_of_char_three, div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rwa [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff] at h

end Quantity

/-! ## Normal forms of characteristic = 3 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3, if it is
`Y² = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharThreeJNeZeroNF`) or
`Y² = X³ + a₄X + a₆` (`WeierstrassCurve.IsShortNF`). -/
class inductive IsCharThreeNF : Prop
| of_j_ne_zero [W.IsCharThreeJNeZeroNF] : IsCharThreeNF
| of_j_eq_zero [W.IsShortNF] : IsCharThreeNF

instance isCharThreeNF_of_isCharThreeJNeZeroNF [W.IsCharThreeJNeZeroNF] : W.IsCharThreeNF :=
  IsCharThreeNF.of_j_ne_zero

instance isCharThreeNF_of_isShortNF [W.IsShortNF] : W.IsCharThreeNF :=
  IsCharThreeNF.of_j_eq_zero

instance isCharNeTwoNF_of_isCharThreeNF [W.IsCharThreeNF] : W.IsCharNeTwoNF := by
  cases ‹W.IsCharThreeNF› <;> infer_instance

section VariableChange

variable [CharP R 3] [CharP F 3]

/-- For a `WeierstrassCurve` defined over a ring of characteristic = 3,
there is an explicit change of variables of it to `Y² = X³ + a₄X + a₆`
(`WeierstrassCurve.IsShortNF`) if its j = 0.
This is in fact given by `WeierstrassCurve.toCharNeTwoNF`. -/
def toShortNFOfCharThree : VariableChange R :=
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  W.toCharNeTwoNF

lemma toShortNFOfCharThree_a₂ : (W.toShortNFOfCharThree • W).a₂ = W.b₂ := by
  simp_rw [toShortNFOfCharThree, toCharNeTwoNF, variableChange_a₂, inv_one, Units.val_one, b₂]
  linear_combination (-W.a₂ - W.a₁ ^ 2) * CharP.cast_eq_zero R 3

theorem toShortNFOfCharThree_spec (hb₂ : W.b₂ = 0) : (W.toShortNFOfCharThree • W).IsShortNF := by
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  have H := W.toCharNeTwoNF_spec
  exact ⟨H.a₁, hb₂ ▸ W.toShortNFOfCharThree_a₂, H.a₃⟩

variable (W : WeierstrassCurve F)

/-- For a `WeierstrassCurve` defined over a field of characteristic = 3,
there is an explicit change of variables of it to `WeierstrassCurve.IsCharThreeNF`, that is,
`Y² = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharThreeJNeZeroNF`) or
`Y² = X³ + a₄X + a₆` (`WeierstrassCurve.IsShortNF`).
It is the composition of an explicit change of variables with
`WeierstrassCurve.toShortNFOfCharThree`. -/
def toCharThreeNF : VariableChange F :=
  ⟨1, (W.toShortNFOfCharThree • W).a₄ /
    (W.toShortNFOfCharThree • W).a₂, 0, 0⟩ * W.toShortNFOfCharThree

theorem toCharThreeNF_spec_of_b₂_ne_zero (hb₂ : W.b₂ ≠ 0) :
    (W.toCharThreeNF • W).IsCharThreeJNeZeroNF := by
  have h : (2 : F) * 2 = 1 := by linear_combination CharP.cast_eq_zero F 3
  letI : Invertible (2 : F) := ⟨2, h, h⟩
  rw [toCharThreeNF, mul_smul]
  set W' := W.toShortNFOfCharThree • W
  haveI : W'.IsCharNeTwoNF := W.toCharNeTwoNF_spec
  constructor
  · simp [variableChange_a₁]
  · simp [variableChange_a₃]
  · have ha₂ : W'.a₂ ≠ 0 := W.toShortNFOfCharThree_a₂ ▸ hb₂
    simp [field, variableChange_a₄, -mul_eq_zero]
    linear_combination (W'.a₄ * W'.a₂ ^ 2 + W'.a₄ ^ 2) * CharP.cast_eq_zero F 3

theorem toCharThreeNF_spec_of_b₂_eq_zero (hb₂ : W.b₂ = 0) : (W.toCharThreeNF • W).IsShortNF := by
  rw [toCharThreeNF, toShortNFOfCharThree_a₂, hb₂, div_zero, ← VariableChange.one_def, one_mul]
  exact W.toShortNFOfCharThree_spec hb₂

instance toCharThreeNF_spec : (W.toCharThreeNF • W).IsCharThreeNF := by
  by_cases hb₂ : W.b₂ = 0
  · haveI := W.toCharThreeNF_spec_of_b₂_eq_zero hb₂
    infer_instance
  · haveI := W.toCharThreeNF_spec_of_b₂_ne_zero hb₂
    infer_instance

theorem exists_variableChange_isCharThreeNF : ∃ C : VariableChange F, (C • W).IsCharThreeNF :=
  ⟨_, W.toCharThreeNF_spec⟩

end VariableChange

/-! ## Normal forms of characteristic = 2 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j ≠ 0, if its `a₁ = 1` and
`a₃, a₄ = 0`. In other words it is `Y² + XY = X³ + a₂X² + a₆`. -/
@[mk_iff]
class IsCharTwoJNeZeroNF : Prop where
  a₁ : W.a₁ = 1
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

section Quantity

variable [W.IsCharTwoJNeZeroNF]

@[simp]
theorem a₁_of_isCharTwoJNeZeroNF : W.a₁ = 1 := IsCharTwoJNeZeroNF.a₁

@[simp]
theorem a₃_of_isCharTwoJNeZeroNF : W.a₃ = 0 := IsCharTwoJNeZeroNF.a₃

@[simp]
theorem a₄_of_isCharTwoJNeZeroNF : W.a₄ = 0 := IsCharTwoJNeZeroNF.a₄

@[simp]
theorem b₂_of_isCharTwoJNeZeroNF : W.b₂ = 1 + 4 * W.a₂ := by
  rw [b₂, a₁_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
theorem b₄_of_isCharTwoJNeZeroNF : W.b₄ = 0 := by
  rw [b₄, a₃_of_isCharTwoJNeZeroNF, a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
theorem b₆_of_isCharTwoJNeZeroNF : W.b₆ = 4 * W.a₆ := by
  rw [b₆, a₃_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
theorem b₈_of_isCharTwoJNeZeroNF : W.b₈ = W.a₆ + 4 * W.a₂ * W.a₆ := by
  rw [b₈, a₁_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF, a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
theorem c₄_of_isCharTwoJNeZeroNF : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄, b₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
theorem c₆_of_isCharTwoJNeZeroNF : W.c₆ = -W.b₂ ^ 3 - 864 * W.a₆ := by
  rw [c₆, b₄_of_isCharTwoJNeZeroNF, b₆_of_isCharTwoJNeZeroNF]
  ring1

variable [CharP R 2]

theorem b₂_of_isCharTwoJNeZeroNF_of_char_two : W.b₂ = 1 := by
  rw [b₂_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

theorem b₆_of_isCharTwoJNeZeroNF_of_char_two : W.b₆ = 0 := by
  rw [b₆_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

theorem b₈_of_isCharTwoJNeZeroNF_of_char_two : W.b₈ = W.a₆ := by
  rw [b₈_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * W.a₆ * CharP.cast_eq_zero R 2

theorem c₄_of_isCharTwoJNeZeroNF_of_char_two : W.c₄ = 1 := by
  rw [c₄_of_isCharTwoJNeZeroNF, b₂_of_isCharTwoJNeZeroNF_of_char_two]
  ring1

theorem c₆_of_isCharTwoJNeZeroNF_of_char_two : W.c₆ = 1 := by
  rw [c₆_of_isCharTwoJNeZeroNF, b₂_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination (-1 - 432 * W.a₆) * CharP.cast_eq_zero R 2

@[simp]
theorem Δ_of_isCharTwoJNeZeroNF_of_char_two : W.Δ = W.a₆ := by
  rw [Δ, b₂_of_isCharTwoJNeZeroNF_of_char_two, b₄_of_isCharTwoJNeZeroNF,
    b₆_of_isCharTwoJNeZeroNF_of_char_two, b₈_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination -W.a₆ * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] [CharP F 2]

@[simp]
theorem j_of_isCharTwoJNeZeroNF_of_char_two : W.j = 1 / W.a₆ := by
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharTwoJNeZeroNF_of_char_two, Δ_of_isCharTwoJNeZeroNF_of_char_two, one_pow]

theorem j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two : W.j ≠ 0 := by
  rw [j_of_isCharTwoJNeZeroNF_of_char_two, div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  exact ⟨one_ne_zero, h⟩

end Quantity

/-! ## Normal forms of characteristic = 2 and j = 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j = 0, if its `a₁, a₂ = 0`.
In other words it is `Y² + a₃Y = X³ + a₄X + a₆`. -/
@[mk_iff]
class IsCharTwoJEqZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0

section Quantity

variable [W.IsCharTwoJEqZeroNF]

@[simp]
theorem a₁_of_isCharTwoJEqZeroNF : W.a₁ = 0 := IsCharTwoJEqZeroNF.a₁

@[simp]
theorem a₂_of_isCharTwoJEqZeroNF : W.a₂ = 0 := IsCharTwoJEqZeroNF.a₂

@[simp]
theorem b₂_of_isCharTwoJEqZeroNF : W.b₂ = 0 := by
  rw [b₂, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
theorem b₄_of_isCharTwoJEqZeroNF : W.b₄ = 2 * W.a₄ := by
  rw [b₄, a₁_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
theorem b₈_of_isCharTwoJEqZeroNF : W.b₈ = -W.a₄ ^ 2 := by
  rw [b₈, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
theorem c₄_of_isCharTwoJEqZeroNF : W.c₄ = -48 * W.a₄ := by
  rw [c₄, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
theorem c₆_of_isCharTwoJEqZeroNF : W.c₆ = -216 * W.b₆ := by
  rw [c₆, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
theorem Δ_of_isCharTwoJEqZeroNF : W.Δ = -(64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2) := by
  rw [Δ, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

variable [CharP R 2]

theorem b₄_of_isCharTwoJEqZeroNF_of_char_two : W.b₄ = 0 := by
  rw [b₄_of_isCharTwoJEqZeroNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

theorem b₈_of_isCharTwoJEqZeroNF_of_char_two : W.b₈ = W.a₄ ^ 2 := by
  rw [b₈_of_isCharTwoJEqZeroNF]
  linear_combination -W.a₄ ^ 2 * CharP.cast_eq_zero R 2

theorem c₄_of_isCharTwoJEqZeroNF_of_char_two : W.c₄ = 0 := by
  rw [c₄_of_isCharTwoJEqZeroNF]
  linear_combination -24 * W.a₄ * CharP.cast_eq_zero R 2

theorem c₆_of_isCharTwoJEqZeroNF_of_char_two : W.c₆ = 0 := by
  rw [c₆_of_isCharTwoJEqZeroNF]
  linear_combination -108 * W.b₆ * CharP.cast_eq_zero R 2

theorem Δ_of_isCharTwoJEqZeroNF_of_char_two : W.Δ = W.a₃ ^ 4 := by
  rw [Δ_of_isCharTwoJEqZeroNF, b₆_of_char_two]
  linear_combination (-32 * W.a₄ ^ 3 - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]

theorem j_of_isCharTwoJEqZeroNF : W.j = 110592 * W.a₄ ^ 3 / (64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2) := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharTwoJEqZeroNF] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharTwoJEqZeroNF, Δ_of_isCharTwoJEqZeroNF, div_eq_div_iff h (neg_ne_zero.1 h)]
  ring1

@[simp]
theorem j_of_isCharTwoJEqZeroNF_of_char_two [CharP F 2] : W.j = 0 := by
  rw [j, c₄_of_isCharTwoJEqZeroNF_of_char_two]; simp

end Quantity

/-! ## Normal forms of characteristic = 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2, if it is
`Y² + XY = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharTwoJNeZeroNF`) or
`Y² + a₃Y = X³ + a₄X + a₆` (`WeierstrassCurve.IsCharTwoJEqZeroNF`). -/
class inductive IsCharTwoNF : Prop
| of_j_ne_zero [W.IsCharTwoJNeZeroNF] : IsCharTwoNF
| of_j_eq_zero [W.IsCharTwoJEqZeroNF] : IsCharTwoNF

instance isCharTwoNF_of_isCharTwoJNeZeroNF [W.IsCharTwoJNeZeroNF] : W.IsCharTwoNF :=
  IsCharTwoNF.of_j_ne_zero

instance isCharTwoNF_of_isCharTwoJEqZeroNF [W.IsCharTwoJEqZeroNF] : W.IsCharTwoNF :=
  IsCharTwoNF.of_j_eq_zero

section VariableChange

variable [CharP R 2] [CharP F 2]

/-- For a `WeierstrassCurve` defined over a ring of characteristic = 2,
there is an explicit change of variables of it to `Y² + a₃Y = X³ + a₄X + a₆`
(`WeierstrassCurve.IsCharTwoJEqZeroNF`) if its j = 0. -/
def toCharTwoJEqZeroNF : VariableChange R := ⟨1, W.a₂, 0, 0⟩

theorem toCharTwoJEqZeroNF_spec (ha₁ : W.a₁ = 0) :
    (W.toCharTwoJEqZeroNF • W).IsCharTwoJEqZeroNF := by
  constructor
  · simp [toCharTwoJEqZeroNF, ha₁, variableChange_a₁]
  · simp_rw [toCharTwoJEqZeroNF, variableChange_a₂, inv_one, Units.val_one]
    linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F)

/-- For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `Y² + XY = X³ + a₂X² + a₆`
(`WeierstrassCurve.IsCharTwoJNeZeroNF`) if its j ≠ 0. -/
def toCharTwoJNeZeroNF (W : WeierstrassCurve F) (ha₁ : W.a₁ ≠ 0) : VariableChange F :=
  ⟨Units.mk0 _ ha₁, W.a₃ / W.a₁, 0, (W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) / W.a₁ ^ 3⟩

theorem toCharTwoJNeZeroNF_spec (ha₁ : W.a₁ ≠ 0) :
    (W.toCharTwoJNeZeroNF ha₁ • W).IsCharTwoJNeZeroNF := by
  constructor
  · simp [toCharTwoJNeZeroNF, ha₁, variableChange_a₁]
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₃, -mul_eq_zero]
    linear_combination (W.a₃ * W.a₁ ^ 3 + W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) * CharP.cast_eq_zero F 2
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₄, -mul_eq_zero]
    linear_combination (W.a₃ ^ 2 + W.a₁ * W.a₃ * W.a₂) * CharP.cast_eq_zero F 2

/-- For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `WeierstrassCurve.IsCharTwoNF`, that is,
`Y² + XY = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharTwoJNeZeroNF`) or
`Y² + a₃Y = X³ + a₄X + a₆` (`WeierstrassCurve.IsCharTwoJEqZeroNF`). -/
def toCharTwoNF [DecidableEq F] : VariableChange F :=
  if ha₁ : W.a₁ = 0 then W.toCharTwoJEqZeroNF else W.toCharTwoJNeZeroNF ha₁

instance toCharTwoNF_spec [DecidableEq F] : (W.toCharTwoNF • W).IsCharTwoNF := by
  by_cases ha₁ : W.a₁ = 0
  · rw [toCharTwoNF, dif_pos ha₁]
    haveI := W.toCharTwoJEqZeroNF_spec ha₁
    infer_instance
  · rw [toCharTwoNF, dif_neg ha₁]
    haveI := W.toCharTwoJNeZeroNF_spec ha₁
    infer_instance

theorem exists_variableChange_isCharTwoNF : ∃ C : VariableChange F, (C • W).IsCharTwoNF := by
  classical
  exact ⟨_, W.toCharTwoNF_spec⟩

end VariableChange

end WeierstrassCurve
