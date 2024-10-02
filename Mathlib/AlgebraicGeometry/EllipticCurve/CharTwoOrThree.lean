/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.CharP.Defs

/-!

# Basic properties of elliptic curves over characteristic 2 or 3 rings

This file states some basic properties of elliptic curves over characteristic 2 or 3 rings.

-/

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (E : EllipticCurve R)

section CharTwo

variable [CharP R 2]

namespace WeierstrassCurve

lemma b₂_of_char_two : W.b₂ = W.a₁ ^ 2 := by
  rw [b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

lemma b₄_of_char_two : W.b₄ = W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

lemma b₆_of_char_two : W.b₆ = W.a₃ ^ 2 := by
  rw [b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

lemma b₈_of_char_two :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 + W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination (2 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ - W.a₄ ^ 2) * CharP.cast_eq_zero R 2

lemma c₄_of_char_two : W.c₄ = W.a₁ ^ 4 := by
  rw [c₄, b₂_of_char_two]
  linear_combination -12 * W.b₄ * CharP.cast_eq_zero R 2

lemma c₆_of_char_two : W.c₆ = W.a₁ ^ 6 := by
  rw [c₆, b₂_of_char_two]
  linear_combination (18 * W.a₁ ^ 2 * W.b₄ - 108 * W.b₆ - W.a₁ ^ 6) * CharP.cast_eq_zero R 2

lemma Δ_of_char_two :
    W.Δ = W.a₁ ^ 4 * W.b₈ + W.a₃ ^ 4 + W.a₁ ^ 3 * W.a₃ ^ 3 := by
  rw [Δ, b₂_of_char_two, b₄_of_char_two, b₆_of_char_two]
  linear_combination (-W.a₁ ^ 4 * W.b₈ - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

lemma b_relation_of_char_two : W.b₂ * W.b₆ = W.b₄ ^ 2 := by
  linear_combination -W.b_relation + 2 * W.b₈ * CharP.cast_eq_zero R 2

lemma c_relation_of_char_two : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 864 * W.Δ * CharP.cast_eq_zero R 2

lemma twoTorsionPolynomial_of_char_two : W.twoTorsionPolynomial = ⟨0, W.b₂, 0, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination 2 * CharP.cast_eq_zero R 2
  · linear_combination W.b₄ * CharP.cast_eq_zero R 2

lemma twoTorsionPolynomial_disc_of_char_two : W.twoTorsionPolynomial.disc = 0 := by
  linear_combination W.twoTorsionPolynomial_disc + 8 * W.Δ * CharP.cast_eq_zero R 2

end WeierstrassCurve

namespace EllipticCurve

lemma j_of_char_two : E.j = E.Δ'⁻¹ * E.a₁ ^ 12 := by
  rw [j, E.c₄_of_char_two, ← pow_mul]

/-- A variant of `EllipticCurve.j_eq_zero_iff_of_char_two` without assuming the ring
being reduced. -/
lemma j_eq_zero_iff_of_char_two' : E.j = 0 ↔ E.a₁ ^ 12 = 0 := by
  rw [j_of_char_two, Units.mul_right_eq_zero]

lemma j_eq_zero_of_char_two (h : E.a₁ = 0) : E.j = 0 := by
  rw [j_eq_zero_iff_of_char_two', h, zero_pow (Nat.succ_ne_zero _)]

lemma j_eq_zero_iff_of_char_two [IsReduced R] : E.j = 0 ↔ E.a₁ = 0 := by
  rw [j_eq_zero_iff_of_char_two', IsReduced.pow_eq_zero_iff (Nat.succ_ne_zero _)]

end EllipticCurve

end CharTwo

section CharThree

variable [CharP R 3]

namespace WeierstrassCurve

lemma b₂_of_char_three : W.b₂ = W.a₁ ^ 2 + W.a₂ := by
  rw [b₂]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

lemma b₄_of_char_three : W.b₄ = -W.a₄ + W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

lemma b₆_of_char_three : W.b₆ = W.a₃ ^ 2 + W.a₆ := by
  rw [b₆]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

lemma b₈_of_char_three :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

lemma c₄_of_char_three : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄]
  linear_combination -8 * W.b₄ * CharP.cast_eq_zero R 3

lemma c₆_of_char_three : W.c₆ = -W.b₂ ^ 3 := by
  rw [c₆]
  linear_combination (12 * W.b₂ * W.b₄ - 72 * W.b₆) * CharP.cast_eq_zero R 3

lemma Δ_of_char_three : W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 := by
  rw [Δ]
  linear_combination (-9 * W.b₆ ^ 2 + 3 * W.b₂ * W.b₄ * W.b₆) * CharP.cast_eq_zero R 3

lemma b_relation_of_char_three : W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  linear_combination W.b_relation - W.b₈ * CharP.cast_eq_zero R 3

lemma c_relation_of_char_three : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 576 * W.Δ * CharP.cast_eq_zero R 3

lemma twoTorsionPolynomial_of_char_three : W.twoTorsionPolynomial = ⟨1, W.b₂, -W.b₄, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination CharP.cast_eq_zero R 3
  · linear_combination W.b₄ * CharP.cast_eq_zero R 3

lemma twoTorsionPolynomial_disc_of_char_three : W.twoTorsionPolynomial.disc = W.Δ := by
  linear_combination W.twoTorsionPolynomial_disc + 5 * W.Δ * CharP.cast_eq_zero R 3

end WeierstrassCurve

namespace EllipticCurve

lemma j_of_char_three : E.j = E.Δ'⁻¹ * E.b₂ ^ 6 := by
  rw [j, E.c₄_of_char_three, ← pow_mul]

/-- A variant of `EllipticCurve.j_eq_zero_iff_of_char_three` without assuming the ring
being reduced. -/
lemma j_eq_zero_iff_of_char_three' : E.j = 0 ↔ E.b₂ ^ 6 = 0 := by
  rw [j_of_char_three, Units.mul_right_eq_zero]

lemma j_eq_zero_of_char_three (h : E.b₂ = 0) : E.j = 0 := by
  rw [j_eq_zero_iff_of_char_three', h, zero_pow (Nat.succ_ne_zero _)]

lemma j_eq_zero_iff_of_char_three [IsReduced R] : E.j = 0 ↔ E.b₂ = 0 := by
  rw [j_eq_zero_iff_of_char_three', IsReduced.pow_eq_zero_iff (Nat.succ_ne_zero _)]

end EllipticCurve

end CharThree
