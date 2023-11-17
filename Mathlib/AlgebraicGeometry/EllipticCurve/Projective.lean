/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Point

/-!
# Projective coordinates of Weierstrass curves
-/

abbrev WeierstrassCurve.Projective :=
  WeierstrassCurve

universe u

namespace WeierstrassCurve.Projective

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

structure PointRep (R : Type u) where
  (x y z : R)

variable (R : Type u) [CommRing R]

def PointRel (P Q : PointRep R) : Prop :=
  ∃ u : Rˣ, P.x = (u : R) * Q.x ∧ P.y = (u : R) * Q.y ∧ P.z = (u : R) * Q.z

def PointEquiv : Equivalence <| PointRel R :=
  ⟨fun _ => ⟨1, by simp only [Units.val_one, one_pow, one_mul]⟩,
    fun ⟨u, hu⟩ => ⟨u⁻¹, by simp only [hu, ← u.val_pow_eq_pow_val, inv_pow, u.inv_mul_cancel_left]⟩,
    fun ⟨u, hu⟩ ⟨u', hu'⟩ => ⟨u * u', by simp only [hu, hu', u.val_mul, mul_pow, mul_assoc]⟩⟩

instance PointSetoid : Setoid <| PointRep R :=
  ⟨PointRel R, PointEquiv R⟩

abbrev PointClass : Type u :=
  Quotient <| PointSetoid R

variable {R} (W : Projective R)

@[pp_dot]
abbrev toAffine : WeierstrassCurve R :=
  W

section Polynomial

@[pp_dot]
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 * X 2 + C W.a₁ * X 0 * X 1 * X 2 + C W.a₃ * X 1 * X 2 ^ 2
    - (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 * X 2 + C W.a₄ * X 0 * X 2 ^ 2 + C W.a₆ * X 2 ^ 3)

lemma eval_polynomial (P : PointRep R) :
    eval ![P.x, P.y, P.z] W.polynomial =
      P.y ^ 2 * P.z + W.a₁ * P.x * P.y * P.z + W.a₃ * P.y * P.z ^ 2
        - (P.x ^ 3 + W.a₂ * P.x ^ 2 * P.z + W.a₄ * P.x * P.z ^ 2 + W.a₆ * P.z ^ 3) := by
  rw [polynomial]
  eval_simp
  rfl

@[pp_dot]
def equation (P : PointRep R) : Prop :=
  eval ![P.x, P.y, P.z] W.polynomial = 0

lemma equation_iff (P : PointRep R) :
    W.equation P ↔
      P.y ^ 2 * P.z + W.a₁ * P.x * P.y * P.z + W.a₃ * P.y * P.z ^ 2
        = P.x ^ 3 + W.a₂ * P.x ^ 2 * P.z + W.a₄ * P.x * P.z ^ 2 + W.a₆ * P.z ^ 3 := by
  rw [equation, eval_polynomial, sub_eq_zero]

lemma equation_zero (y : R) : W.equation ⟨0, y, 0⟩ :=
  (W.equation_iff ⟨0, y, 0⟩).mpr <| by ring1

lemma equation_some (x y : R) : W.equation ⟨x, y, 1⟩ ↔ W.toAffine.equation x y := by
  rw [equation_iff, W.toAffine.equation_iff]
  congr! 1 <;> ring1

@[simp]
lemma equation_mul_iff (P : PointRep R) (u : Rˣ) :
    W.equation ⟨u * P.x, u * P.y, u * P.z⟩ ↔ W.equation P :=
  have (u : Rˣ) {P : PointRep R} (h : W.equation P) : W.equation ⟨u * P.x, u * P.y, u * P.z⟩ := by
    rw [equation_iff] at h ⊢
    linear_combination (norm := ring1) (u : R) ^ 3 * h
  ⟨fun h => by convert this u⁻¹ h <;> exact (u.inv_mul_cancel_left _).symm, this u⟩


@[pp_dot]
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  C W.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W.a₂) * X 0 * X 2 + C W.a₄ * X 2 ^ 2)

lemma eval_polynomialX (P : PointRep R) :
    eval ![P.x, P.y, P.z] W.polynomialX =
      W.a₁ * P.y * P.z - (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2) := by
  rw [polynomialX]
  eval_simp
  rfl

@[pp_dot]
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  C 2 * X 1 * X 2 + C W.a₁ * X 0 * X 2 + C W.a₃ * X 2 ^ 2

lemma eval_polynomialY (P : PointRep R) :
    eval ![P.x, P.y, P.z] W.polynomialY = 2 * P.y * P.z + W.a₁ * P.x * P.z + W.a₃ * P.z ^ 2 := by
  rw [polynomialY]
  eval_simp
  rfl

@[pp_dot]
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C (2 * W.a₃) * X 1 * X 2
    - (C W.a₂ * X 0 ^ 2 + C (2 * W.a₄) * X 0 * X 2 + C (3 * W.a₆) * X 2 ^ 2)

lemma eval_polynomialZ (P : PointRep R) :
    eval ![P.x, P.y, P.z] W.polynomialZ =
      P.y ^ 2 + W.a₁ * P.x * P.y + 2 * W.a₃ * P.y * P.z
        - (W.a₂ * P.x ^ 2 + 2 * W.a₄ * P.x * P.z + 3 * W.a₆ * P.z ^ 2) := by
  rw [polynomialZ]
  eval_simp
  rfl

/-- Euler's homogeneous function theorem. -/
theorem polynomial_relation (P : PointRep R) :
    3 * eval ![P.x, P.y, P.z] W.polynomial =
      P.x * eval ![P.x, P.y, P.z] W.polynomialX + P.y * eval ![P.x, P.y, P.z] W.polynomialY
        + P.z * eval ![P.x, P.y, P.z] W.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

@[pp_dot]
def nonsingular (P : PointRep R) : Prop :=
  W.equation P ∧ (eval ![P.x, P.y, P.z] W.polynomialX ≠ 0 ∨ eval ![P.x, P.y, P.z] W.polynomialY ≠ 0
    ∨ eval ![P.x, P.y, P.z] W.polynomialZ ≠ 0)

lemma nonsingular_iff (P : PointRep R) :
    W.nonsingular P ↔ W.equation P ∧
      (W.a₁ * P.y * P.z ≠ 3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 ∨
        P.y * P.z ≠ -P.y * P.z - W.a₁ * P.x * P.z - W.a₃ * P.z ^ 2 ∨
        P.y ^ 2 + W.a₁ * P.x * P.y + 2 * W.a₃ * P.y * P.z
          ≠ W.a₂ * P.x ^ 2 + 2 * W.a₄ * P.x * P.z + 3 * W.a₆ * P.z ^ 2) := by
  rw [nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ, sub_ne_zero, sub_ne_zero,
    ← sub_ne_zero (a := P.y * P.z)]
  congr! 4
  ring1

lemma nonsingular_zero [Nontrivial R] : W.nonsingular ⟨0, 1, 0⟩ :=
  (W.nonsingular_iff ⟨0, 1, 0⟩).mpr ⟨W.equation_zero 1, by simp⟩

lemma nonsingular_zero' [NoZeroDivisors R] {y : R} (hy : y ≠ 0) : W.nonsingular ⟨0, y, 0⟩ :=
  (W.nonsingular_iff ⟨0, y, 0⟩).mpr ⟨W.equation_zero y, by simpa⟩

lemma nonsingular_some (x y : R) : W.nonsingular ⟨x, y, 1⟩ ↔ W.toAffine.nonsingular x y := by
  simp only [nonsingular_iff, W.toAffine.nonsingular_iff, equation_some, and_congr_right_iff,
    W.toAffine.equation_iff, ← not_and_or, not_iff_not, one_pow, mul_one, Iff.comm, iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 3 * h - x * hX - y * hY

@[simp]
lemma nonsingular_mul_iff (P : PointRep R) (u : Rˣ) :
    W.nonsingular ⟨u * P.x, u * P.y, u * P.z⟩ ↔ W.nonsingular P :=
  have (u : Rˣ) {P : PointRep R} (h : W.nonsingular ⟨u * P.x, u * P.y, u * P.z⟩) :
      W.nonsingular P := by
    rcases (W.nonsingular_iff _).mp h with ⟨h, h'⟩
    refine (W.nonsingular_iff P).mpr ⟨(W.equation_mul_iff P u).mp h, ?_⟩
    contrapose! h'
    exact ⟨by linear_combination (norm := ring1) (u : R) ^ 2 * h'.left,
      by linear_combination (norm := ring1) (u : R) ^ 2 * h'.right.left,
      by linear_combination (norm := ring1) (u : R) ^ 2 * h'.right.right⟩
  ⟨this u, fun h => this u⁻¹ <| by simpa only [u.inv_mul_cancel_left] using h⟩

lemma nonsingular_of_equiv {P Q : PointRep R} (h : P ≈ Q) : W.nonsingular P ↔ W.nonsingular Q := by
  rcases P, h with ⟨⟨_, _, _⟩, ⟨u, ⟨rfl, rfl, rfl⟩⟩⟩
  exact W.nonsingular_mul_iff Q u

@[pp_dot]
def nonsingular_lift (P : PointClass R) : Prop :=
  P.lift W.nonsingular fun _ _ => propext ∘ W.nonsingular_of_equiv

@[simp]
def nonsingular_lift_eq (P : PointRep R) : W.nonsingular_lift ⟦P⟧ = W.nonsingular P :=
  rfl

lemma nonsingular_lift_zero [Nontrivial R] : W.nonsingular_lift ⟦⟨0, 1, 0⟩⟧ :=
  W.nonsingular_zero

lemma nonsingular_lift_zero' [NoZeroDivisors R] {y : R} (hy : y ≠ 0) :
    W.nonsingular_lift ⟦⟨0, y, 0⟩⟧ :=
  W.nonsingular_zero' hy

lemma nonsingular_lift_some (x y : R) :
    W.nonsingular_lift ⟦⟨x, y, 1⟩⟧ ↔ W.toAffine.nonsingular x y :=
  W.nonsingular_some x y

variable {F : Type u} [Field F] {W : Projective F}

lemma equiv_of_Zeq0 {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) (hPz : P.z = 0)
    (hQz : Q.z = 0) : P ≈ Q := by
  rcases P, Q with ⟨⟨_, y, _⟩, ⟨_, y', _⟩⟩
  subst hPz hQz
  simp [nonsingular_iff, equation_iff] at hP hQ
  rcases pow_eq_zero hP.left.symm, pow_eq_zero hQ.left.symm with ⟨⟨_⟩, ⟨_⟩⟩
  simp at hP hQ
  exact ⟨Units.mk0 (y / y') <| div_ne_zero hP hQ, by simpa using (div_mul_cancel y hQ).symm⟩

lemma equiv_zero_of_Zeq0 {P : PointRep F} (h : W.nonsingular P) (hPz : P.z = 0) : P ≈ ⟨0, 1, 0⟩ :=
  equiv_of_Zeq0 h W.nonsingular_zero hPz rfl

lemma equiv_some_of_Zne0 {P : PointRep F} (hPz : P.z ≠ 0) : P ≈ ⟨P.x / P.z, P.y / P.z, 1⟩ :=
  ⟨Units.mk0 P.z hPz, ⟨(mul_div_cancel' _ hPz).symm, (mul_div_cancel' _ hPz).symm, (mul_one P.z).symm⟩⟩

@[simp]
lemma nonsingular_some_of_Zne0 {P : PointRep F} (hPz : P.z ≠ 0) :
    W.nonsingular P ↔ W.toAffine.nonsingular (P.x / P.z) (P.y / P.z) :=
  (W.nonsingular_of_equiv <| equiv_some_of_Zne0 hPz).trans <| W.nonsingular_some ..

end Polynomial

section Addition

@[pp_dot]
def negY (P : PointRep R) : R :=
  -P.y - W.a₁ * P.x - W.a₃ * P.z

@[simp]
lemma negY_mul (P : PointRep R) (u : Rˣ) : W.negY ⟨u * P.x, u * P.y, u * P.z⟩ = u * W.negY P := by
  simp only [negY]
  ring1

@[pp_dot]
def neg (P : PointRep R) : PointRep R :=
  ⟨P.x, W.negY P, P.z⟩

@[simp]
lemma neg_zero : W.neg ⟨0, 1, 0⟩ = ⟨0, -1, 0⟩ := by
  simp only [neg, negY, sub_zero, mul_zero]

@[simp]
lemma neg_some (x y : R) : W.neg ⟨x, y, 1⟩ = ⟨x, -y - W.a₁ * x - W.a₃, 1⟩ := by
  simp only [neg, negY, mul_one]

lemma neg_equiv {P Q : PointRep R} (h : P ≈ Q) : W.neg P ≈ W.neg Q := by
  rcases P, h with ⟨⟨_, _, _⟩, ⟨u, ⟨rfl, rfl, rfl⟩⟩⟩
  exact ⟨u, ⟨rfl, W.negY_mul Q u, rfl⟩⟩

@[pp_dot]
def neg_map (P : PointClass R) : PointClass R :=
  P.map W.neg fun _ _ => W.neg_equiv

@[simp]
lemma neg_map_eq {P : PointRep R} : W.neg_map ⟦P⟧ = ⟦W.neg P⟧ :=
  rfl

@[simp]
lemma neg_map_zero : W.neg_map ⟦⟨0, 1, 0⟩⟧ = ⟦⟨0, 1, 0⟩⟧ := by
  simpa only [neg_map_eq, neg_zero, Quotient.eq] using ⟨-1, by simp⟩

@[simp]
lemma neg_map_some (x y : R) : W.neg_map ⟦⟨x, y, 1⟩⟧ = ⟦⟨x, -y - W.a₁ * x - W.a₃, 1⟩⟧ := by
  rw [neg_map_eq, neg_some]

@[pp_dot]
def sec_addX' (P Q : PointRep R) : R :=
  (P.y * Q.z - P.z * Q.y) ^ 2 * (P.z * Q.z)
    + W.a₁ * (P.y * Q.z - P.z * Q.y) * (P.z * Q.z * (P.x * Q.z - P.z * Q.x))
    - W.a₂ * (P.z * Q.z * (P.x * Q.z - P.z * Q.x) ^ 2) - P.x * Q.z * (P.x * Q.z - P.z * Q.x) ^ 2
    - P.z * Q.x * (P.x * Q.z - P.z * Q.x) ^ 2

@[simp]
lemma sec_addX'_mul (P Q : PointRep R) (u v : Rˣ) :
    W.sec_addX' ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 3 * (v : R) ^ 3 * W.sec_addX' P Q := by
  simp only [sec_addX']
  ring1

@[pp_dot]
def tan_addX' (P : PointRep R) : R :=
  (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 - W.a₁ * P.y * P.z) ^ 2
    + W.a₁ * (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 - W.a₁ * P.y * P.z) *
      (P.z * (P.y - W.negY P))
    - W.a₂ * (P.z ^ 2 * (P.y - W.negY P) ^ 2) - 2 * P.x * (P.z * (P.y - W.negY P) ^ 2)

@[simp]
lemma tan_addX'_mul (P : PointRep R) (u : Rˣ) :
    W.tan_addX' ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 4 * W.tan_addX' P := by
  simp only [tan_addX', negY_mul]
  ring1

@[pp_dot]
def sec_addY' (P Q : PointRep R) : R :=
  (P.y * Q.z - P.z * Q.y) * W.sec_addX' P Q
    - P.x * (P.y * Q.z - P.z * Q.y) * (Q.z * (P.x * Q.z - P.z * Q.x) ^ 2)
    + P.y * (Q.z * (P.x * Q.z - P.z * Q.x) ^ 3)

@[simp]
lemma sec_addY'_mul (P Q : PointRep R) (u v : Rˣ) :
    W.sec_addY' ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 4 * (v : R) ^ 4 * W.sec_addY' P Q := by
  simp only [sec_addY', sec_addX'_mul]
  ring1

@[pp_dot]
def tan_addY' (P : PointRep R) : R :=
  (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 - W.a₁ * P.y * P.z) * W.tan_addX' P
    - (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 - W.a₁ * P.y * P.z) * P.x
      * (P.z * (P.y - W.negY P) ^ 2)
    + P.y * (P.z ^ 2 * (P.y - W.negY P) ^ 3)

@[simp]
lemma tan_addY'_mul (P : PointRep R) (u : Rˣ) :
    W.tan_addY' ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 6 * W.tan_addY' P := by
  simp only [tan_addY', negY_mul, tan_addX'_mul]
  ring1

def sec_addZ (P Q : PointRep R) : R :=
  P.z * Q.z * (P.x * Q.z - P.z * Q.x) ^ 3

@[simp]
lemma sec_addZ_mul (P Q : PointRep R) (u v : Rˣ) :
    sec_addZ ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 4 * (v : R) ^ 4 * sec_addZ P Q := by
  simp only [sec_addZ]
  ring1

@[pp_dot]
def tan_addZ (P : PointRep R) : R :=
  P.z ^ 3 * (P.y - W.negY P) ^ 3

@[simp]
lemma tan_addZ_mul (P : PointRep R) (u : Rˣ) :
    W.tan_addZ ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 6 * W.tan_addZ P := by
  simp only [tan_addZ, negY_mul]
  ring1

@[pp_dot]
def sec_addX (P Q : PointRep R) : R :=
  W.sec_addX' P Q * (P.x * Q.z - P.z * Q.x)

@[simp]
lemma sec_addX_mul (P Q : PointRep R) (u v : Rˣ) :
    W.sec_addX ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 4 * (v : R) ^ 4 * W.sec_addX P Q := by
  simp only [sec_addX, sec_addX'_mul]
  ring1

@[pp_dot]
def tan_addX (P : PointRep R) : R :=
  W.tan_addX' P * P.z * (P.y - W.negY P)

@[simp]
lemma tan_addX_mul (P : PointRep R) (u : Rˣ) :
    W.tan_addX ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 6 * W.tan_addX P := by
  simp only [tan_addX, negY_mul, tan_addX'_mul]
  ring1

@[pp_dot]
def sec_addY (P Q : PointRep R) : R :=
  W.negY <| ⟨W.sec_addX P Q, W.sec_addY' P Q, sec_addZ P Q⟩

@[simp]
lemma sec_addY_mul (P Q : PointRep R) (u v : Rˣ) :
    W.sec_addY ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 4 * (v : R) ^ 4 * W.sec_addY P Q := by
  simp only [sec_addY, negY, sec_addX_mul, sec_addY'_mul, sec_addZ_mul]
  ring1

@[pp_dot]
def tan_addY (P : PointRep R) : R :=
  W.negY <| ⟨W.tan_addX P, W.tan_addY' P, W.tan_addZ P⟩

@[simp]
lemma tan_addY_mul (P : PointRep R) (u : Rˣ) :
    W.tan_addY ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 6 * W.tan_addY P := by
  simp only [tan_addY, negY, tan_addX_mul, tan_addY'_mul, tan_addZ_mul]
  ring1

open scoped Classical

@[pp_dot]
noncomputable def add (P Q : PointRep R) : PointRep R :=
  if P.z = 0 then Q else if Q.z = 0 then P else if P.x * Q.z = P.z * Q.x then
    if P.y * Q.z = P.z * W.negY Q then ⟨0, 1, 0⟩ else ⟨W.tan_addX P, W.tan_addY P, W.tan_addZ P⟩
  else ⟨W.sec_addX P Q, W.sec_addY P Q, sec_addZ P Q⟩

@[simp]
lemma add_of_Zeq0_left {P : PointRep R} (Q : PointRep R) (hPz : P.z = 0) : W.add P Q = Q :=
  if_pos hPz

@[simp]
lemma add_zero_left (P : PointRep R) : W.add ⟨0, 1, 0⟩ P = P :=
  W.add_of_Zeq0_left _ rfl

@[simp]
lemma add_of_Zeq0_right {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z = 0) : W.add P Q = P := by
  rw [add, if_neg hPz, if_pos hQz]

@[simp]
lemma add_zero_right {P : PointRep R} (hPz : P.z ≠ 0) : W.add P ⟨0, 1, 0⟩ = P :=
  W.add_of_Zeq0_right hPz rfl

@[simp]
lemma add_of_Yeq {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z = P.z * W.negY Q) : W.add P Q = ⟨0, 1, 0⟩ := by
  rw [add, if_neg hPz, if_neg hQz, if_pos hx, if_pos hy]

@[simp]
lemma add_of_Yne {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z ≠ P.z * W.negY Q) : W.add P Q = ⟨W.tan_addX P, W.tan_addY P, W.tan_addZ P⟩ := by
  rw [add, if_neg hPz, if_neg hQz, if_pos hx, if_neg hy]

@[simp]
lemma add_of_Xne {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z ≠ P.z * Q.x) :
    W.add P Q = ⟨W.sec_addX P Q, W.sec_addY P Q, sec_addZ P Q⟩ := by
  rw [add, if_neg hPz, if_neg hQz, if_neg hx]

variable [IsDomain R]

lemma add_mul_equiv (P Q : PointRep R) (u v : Rˣ) :
    W.add ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ ≈ W.add P Q := by
  have huv : (u * v : R) ≠ 0 := mul_ne_zero u.ne_zero v.ne_zero
  by_cases hPz : P.z = 0
  · rw [hPz, mul_zero, W.add_of_Zeq0_left _ <| by exact rfl, W.add_of_Zeq0_left Q hPz]
    exact ⟨v, ⟨rfl, rfl, rfl⟩⟩
  · have huz : (⟨u * P.x, u * P.y, u * P.z⟩ : PointRep R).z ≠ 0 := mul_ne_zero u.ne_zero hPz
    by_cases hQz : Q.z = 0
    · rw [hQz, mul_zero, W.add_of_Zeq0_right huz <| by exact rfl, W.add_of_Zeq0_right hPz hQz]
      exact ⟨u, ⟨rfl, rfl, rfl⟩⟩
    · have hvz : (⟨v * Q.x, v * Q.y, v * Q.z⟩ : PointRep R).z ≠ 0 := mul_ne_zero v.ne_zero hQz
      by_cases hx : P.x * Q.z = P.z * Q.x
      · by_cases hy : P.y * Q.z = P.z * W.negY Q
        · rw [W.add_of_Yeq huz hvz (by rw [mul_mul_mul_comm, hx, mul_mul_mul_comm]) <|
            by simp only [negY_mul, mul_mul_mul_comm, hy], W.add_of_Yeq hPz hQz hx hy]
        · simpa only [W.add_of_Yne huz hvz (by rw [mul_mul_mul_comm, hx, mul_mul_mul_comm]) <|
            by simpa only [negY_mul, mul_mul_mul_comm] using hy ∘ mul_left_cancel₀ huv,
            W.add_of_Yne hPz hQz hx hy] using ⟨u ^ 6, by simp⟩
      · simpa only [W.add_of_Xne huz hvz <|
          by simpa only [mul_mul_mul_comm] using hx ∘ mul_left_cancel₀ huv, W.add_of_Xne hPz hQz hx]
          using ⟨u ^ 4 * v ^ 4, by simp⟩

lemma add_equiv {P P' Q Q' : PointRep R} (hP : P ≈ P') (hQ : Q ≈ Q') : W.add P Q ≈ W.add P' Q' := by
  rcases P, Q with ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩
  rcases hP, hQ with ⟨⟨u, ⟨rfl, rfl, rfl⟩⟩, ⟨v, ⟨rfl, rfl, rfl⟩⟩⟩
  exact W.add_mul_equiv P' Q' u v

@[pp_dot]
noncomputable def add_map (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W.add (fun _ _ hP _ _ hQ => W.add_equiv hP hQ) P Q

@[simp]
lemma add_map_eq (P Q : PointRep R) : W.add_map ⟦P⟧ ⟦Q⟧ = ⟦W.add P Q⟧ :=
  rfl

@[simp]
lemma add_map_of_Zeq0_left {P : PointRep R} (Q : PointClass R) (hPz : P.z = 0) :
    W.add_map ⟦P⟧ Q = Q := by
  rcases Q with ⟨Q⟩
  erw [add_map_eq, W.add_of_Zeq0_left Q hPz]
  rfl

@[simp]
lemma add_map_zero_left (P : PointClass R) : W.add_map ⟦⟨0, 1, 0⟩⟧ P = P :=
  W.add_map_of_Zeq0_left P rfl

@[simp]
lemma add_map_of_Zeq0_right {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z = 0) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦P⟧ := by
  rw [add_map_eq, W.add_of_Zeq0_right hPz hQz]

@[simp]
lemma add_map_zero_right {P : PointRep R} (hPz : P.z ≠ 0) : W.add_map ⟦P⟧ ⟦⟨0, 1, 0⟩⟧ = ⟦P⟧ := by
  rw [add_map_eq, W.add_zero_right hPz]

@[simp]
lemma add_map_of_Yeq {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z = P.z * W.negY Q) : W.add_map ⟦P⟧ ⟦Q⟧ = ⟦⟨0, 1, 0⟩⟧ := by
  rw [add_map_eq, W.add_of_Yeq hPz hQz hx hy]

@[simp]
lemma add_map_of_Yne {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z ≠ P.z * W.negY Q) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦⟨W.tan_addX P, W.tan_addY P, W.tan_addZ P⟩⟧ := by
  rw [add_map_eq, W.add_of_Yne hPz hQz hx hy]

@[simp]
lemma add_map_of_Xne {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0)
    (hx : P.x * Q.z ≠ P.z * Q.x) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦⟨W.sec_addX P Q, W.sec_addY P Q, sec_addZ P Q⟩⟧ := by
  rw [add_map_eq, W.add_of_Xne hPz hQz hx]

variable {F : Type u} [Field F] {W : Projective F}

@[simp]
lemma add_map_of_Zeq0_right' {P : PointClass F} {Q : PointRep F} (hP : W.nonsingular_lift P)
    (hQ : W.nonsingular Q) (hQz : Q.z = 0) : W.add_map P ⟦Q⟧ = P := by
  rcases P with ⟨P⟩
  by_cases hPz : P.z = 0
  · erw [W.add_map_of_Zeq0_left _ hPz, Quotient.eq]
    exact equiv_of_Zeq0 hQ hP hQz hPz
  · exact W.add_map_of_Zeq0_right hPz hQz

@[simp]
lemma add_map_zero_right' {P : PointClass F} (hP : W.nonsingular_lift P) :
    W.add_map P ⟦⟨0, 1, 0⟩⟧ = P :=
  add_map_of_Zeq0_right' hP W.nonsingular_zero rfl

private lemma negY_divZ {P : PointRep F} (hPz : P.z ≠ 0) :
    W.negY P / P.z = W.toAffine.negY (P.x / P.z) (P.y / P.z) := by
  rw [negY, WeierstrassCurve.negY]
  linear_combination (norm := ring1) -W.a₃ * mul_inv_cancel hPz

lemma nonsingular_neg {P : PointRep F} (h : W.nonsingular P) : W.nonsingular <| W.neg P := by
  by_cases hPz : P.z = 0
  · rw [W.nonsingular_of_equiv <| W.neg_equiv <| equiv_zero_of_Zeq0 h hPz, neg_zero]
    exact W.nonsingular_zero' <| neg_ne_zero.mpr one_ne_zero
  · rw [W.nonsingular_some_of_Zne0 <| by exact hPz] at h ⊢
    rwa [← nonsingular_neg_iff, ← negY_divZ hPz] at h

lemma nonsingular_lift_neg_map {P : PointClass F} (h : W.nonsingular_lift P) :
    W.nonsingular_lift <| W.neg_map P := by
  rcases P with ⟨P⟩
  exact W.nonsingular_neg h

private lemma Yne_of_Yne {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x) (hy : P.y * Q.z ≠ P.z * W.negY Q) :
    P.y ≠ W.negY P := by
  simp only [mul_comm P.z, ne_eq, ← div_eq_div_iff hPz hQz] at hx hy
  have hy' : P.y / P.z = Q.y / Q.z := Y_eq_of_Y_ne ((nonsingular_some_of_Zne0 hPz).mp hP).left
    ((nonsingular_some_of_Zne0 hQz).mp hQ).left hx <| (negY_divZ hQz).symm ▸ hy
  simp_rw [negY, sub_div, neg_div, mul_div_assoc, ← hy', ← hx, div_self hQz, ← div_self hPz,
    ← mul_div_assoc, ← neg_div, ← sub_div, div_left_inj' hPz] at hy
  exact hy

private lemma addX_div_addZ_of_Yne {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x) (hy : P.y * Q.z ≠ P.z * W.negY Q) :
    (W.add P Q).x / (W.add P Q).z =
      W.addX (P.x / P.z) (Q.x / Q.z) (W.slope (P.x / P.z) (Q.x / Q.z) (P.y / P.z) (Q.y / Q.z)) := by
  have : P.y - W.negY P ≠ 0 := sub_ne_zero_of_ne <| Yne_of_Yne hP hQ hPz hQz hx hy
  rw [W.add_of_Yne hPz hQz hx hy, tan_addX, tan_addX', tan_addZ]
  simp only [mul_comm P.z, ne_eq, ← div_eq_div_iff hPz hQz] at hx hy
  rw [slope_of_Y_ne hx <| (negY_divZ hQz).symm ▸ hy, ← hx, ← negY_divZ hPz]
  field_simp
  ring1

private lemma addX_div_addZ_of_Xne {P Q : PointRep F} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0)
    (hx : P.x * Q.z ≠ P.z * Q.x) : (W.add P Q).x / (W.add P Q).z =
      W.addX (P.x / P.z) (Q.x / Q.z) (W.slope (P.x / P.z) (Q.x / Q.z) (P.y / P.z) (Q.y / Q.z)) := by
  have : P.x * Q.z - P.z * Q.x ≠ 0 := sub_ne_zero_of_ne hx
  rw [W.add_of_Xne hPz hQz hx, sec_addX, sec_addX', sec_addZ,
    slope_of_X_ne <| by rwa [ne_eq, div_eq_div_iff hPz hQz, mul_comm Q.x]]
  field_simp
  ring1

private lemma addY_div_addZ_of_Yne {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x) (hy : P.y * Q.z ≠ P.z * W.negY Q) :
    (W.add P Q).y / (W.add P Q).z = W.addY (P.x / P.z) (Q.x / Q.z) (P.y / P.z)
      (W.slope (P.x / P.z) (Q.x / Q.z) (P.y / P.z) (Q.y / Q.z)) := by
  have : P.y - W.negY P ≠ 0 := sub_ne_zero_of_ne <| Yne_of_Yne hP hQ hPz hQz hx hy
  rw [W.add_of_Yne hPz hQz hx hy, tan_addY, negY, tan_addY', tan_addX, tan_addX', tan_addZ]
  simp only [mul_comm P.z, ne_eq, ← div_eq_div_iff hPz hQz] at hx hy
  rw [slope_of_Y_ne hx <| (negY_divZ hQz).symm ▸ hy, ← hx, ← negY_divZ hPz]
  field_simp
  ring1

private lemma addY_div_addZ_of_Xne {P Q : PointRep F} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0)
    (hx : P.x * Q.z ≠ P.z * Q.x) : (W.add P Q).y / (W.add P Q).z =
      W.addY (P.x / P.z) (Q.x / Q.z) (P.y / P.z)
        (W.slope (P.x / P.z) (Q.x / Q.z) (P.y / P.z) (Q.y / Q.z)) := by
  have : P.x * Q.z - P.z * Q.x ≠ 0 := sub_ne_zero_of_ne hx
  rw [W.add_of_Xne hPz hQz hx, sec_addY, negY, sec_addY', sec_addX, sec_addX', sec_addZ,
    slope_of_X_ne <| by rwa [ne_eq, div_eq_div_iff hPz hQz, mul_comm Q.x]]
  field_simp
  ring1

private lemma addZ_ne_zero_of_Yne {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x) (hy : P.y * Q.z ≠ P.z * W.negY Q) :
    (W.add P Q).z ≠ 0 := by
  rw [W.add_of_Yne hPz hQz hx hy]
  exact mul_ne_zero (pow_ne_zero 3 hPz) <| pow_ne_zero 3 <| sub_ne_zero_of_ne <|
    Yne_of_Yne hP hQ hPz hQz hx hy

private lemma addZ_ne_zero_of_Xne {P Q : PointRep F} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0)
    (hx : P.x * Q.z ≠ P.z * Q.x) : (W.add P Q).z ≠ 0 := by
  rw [W.add_of_Xne hPz hQz hx]
  exact mul_ne_zero (mul_ne_zero hPz hQz) <| pow_ne_zero 3 <| sub_ne_zero_of_ne hx

lemma nonsingular_add {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) :
    W.nonsingular <| W.add P Q := by
  by_cases hPz : P.z = 0
  · rwa [W.nonsingular_of_equiv <| W.add_equiv (equiv_zero_of_Zeq0 hP hPz) <| Setoid.refl Q,
      W.add_of_Zeq0_left Q <| by exact rfl]
  · by_cases hQz : Q.z = 0
    · rwa [W.nonsingular_of_equiv <| W.add_equiv (Setoid.refl P) <| equiv_zero_of_Zeq0 hQ hQz,
        W.add_of_Zeq0_right hPz <| by exact rfl]
    · by_cases hx : P.x * Q.z = P.z * Q.x
      · by_cases hy : P.y * Q.z = P.z * W.negY Q
        · simpa only [W.add_of_Yeq hPz hQz hx hy] using W.nonsingular_zero
        · rw [nonsingular_some_of_Zne0 <| addZ_ne_zero_of_Yne hP hQ hPz hQz hx hy,
            addX_div_addZ_of_Yne hP hQ hPz hQz hx hy, addY_div_addZ_of_Yne hP hQ hPz hQz hx hy]
          exact W.toAffine.nonsingular_add ((nonsingular_some_of_Zne0 hPz).mp hP)
            ((nonsingular_some_of_Zne0 hQz).mp hQ)
            fun _ => (negY_divZ hQz).symm ▸ (mul_comm P.z _ ▸ hy) ∘ (div_eq_div_iff hPz hQz).mp
      · rw [nonsingular_some_of_Zne0 <| addZ_ne_zero_of_Xne hPz hQz hx,
          addX_div_addZ_of_Xne hPz hQz hx, addY_div_addZ_of_Xne hPz hQz hx]
        exact W.toAffine.nonsingular_add ((nonsingular_some_of_Zne0 hPz).mp hP)
          ((nonsingular_some_of_Zne0 hQz).mp hQ)
          fun h => (hx <| mul_comm Q.x P.z ▸ (div_eq_div_iff hPz hQz).mp h).elim

lemma nonsingular_lift_add_map {P Q : PointClass F} (hP : W.nonsingular_lift P)
    (hQ : W.nonsingular_lift Q) : W.nonsingular_lift <| W.add_map P Q := by
  rcases P, Q with ⟨⟨P⟩, ⟨Q⟩⟩
  exact W.nonsingular_add hP hQ

end Addition

section Group

@[pp_dot]
structure Point where
  {point : PointClass R}
  (nonsingular : W.nonsingular_lift point)

attribute [pp_dot] Point.point
attribute [pp_dot] Point.nonsingular

variable {W}

namespace Point

def zero [Nontrivial R] : W.Point :=
  ⟨W.nonsingular_lift_zero⟩

instance [Nontrivial R] : Zero W.Point :=
  ⟨zero⟩

lemma zero_def [Nontrivial R] : (zero : W.Point) = 0 :=
  rfl

def fromAffine [Nontrivial R] : W.toAffine.Point → W.Point
| 0 => 0
| Point.some h => ⟨(W.nonsingular_lift_some ..).mpr h⟩

@[simp]
lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W.Point) :=
  rfl

@[simp]
lemma fromAffine_some [Nontrivial R] {x y : R} (h : W.toAffine.nonsingular x y) :
    fromAffine (Point.some h) = ⟨(W.nonsingular_lift_some ..).mpr h⟩ :=
  rfl

variable {F : Type u} [Field F] {W : Projective F}

@[pp_dot]
def neg (P : W.Point) : W.Point :=
  ⟨W.nonsingular_lift_neg_map P.nonsingular⟩

instance : Neg W.Point :=
  ⟨neg⟩

lemma neg_def (P : W.Point) : P.neg = -P :=
  rfl

@[pp_dot]
noncomputable def add (P : W.Point) (Q : W.Point) : W.Point :=
  ⟨W.nonsingular_lift_add_map P.nonsingular Q.nonsingular⟩

noncomputable instance : Add W.Point :=
  ⟨add⟩

lemma add_def (P Q : W.Point) : P.add Q = P + Q :=
  rfl

noncomputable instance : AddZeroClass W.Point where
  zero_add := fun P => by
    change ⟨nonsingular_lift_add_map W.nonsingular_lift_zero P.nonsingular⟩ = P
    simp only [add_map_zero_left]
  add_zero := fun P => by
    change ⟨nonsingular_lift_add_map P.nonsingular W.nonsingular_lift_zero⟩ = P
    simp only [add_map_zero_right' P.nonsingular]

open scoped Classical

noncomputable def toAffine {P : PointRep F} (h : W.nonsingular P) : W.toAffine.Point :=
  if hPz : P.z = 0 then 0 else Point.some <| (nonsingular_some_of_Zne0 hPz).mp h

@[simp]
lemma toAffine_of_Zeq0 {P : PointRep F} (h : W.nonsingular P) (hPz : P.z = 0) : toAffine h = 0 :=
  dif_pos hPz

@[simp]
lemma toAffine_zero : toAffine W.nonsingular_zero = 0 :=
  toAffine_of_Zeq0 W.nonsingular_zero rfl

@[simp]
lemma toAffine_of_Zne0 {P : PointRep F} (h : W.nonsingular P) (hPz : P.z ≠ 0) :
    toAffine h = Point.some ((nonsingular_some_of_Zne0 hPz).mp h) :=
  dif_neg hPz

@[simp]
lemma toAffine_some {x y : F} (h : W.nonsingular ⟨x, y, 1⟩) :
    toAffine h = Point.some ((W.nonsingular_some x y).mp h) := by
  simp only [toAffine_of_Zne0 h one_ne_zero, div_one]

lemma toAffine_neg {P : PointRep F} (hP : W.nonsingular P) :
    toAffine (nonsingular_neg hP) = -toAffine hP := by
  by_cases hPz : P.z = 0
  · rw [toAffine_of_Zeq0 (nonsingular_neg hP) hPz, toAffine_of_Zeq0 hP hPz, _root_.neg_zero]
  · simpa only [toAffine_of_Zne0 (nonsingular_neg hP) hPz, toAffine_of_Zne0 hP hPz,
      WeierstrassCurve.Point.neg_some, Point.some.injEq] using ⟨rfl, negY_divZ hPz⟩

lemma toAffine_add {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) :
    toAffine (nonsingular_add hP hQ) = toAffine hP + toAffine hQ := by
  by_cases hPz : P.z = 0
  · simp only [W.add_of_Zeq0_left Q hPz, toAffine_of_Zeq0 hP hPz, zero_add]
  · by_cases hQz : Q.z = 0
    · simp only [W.add_of_Zeq0_right hPz hQz, toAffine_of_Zeq0 hQ hQz, add_zero]
    · by_cases hx : P.x * Q.z = P.z * Q.x
      · have hx' : P.x / P.z = Q.x / Q.z := (div_eq_div_iff hPz hQz).mpr <| mul_comm P.z _ ▸ hx
        rw [toAffine_of_Zne0 hP hPz, toAffine_of_Zne0 hQ hQz]
        by_cases hy : P.y * Q.z = P.z * W.negY Q
        · have hy' : P.y / P.z = W.negY Q / Q.z :=
            (div_eq_div_iff hPz hQz).mpr <| mul_comm P.z _ ▸ hy
          simp only [W.add_of_Yeq hPz hQz hx hy]
          rw [toAffine_zero, Point.some_add_some_of_Y_eq hx' <| by rwa [← negY_divZ hQz]]
        · have hy' : P.y / P.z ≠ W.negY Q / Q.z :=
            (mul_comm P.z _ ▸ hy) ∘ (div_eq_div_iff hPz hQz).mp
          rw [toAffine_of_Zne0 _ <| addZ_ne_zero_of_Yne hP hQ hPz hQz hx hy,
            Point.some_add_some_of_Y_ne hx' <| (negY_divZ hQz).symm ▸ hy', Point.some.injEq]
          exact ⟨addX_div_addZ_of_Yne hP hQ hPz hQz hx hy, addY_div_addZ_of_Yne hP hQ hPz hQz hx hy⟩
      · have hx' : P.x / P.z ≠ Q.x / Q.z := (mul_comm P.z _ ▸ hx) ∘ (div_eq_div_iff hPz hQz).mp
        rw [toAffine_of_Zne0 _ <| addZ_ne_zero_of_Xne hPz hQz hx, toAffine_of_Zne0 hP hPz,
          toAffine_of_Zne0 hQ hQz, Point.some_add_some_of_X_ne hx', Point.some.injEq]
        exact ⟨addX_div_addZ_of_Xne hPz hQz hx, addY_div_addZ_of_Xne hPz hQz hx⟩

lemma toAffine_of_equiv (P Q : PointRep F) (h : P ≈ Q) :
    HEq (toAffine (W := W) (P := P)) (toAffine (W := W) (P := Q)) := by
  rcases P, h with ⟨⟨_, _, _⟩, ⟨u, ⟨rfl, rfl, rfl⟩⟩⟩
  refine Function.hfunext (propext <| W.nonsingular_mul_iff Q u) <| fun _ _ _ => ?_
  by_cases hPz : Q.z = 0
  · rw [toAffine_of_Zeq0 _ <| by exact u.mul_right_eq_zero.mpr hPz, toAffine_of_Zeq0 _ hPz]
  · rw [toAffine_of_Zne0 _ <| by exact mul_ne_zero u.ne_zero hPz, toAffine_of_Zne0 _ hPz]
    simp only [heq_eq_eq, Point.some.injEq, mul_div_mul_left _ _ u.ne_zero]

noncomputable def toAffine_lift (P : W.Point) : W.toAffine.Point :=
  P.point.hrecOn (fun _ => toAffine) toAffine_of_equiv P.nonsingular

@[simp]
lemma toAffine_lift_eq {P : PointRep F} (h : W.nonsingular_lift ⟦P⟧) :
    toAffine_lift ⟨h⟩ = toAffine h :=
  rfl

@[simp]
lemma toAffine_lift_of_Zeq0 {P : PointRep F} (h : W.nonsingular P) (hPz : P.z = 0) :
    toAffine_lift ⟨(by exact h : W.nonsingular_lift ⟦P⟧)⟩ = 0 :=
  toAffine_of_Zeq0 h hPz

@[simp]
lemma toAffine_lift_zero : toAffine_lift (0 : W.Point) = 0 :=
  toAffine_zero

@[simp]
lemma toAffine_lift_of_Zne0 {P : PointRep F} (h : W.nonsingular P) (hPz : P.z ≠ 0) :
    toAffine_lift ⟨(by exact h : W.nonsingular_lift ⟦P⟧)⟩ =
      Point.some ((nonsingular_some_of_Zne0 hPz).mp h) :=
  toAffine_of_Zne0 h hPz

@[simp]
lemma toAffine_lift_some {x y : F} (h : W.nonsingular ⟨x, y, 1⟩) :
    toAffine_lift ⟨(by exact h : W.nonsingular_lift ⟦⟨x, y, 1⟩⟧)⟩ =
      Point.some ((W.nonsingular_some x y).mp h) :=
  toAffine_some h

lemma toAffine_lift_neg {P : PointRep F} (h : W.nonsingular P) :
    toAffine_lift (-⟨(by exact h : W.nonsingular_lift ⟦P⟧)⟩) =
      -toAffine_lift ⟨(by exact h : W.nonsingular_lift ⟦P⟧)⟩ :=
  toAffine_neg h

lemma toAffine_lift_add {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) :
    toAffine_lift (⟨(by exact hP : W.nonsingular_lift ⟦P⟧)⟩
        + ⟨(by exact hQ : W.nonsingular_lift ⟦Q⟧)⟩) =
      toAffine_lift ⟨(by exact hP : W.nonsingular_lift ⟦P⟧)⟩
        + toAffine_lift ⟨(by exact hQ : W.nonsingular_lift ⟦Q⟧)⟩ :=
  toAffine_add hP hQ

@[simps]
noncomputable def toAffine_addEquiv : W.Point ≃+ W.toAffine.Point where
  toFun := toAffine_lift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, h⟩
    by_cases hPz : P.z = 0
    · erw [toAffine_lift_eq, toAffine_of_Zeq0 h hPz, fromAffine_zero, mk.injEq, Quotient.eq]
      exact Setoid.symm <| equiv_zero_of_Zeq0 h hPz
    · erw [toAffine_lift_eq, toAffine_of_Zne0 h hPz, fromAffine_some, mk.injEq, Quotient.eq]
      exact Setoid.symm <| equiv_some_of_Zne0 hPz
  right_inv := by
    rintro (_ | _)
    · erw [fromAffine_zero, toAffine_lift_zero, WeierstrassCurve.Point.zero_def]
    · rw [fromAffine_some, toAffine_lift_some]
  map_add' := by
    rintro @⟨⟨_⟩, _⟩ @⟨⟨_⟩, _⟩
    simpa only using toAffine_lift_add _ _

lemma add_left_neg (P : W.Point) : -P + P = 0 :=
  toAffine_addEquiv.injective <| by
    rcases P with @⟨⟨_⟩, _⟩
    simp only [map_add, toAffine_addEquiv_apply, toAffine_lift_neg, _root_.add_left_neg,
      toAffine_lift_zero]

lemma add_comm (P Q : W.Point) : P + Q = Q + P :=
  toAffine_addEquiv.injective <| by simp only [map_add, _root_.add_comm]

lemma add_assoc (P Q R : W.Point) : P + Q + R = P + (Q + R) :=
  toAffine_addEquiv.injective <| by simp only [map_add, _root_.add_assoc]

noncomputable instance : AddCommGroup W.Point where
  zero_add := zero_add
  add_zero := add_zero
  add_left_neg := add_left_neg
  add_comm := add_comm
  add_assoc := add_assoc

end Point

end Group

end WeierstrassCurve.Projective
