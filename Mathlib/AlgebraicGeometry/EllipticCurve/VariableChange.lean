/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata, Jz Pan
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Change of variables of Weierstrass curves

This file defines admissible linear change of variables of Weierstrass curves.

## Main definitions

* `WeierstrassCurve.VariableChange`: a change of variables of Weierstrass curves.
* An instance which states that change of variables forms a group.
* An instance which states that change of variables acts on Weierstrass curves.

## Main statements

* An instance which states that change of variables preserves elliptic curves.
* `WeierstrassCurve.variableChange_j`: the j-invariant of an elliptic curve is invariant under an
  admissible linear change of variables.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, change of variables
-/

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])

universe s u v w

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section VariableChange

/-! ## Variable changes -/

/-- An admissible linear change of variables of Weierstrass curves defined over a ring `R` given by
a tuple `(u, r, s, t)` for some `u` in `Rˣ` and some `r, s, t` in `R`. As a matrix, it is
$$\begin{pmatrix} u^2 & 0 & r \cr u^2s & u^3 & t \cr 0 & 0 & 1 \end{pmatrix}.$$
In other words, this is the change of variables `(X, Y) ↦ (u²X + r, u³Y + u²sX + t)`.
When `R` is a field, any two isomorphic Weierstrass equations are related by this. -/
@[ext]
structure VariableChange (R : Type u) [CommRing R] where
  /-- The `u` coefficient of an admissible linear change of variables, which must be a unit. -/
  u : Rˣ
  /-- The `r` coefficient of an admissible linear change of variables. -/
  r : R
  /-- The `s` coefficient of an admissible linear change of variables. -/
  s : R
  /-- The `t` coefficient of an admissible linear change of variables. -/
  t : R

namespace VariableChange

variable (C C' : VariableChange R)

instance : One (VariableChange R) where
  one := ⟨1, 0, 0, 0⟩

/-- The identity linear change of variables given by the identity matrix. -/
lemma one_def : (1 : VariableChange R) = ⟨1, 0, 0, 0⟩ := rfl

instance : Mul (VariableChange R) where
  mul C C' := {
    u := C.u * C'.u
    r := C.r * C'.u ^ 2 + C'.r
    s := C'.u * C.s + C'.s
    t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t }

/-- The composition of two linear changes of variables given by matrix multiplication. -/
lemma mul_def : C * C' = {
    u := C.u * C'.u
    r := C.r * C'.u ^ 2 + C'.r
    s := C'.u * C.s + C'.s
    t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t } := rfl

instance : Inv (VariableChange R) where
  inv C := {
    u := C.u⁻¹
    r := -C.r * C.u⁻¹ ^ 2
    s := -C.s * C.u⁻¹
    t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3 }

/-- The inverse of a linear change of variables given by matrix inversion. -/
lemma inv_def : C⁻¹ = {
    u := C.u⁻¹
    r := -C.r * C.u⁻¹ ^ 2
    s := -C.s * C.u⁻¹
    t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3 } := rfl

instance : Group (VariableChange R) where
  one_mul C := by
    simp only [mul_def, one_def, zero_add, zero_mul, mul_zero, one_mul]
  mul_one C := by
    simp only [mul_def, one_def, add_zero, mul_zero, one_mul, mul_one, one_pow, Units.val_one]
  inv_mul_cancel C := by
    rw [mul_def, one_def, inv_def]
    ext <;> dsimp only
    · exact C.u.inv_mul
    · linear_combination -C.r * pow_mul_pow_eq_one 2 C.u.inv_mul
    · linear_combination -C.s * C.u.inv_mul
    · linear_combination (C.r * C.s - C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul
        + -C.r * C.s * pow_mul_pow_eq_one 2 C.u.inv_mul
  mul_assoc _ _ _ := by
    ext <;> simp only [mul_def, Units.val_mul] <;> ring1

end VariableChange

variable (C : VariableChange R)

instance : SMul (VariableChange R) (WeierstrassCurve R) where
  smul C W := {
    a₁ := C.u⁻¹ * (W.a₁ + 2 * C.s)
    a₂ := C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
    a₃ := C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
    a₄ := C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t)
    a₆ := C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) }

/-- The Weierstrass curve over `R` induced by an admissible linear change of variables
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` for some `u` in `Rˣ` and some `r, s, t` in `R`. -/
lemma variableChange_def : C • W = {
    a₁ := C.u⁻¹ * (W.a₁ + 2 * C.s)
    a₂ := C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
    a₃ := C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
    a₄ := C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t)
    a₆ := C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) } := rfl

instance : MulAction (VariableChange R) (WeierstrassCurve R) where
  one_smul W := by
    rw [VariableChange.one_def, variableChange_def, inv_one, Units.val_one]
    ext <;> dsimp only <;> ring1
  mul_smul C C' W := by
    simp only [VariableChange.mul_def, variableChange_def]
    ext <;> simp only [mul_inv, Units.val_mul]
    · linear_combination ↑C.u⁻¹ * C.s * 2 * C'.u.inv_mul
    · linear_combination
        C.s * (-C'.s * 2 - W.a₁) * C.u⁻¹ ^ 2 * ↑C'.u⁻¹ * C'.u.inv_mul
          + (C.r * 3 - C.s ^ 2) * C.u⁻¹ ^ 2 * pow_mul_pow_eq_one 2 C'.u.inv_mul
    · linear_combination
        C.r * (C'.s * 2 + W.a₁) * C.u⁻¹ ^ 3 * ↑C'.u⁻¹ * pow_mul_pow_eq_one 2 C'.u.inv_mul
          + C.t * 2 * C.u⁻¹ ^ 3 * pow_mul_pow_eq_one 3 C'.u.inv_mul
    · linear_combination
        C.s * (-W.a₃ - C'.r * W.a₁ - C'.t * 2) * C.u⁻¹ ^ 4 * C'.u⁻¹ ^ 3 * C'.u.inv_mul
          + C.u⁻¹ ^ 4 * C'.u⁻¹ ^ 2 * (C.r * C'.r * 6 + C.r * W.a₂ * 2 - C'.s * C.r * W.a₁ * 2
            - C'.s ^ 2 * C.r * 2) * pow_mul_pow_eq_one 2 C'.u.inv_mul
          - C.u⁻¹ ^ 4 * ↑C'.u⁻¹ * (C.s * C'.s * C.r * 2 + C.s * C.r * W.a₁ + C'.s * C.t * 2
            + C.t * W.a₁) * pow_mul_pow_eq_one 3 C'.u.inv_mul
          + C.u⁻¹ ^ 4 * (C.r ^ 2 * 3 - C.s * C.t * 2) * pow_mul_pow_eq_one 4 C'.u.inv_mul
    · linear_combination
        C.r * C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 4 * (C'.r * W.a₂ * 2 - C'.r * C'.s * W.a₁ + C'.r ^ 2 * 3 + W.a₄
            - C'.s * C'.t * 2 - C'.s * W.a₃ - C'.t * W.a₁) * pow_mul_pow_eq_one 2 C'.u.inv_mul
          - C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 3 * C.t * (C'.r * W.a₁ + C'.t * 2 + W.a₃)
            * pow_mul_pow_eq_one 3 C'.u.inv_mul
          + C.r ^ 2 * C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 2 * (C'.r * 3 + W.a₂ - C'.s * W.a₁ - C'.s ^ 2)
            * pow_mul_pow_eq_one 4 C'.u.inv_mul
          - C.r * C.t * C.u⁻¹ ^ 6 * ↑C'.u⁻¹ * (C'.s * 2 + W.a₁) * pow_mul_pow_eq_one 5 C'.u.inv_mul
          + C.u⁻¹ ^ 6 * (C.r ^ 3 - C.t ^ 2) * pow_mul_pow_eq_one 6 C'.u.inv_mul

lemma variableChange_a₁ : (C • W).a₁ = C.u⁻¹ * (W.a₁ + 2 * C.s) := rfl

lemma variableChange_a₂ : (C • W).a₂ = C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := rfl

lemma variableChange_a₃ : (C • W).a₃ = C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) := rfl

lemma variableChange_a₄ : (C • W).a₄ =
    C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t) := rfl

lemma variableChange_a₆ : (C • W).a₆ =
    C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) := rfl

lemma variableChange_b₂ : (C • W).b₂ = C.u⁻¹ ^ 2 * (W.b₂ + 12 * C.r) := by
  simp only [b₂, variableChange_a₁, variableChange_a₂]
  ring1

lemma variableChange_b₄ : (C • W).b₄ = C.u⁻¹ ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) := by
  simp only [b₂, b₄, variableChange_a₁, variableChange_a₃, variableChange_a₄]
  ring1

lemma variableChange_b₆ : (C • W).b₆ =
    C.u⁻¹ ^ 6 * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) := by
  simp only [b₂, b₄, b₆, variableChange_a₃, variableChange_a₆]
  ring1

lemma variableChange_b₈ : (C • W).b₈ = C.u⁻¹ ^ 8 *
    (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) := by
  simp only [b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

lemma variableChange_c₄ : (C • W).c₄ = C.u⁻¹ ^ 4 * W.c₄ := by
  simp only [c₄, variableChange_b₂, variableChange_b₄]
  ring1

lemma variableChange_c₆ : (C • W).c₆ = C.u⁻¹ ^ 6 * W.c₆ := by
  simp only [c₆, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring1

lemma variableChange_Δ : (C • W).Δ = C.u⁻¹ ^ 12 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

variable [W.IsElliptic]

instance : (C • W).IsElliptic := by
  rw [isElliptic_iff, variableChange_Δ]
  exact (C.u⁻¹.isUnit.pow 12).mul W.isUnit_Δ

set_option linter.docPrime false in
lemma variableChange_Δ' : (C • W).Δ' = C.u⁻¹ ^ 12 * W.Δ' := by
  simp_rw [Units.ext_iff, Units.val_mul, coe_Δ', variableChange_Δ, Units.val_pow_eq_pow_val]

set_option linter.docPrime false in
lemma coe_variableChange_Δ' : ((C • W).Δ' : R) = C.u⁻¹ ^ 12 * W.Δ' := by
  simp_rw [coe_Δ', variableChange_Δ]

set_option linter.docPrime false in
lemma inv_variableChange_Δ' : (C • W).Δ'⁻¹ = C.u ^ 12 * W.Δ'⁻¹ := by
  rw [variableChange_Δ', mul_inv, inv_pow, inv_inv]

set_option linter.docPrime false in
lemma coe_inv_variableChange_Δ' : (↑(C • W).Δ'⁻¹ : R) = C.u ^ 12 * W.Δ'⁻¹ := by
  rw [inv_variableChange_Δ', Units.val_mul, Units.val_pow_eq_pow_val]

@[simp]
lemma variableChange_j : (C • W).j = W.j := by
  rw [j, coe_inv_variableChange_Δ', variableChange_c₄, j, mul_pow, ← pow_mul, ← mul_assoc,
    mul_right_comm (C.u.val ^ 12), ← mul_pow, C.u.mul_inv, one_pow, one_mul]

end VariableChange

section BaseChange

/-! ## Maps and base changes -/

variable {A : Type v} [CommRing A] (φ : R →+* A)

namespace VariableChange

variable (C : VariableChange R)

/-- The change of variables mapped over a ring homomorphism `φ : R →+* A`. -/
@[simps]
def map : VariableChange A :=
  ⟨Units.map φ C.u, φ C.r, φ C.s, φ C.t⟩

variable (A) in
/-- The change of variables base changed to an algebra `A` over `R`. -/
abbrev baseChange [Algebra R A] : VariableChange A :=
  C.map <| algebraMap R A

@[simp]
lemma map_id : C.map (RingHom.id R) = C :=
  rfl

lemma map_map {A : Type v} [CommRing A] (φ : R →+* A) {B : Type w} [CommRing B] (ψ : A →+* B) :
    (C.map φ).map ψ = C.map (ψ.comp φ) :=
  rfl

@[simp]
lemma map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (ψ : A →ₐ[S] B) : (C.baseChange A).map ψ = C.baseChange B :=
  congr_arg C.map <| ψ.comp_algebraMap_of_tower R

lemma map_injective {φ : R →+* A} (hφ : Function.Injective φ) :
    Function.Injective <| map (φ := φ) := fun _ _ h => by
  rcases mk.inj h with ⟨h, _, _, _⟩
  replace h := (Units.mk.inj h).left
  ext <;> apply_fun _ using hφ <;> assumption

/-- The map over a ring homomorphism of a change of variables is a group homomorphism. -/
def mapHom : VariableChange R →* VariableChange A where
  toFun := map φ
  map_one' := by
    simp only [one_def, map]
    ext <;> simp only [map_one, Units.val_one, map_zero]
  map_mul' C C' := by
    simp only [mul_def, map]
    ext <;> map_simp <;> simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

end VariableChange

lemma map_variableChange (C : VariableChange R) : (C.map φ) • (W.map φ) = (C • W).map φ := by
  simp only [map, variableChange_def, VariableChange.map]
  ext <;> map_simp <;> simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

end BaseChange

end WeierstrassCurve
