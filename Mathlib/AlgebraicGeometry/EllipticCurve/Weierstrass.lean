/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

#align_import algebraic_geometry.elliptic_curve.weierstrass from "leanprover-community/mathlib"@"e2e7f2ac359e7514e4d40061d7c08bb69487ba4e"

/-!
# Weierstrass equations of elliptic curves

This file defines the structure of an elliptic curve as a nonsingular Weierstrass curve given by a
Weierstrass equation, which is mathematically accurate in many cases but also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map
is smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is zero
(this includes all fields, all PIDs, and many other commutative rings) it can be shown (using a lot
of algebro-geometric machinery) that every elliptic curve `E` is a projective plane cubic isomorphic
to a Weierstrass curve given by the equation $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ for
some $a_i$ in `R`, and such that a certain quantity called the discriminant of `E` is a unit in `R`.
If `R` is a field, this quantity divides the discriminant of a cubic polynomial whose roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `E`.

## Main definitions

 * `WeierstrassCurve`: a Weierstrass curve over a commutative ring.
 * `WeierstrassCurve.Δ`: the discriminant of a Weierstrass curve.
 * `WeierstrassCurve.ofJ0`: a Weierstrass curve whose j-invariant is 0.
 * `WeierstrassCurve.ofJ1728`: a Weierstrass curve whose j-invariant is 1728.
 * `WeierstrassCurve.ofJ`: a Weierstrass curve whose j-invariant is neither 0 nor 1728.
 * `WeierstrassCurve.VariableChange`: a change of variables of Weierstrass curves.
 * `WeierstrassCurve.variableChange`: the Weierstrass curve induced by a change of variables.
 * `WeierstrassCurve.baseChange`: the Weierstrass curve base changed over an algebra.
 * `WeierstrassCurve.twoTorsionPolynomial`: the 2-torsion polynomial of a Weierstrass curve.
 * `EllipticCurve`: an elliptic curve over a commutative ring.
 * `EllipticCurve.j`: the j-invariant of an elliptic curve.
 * `EllipticCurve.ofJ0`: an elliptic curve whose j-invariant is 0.
 * `EllipticCurve.ofJ1728`: an elliptic curve whose j-invariant is 1728.
 * `EllipticCurve.ofJ'`: an elliptic curve whose j-invariant is neither 0 nor 1728.
 * `EllipticCurve.ofJ`: an elliptic curve whose j-invariant equal to j.

## Main statements

 * `WeierstrassCurve.twoTorsionPolynomial_disc`: the discriminant of a Weierstrass curve is a
    constant factor of the cubic discriminant of its 2-torsion polynomial.
 * `EllipticCurve.variableChange_j`: the j-invariant of an elliptic curve is invariant under an
    admissible linear change of variables.
 * `EllipticCurve.ofJ_j`: the j-invariant of `EllipticCurve.ofJ` is equal to j.

## Implementation notes

The definition of elliptic curves in this file makes sense for all commutative rings `R`, but it
only gives a type which can be beefed up to a category which is equivalent to the category of
elliptic curves over the spectrum $\mathrm{Spec}(R)$ of `R` in the case that `R` has trivial Picard
group $\mathrm{Pic}(R)$ or, slightly more generally, when its 12-torsion is trivial. The issue is
that for a general ring `R`, there might be elliptic curves over $\mathrm{Spec}(R)$ in the sense of
algebraic geometry which are not globally defined by a cubic equation valid over the entire base.

## References

 * [N Katz and B Mazur, *Arithmetic Moduli of Elliptic Curves*][katz_mazur]
 * [P Deligne, *Courbes Elliptiques: Formulaire (d'après J. Tate)*][deligne_formulaire]
 * [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/

-- porting note: replaced `map_one`, `map_bit0`, and `map_bit1` with `map_ofNat`
local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])

universe u v w

/-! ## Weierstrass curves -/

/-- A Weierstrass curve $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ with parameters $a_i$. -/
@[ext]
structure WeierstrassCurve (R : Type u) where
  (a₁ a₂ a₃ a₄ a₆ : R)
#align weierstrass_curve WeierstrassCurve

namespace WeierstrassCurve

/-- The `a₁` coefficient of a Weierstrass curve. -/
add_decl_doc a₁

/-- The `a₂` coefficient of a Weierstrass curve. -/
add_decl_doc a₂

/-- The `a₃` coefficient of a Weierstrass curve. -/
add_decl_doc a₃

/-- The `a₄` coefficient of a Weierstrass curve. -/
add_decl_doc a₄

/-- The `a₆` coefficient of a Weierstrass curve. -/
add_decl_doc a₆

instance instInhabitedWeierstrassCurve {R : Type u} [Inhabited R] :
    Inhabited <| WeierstrassCurve R :=
  ⟨⟨default, default, default, default, default⟩⟩
#align weierstrass_curve.inhabited WeierstrassCurve.instInhabitedWeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Quantity

/-! ### Standard quantities -/

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `b₂` coefficient of a Weierstrass curve. -/
@[pp_dot]
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂
#align weierstrass_curve.b₂ WeierstrassCurve.b₂

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `b₄` coefficient of a Weierstrass curve. -/
@[pp_dot]
def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃
#align weierstrass_curve.b₄ WeierstrassCurve.b₄

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `b₆` coefficient of a Weierstrass curve. -/
@[pp_dot]
def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆
#align weierstrass_curve.b₆ WeierstrassCurve.b₆

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `b₈` coefficient of a Weierstrass curve. -/
@[pp_dot]
def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2
#align weierstrass_curve.b₈ WeierstrassCurve.b₈

lemma b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈]
  ring1
#align weierstrass_curve.b_relation WeierstrassCurve.b_relation

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `c₄` coefficient of a Weierstrass curve. -/
@[pp_dot]
def c₄ : R :=
  W.b₂ ^ 2 - 24 * W.b₄
#align weierstrass_curve.c₄ WeierstrassCurve.c₄

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `c₆` coefficient of a Weierstrass curve. -/
@[pp_dot]
def c₆ : R :=
  -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆
#align weierstrass_curve.c₆ WeierstrassCurve.c₆

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes
if and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to
sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
@[pp_dot]
def Δ : R :=
  -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
#align weierstrass_curve.Δ WeierstrassCurve.Δ

lemma c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1
#align weierstrass_curve.c_relation WeierstrassCurve.c_relation

end Quantity

section VariableChange

/-! ### Variable changes -/

/-- An admissible linear change of variables of Weierstrass curves defined over a ring `R` given by
a tuple $(u, r, s, t)$ for some $u \in R^\times$ and some $r, s, t \in R$. As a matrix, it is
$\begin{pmatrix} u^2 & 0 & r \cr u^2s & u^3 & t \cr 0 & 0 & 1 \end{pmatrix}$. -/
@[ext]
structure VariableChange (R : Type u) [CommRing R] where
  (u : Rˣ)
  (r s t : R)

namespace VariableChange

/-- The `u` coefficient of an admissible linear change of variables, which must be a unit. -/
add_decl_doc u

/-- The `r` coefficient of an admissible linear change of variables. -/
add_decl_doc r

/-- The `s` coefficient of an admissible linear change of variables. -/
add_decl_doc s

/-- The `t` coefficient of an admissible linear change of variables. -/
add_decl_doc t

variable (C C' C'' : VariableChange R)

/-- The identity linear change of variables given by the identity matrix. -/
def id : VariableChange R :=
  ⟨1, 0, 0, 0⟩

/-- The composition of two linear changes of variables given by matrix multiplication. -/
def comp : VariableChange R where
  u := C.u * C'.u
  r := C.r * ↑C'.u ^ 2 + C'.r
  s := ↑C'.u * C.s + C'.s
  t := C.t * ↑C'.u ^ 3 + C.r * C'.s * ↑C'.u ^ 2 + C'.t

/-- The inverse of a linear change of variables given by matrix inversion. -/
def inv : VariableChange R where
  u := C.u⁻¹
  r := -C.r * ↑C.u⁻¹ ^ 2
  s := -C.s * ↑C.u⁻¹
  t := (C.r * C.s - C.t) * ↑C.u⁻¹ ^ 3

lemma id_comp (C : VariableChange R) : comp id C = C := by
  simp only [comp, id, zero_add, zero_mul, mul_zero, one_mul]

lemma comp_id (C : VariableChange R) : comp C id = C := by
  simp only [comp, id, add_zero, mul_zero, one_mul, mul_one, one_pow, Units.val_one]

lemma comp_left_inv (C : VariableChange R) : comp (inv C) C = id := by
  rw [comp, id, inv]
  ext <;> dsimp only
  · exact C.u.inv_mul
  · linear_combination (norm := ring1) -C.r * pow_mul_pow_eq_one 2 C.u.inv_mul
  · linear_combination (norm := ring1) -C.s * C.u.inv_mul
  · linear_combination (norm := ring1) (C.r * C.s - C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul
      + -C.r * C.s * pow_mul_pow_eq_one 2 C.u.inv_mul

lemma comp_assoc (C C' C'' : VariableChange R) : comp (comp C C') C'' = comp C (comp C' C'') := by
  ext <;> simp only [comp, Units.val_mul] <;> ring1

instance instGroupVariableChange : Group (VariableChange R) where
  one := id
  inv := inv
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_left_inv := comp_left_inv
  mul_assoc := comp_assoc

end VariableChange

variable (C : VariableChange R)

/-- The Weierstrass curve over `R` induced by an admissible linear change of variables
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$. -/
@[pp_dot, simps]
def variableChange : WeierstrassCurve R where
  a₁ := ↑C.u⁻¹ * (W.a₁ + 2 * C.s)
  a₂ := ↑C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
  a₃ := ↑C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
  a₄ := ↑C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
    - 2 * C.s * C.t)
  a₆ := ↑C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
    - C.r * C.t * W.a₁)
#align weierstrass_curve.variable_change WeierstrassCurve.variableChange

lemma variableChange_id : W.variableChange VariableChange.id = W := by
  rw [VariableChange.id, variableChange, inv_one, Units.val_one]
  ext <;> (dsimp only; ring1)

lemma variableChange_comp (C C' : VariableChange R) (W : WeierstrassCurve R) :
    W.variableChange (C.comp C') = (W.variableChange C').variableChange C := by
  simp only [VariableChange.comp, variableChange]
  ext <;> simp only [mul_inv, Units.val_mul]
  · linear_combination (norm := ring1) ↑C.u⁻¹ * C.s * 2 * C'.u.inv_mul
  · linear_combination (norm := ring1)
      C.s * (-C'.s * 2 - W.a₁) * (↑C.u⁻¹ : R) ^ 2 * ↑C'.u⁻¹ * C'.u.inv_mul
        + (C.r * 3 - C.s ^ 2) * (↑C.u⁻¹ : R) ^ 2 * pow_mul_pow_eq_one 2 C'.u.inv_mul
  · linear_combination (norm := ring1)
      C.r * (C'.s * 2 + W.a₁) * (↑C.u⁻¹ : R) ^ 3 * ↑C'.u⁻¹ * pow_mul_pow_eq_one 2 C'.u.inv_mul
        + C.t * 2 * (↑C.u⁻¹ : R) ^ 3 * pow_mul_pow_eq_one 3 C'.u.inv_mul
  · linear_combination (norm := ring1)
      C.s * (-W.a₃ - C'.r * W.a₁ - C'.t * 2) * (↑C.u⁻¹ : R) ^ 4 * (↑C'.u⁻¹ : R) ^ 3 * C'.u.inv_mul
        + (↑C.u⁻¹ : R) ^ 4 * (↑C'.u⁻¹ : R) ^ 2
          * (C.r * C'.r * 6 + C.r * W.a₂ * 2 - C'.s * C.r * W.a₁ * 2 - C'.s ^ 2 * C.r * 2)
          * pow_mul_pow_eq_one 2 C'.u.inv_mul
        + -(↑C.u⁻¹ : R) ^ 4
          * ↑C'.u⁻¹ * (C.s * C'.s * C.r * 2 + C.s * C.r * W.a₁ + C'.s * C.t * 2 + C.t * W.a₁)
          * pow_mul_pow_eq_one 3 C'.u.inv_mul
        + (↑C.u⁻¹ : R) ^ 4 * (C.r ^ 2 * 3 - C.s * C.t * 2) * pow_mul_pow_eq_one 4 C'.u.inv_mul
  · linear_combination (norm := ring1)
      C.r * (↑C.u⁻¹ : R) ^ 6 * (↑C'.u⁻¹ : R) ^ 4 * (C'.r * W.a₂ * 2 - C'.r * C'.s * W.a₁
          + C'.r ^ 2 * 3 + W.a₄ - C'.s * C'.t * 2 - C'.s * W.a₃ - C'.t * W.a₁)
          * pow_mul_pow_eq_one 2 C'.u.inv_mul
        + -(↑C.u⁻¹ : R) ^ 6 * (↑C'.u⁻¹ : R) ^ 3 * C.t * (C'.r * W.a₁ + C'.t * 2 + W.a₃)
          * pow_mul_pow_eq_one 3 C'.u.inv_mul
        + C.r ^ 2 * (↑C.u⁻¹ : R) ^ 6 * (↑C'.u⁻¹ : R) ^ 2
          * (C'.r * 3 + W.a₂ - C'.s * W.a₁ - C'.s ^ 2) * pow_mul_pow_eq_one 4 C'.u.inv_mul
        + -C.r * C.t * (↑C.u⁻¹ : R) ^ 6 * ↑C'.u⁻¹ * (C'.s * 2 + W.a₁)
          * pow_mul_pow_eq_one 5 C'.u.inv_mul
        + (↑C.u⁻¹ : R) ^ 6 * (C.r ^ 3 - C.t ^ 2) * pow_mul_pow_eq_one 6 C'.u.inv_mul

instance instMulActionVariableChange : MulAction (VariableChange R) (WeierstrassCurve R) where
  smul := fun C W => W.variableChange C
  one_smul := variableChange_id
  mul_smul := variableChange_comp

@[simp]
lemma variableChange_b₂ : (W.variableChange C).b₂ = (↑C.u⁻¹ : R) ^ 2 * (W.b₂ + 12 * C.r) := by
  simp only [b₂, variableChange_a₁, variableChange_a₂]
  ring1
#align weierstrass_curve.variable_change_b₂ WeierstrassCurve.variableChange_b₂

@[simp]
lemma variableChange_b₄ :
    (W.variableChange C).b₄ = (↑C.u⁻¹ : R) ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) := by
  simp only [b₂, b₄, variableChange_a₁, variableChange_a₃, variableChange_a₄]
  ring1
#align weierstrass_curve.variable_change_b₄ WeierstrassCurve.variableChange_b₄

@[simp]
lemma variableChange_b₆ : (W.variableChange C).b₆ =
    (↑C.u⁻¹ : R) ^ 6 * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) := by
  simp only [b₂, b₄, b₆, variableChange_a₃, variableChange_a₆]
  ring1
#align weierstrass_curve.variable_change_b₆ WeierstrassCurve.variableChange_b₆

@[simp]
lemma variableChange_b₈ : (W.variableChange C).b₈ = (↑C.u⁻¹ : R) ^ 8 *
    (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) := by
  simp only [b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1
#align weierstrass_curve.variable_change_b₈ WeierstrassCurve.variableChange_b₈

@[simp]
lemma variableChange_c₄ : (W.variableChange C).c₄ = (↑C.u⁻¹ : R) ^ 4 * W.c₄ := by
  simp only [c₄, variableChange_b₂, variableChange_b₄]
  ring1
#align weierstrass_curve.variable_change_c₄ WeierstrassCurve.variableChange_c₄

@[simp]
lemma variableChange_c₆ : (W.variableChange C).c₆ = (↑C.u⁻¹ : R) ^ 6 * W.c₆ := by
  simp only [c₆, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring1
#align weierstrass_curve.variable_change_c₆ WeierstrassCurve.variableChange_c₆

@[simp]
lemma variableChange_Δ : (W.variableChange C).Δ = (↑C.u⁻¹ : R) ^ 12 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1
#align weierstrass_curve.variable_change_Δ WeierstrassCurve.variableChange_Δ

end VariableChange

section BaseChange

/-! ### Base changes -/

variable (A : Type v) [CommRing A] [Algebra R A] (B : Type w) [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The Weierstrass curve over `R` base changed to `A`. -/
@[pp_dot, simps]
def baseChange : WeierstrassCurve A :=
  ⟨algebraMap R A W.a₁, algebraMap R A W.a₂, algebraMap R A W.a₃, algebraMap R A W.a₄,
    algebraMap R A W.a₆⟩
#align weierstrass_curve.base_change WeierstrassCurve.baseChange

@[simp]
lemma baseChange_b₂ : (W.baseChange A).b₂ = algebraMap R A W.b₂ := by
  simp only [b₂, baseChange_a₁, baseChange_a₂]
  map_simp
#align weierstrass_curve.base_change_b₂ WeierstrassCurve.baseChange_b₂

@[simp]
lemma baseChange_b₄ : (W.baseChange A).b₄ = algebraMap R A W.b₄ := by
  simp only [b₄, baseChange_a₁, baseChange_a₃, baseChange_a₄]
  map_simp
#align weierstrass_curve.base_change_b₄ WeierstrassCurve.baseChange_b₄

@[simp]
lemma baseChange_b₆ : (W.baseChange A).b₆ = algebraMap R A W.b₆ := by
  simp only [b₆, baseChange_a₃, baseChange_a₆]
  map_simp
#align weierstrass_curve.base_change_b₆ WeierstrassCurve.baseChange_b₆

@[simp]
lemma baseChange_b₈ : (W.baseChange A).b₈ = algebraMap R A W.b₈ := by
  simp only [b₈, baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄, baseChange_a₆]
  map_simp
#align weierstrass_curve.base_change_b₈ WeierstrassCurve.baseChange_b₈

@[simp]
lemma baseChange_c₄ : (W.baseChange A).c₄ = algebraMap R A W.c₄ := by
  simp only [c₄, baseChange_b₂, baseChange_b₄]
  map_simp
#align weierstrass_curve.base_change_c₄ WeierstrassCurve.baseChange_c₄

@[simp]
lemma baseChange_c₆ : (W.baseChange A).c₆ = algebraMap R A W.c₆ := by
  simp only [c₆, baseChange_b₂, baseChange_b₄, baseChange_b₆]
  map_simp
#align weierstrass_curve.base_change_c₆ WeierstrassCurve.baseChange_c₆

@[simp]
lemma baseChange_Δ : (W.baseChange A).Δ = algebraMap R A W.Δ := by
  simp only [Δ, baseChange_b₂, baseChange_b₄, baseChange_b₆, baseChange_b₈]
  map_simp
#align weierstrass_curve.base_change_Δ WeierstrassCurve.baseChange_Δ

lemma baseChange_self : W.baseChange R = W := by
  ext <;> rfl
#align weierstrass_curve.base_change_self WeierstrassCurve.baseChange_self

lemma baseChange_baseChange : (W.baseChange A).baseChange B = W.baseChange B := by
  ext <;> exact (IsScalarTower.algebraMap_apply R A B _).symm
#align weierstrass_curve.base_change_base_change WeierstrassCurve.baseChange_baseChange

lemma baseChange_injective (h : Function.Injective <| algebraMap R A) :
    Function.Injective <| baseChange (R := R) (A := A) := fun W W' h1 => by
  rcases mk.inj h1 with ⟨_, _, _, _, _⟩
  ext <;> apply_fun _ using h <;> assumption

namespace VariableChange

variable (C : VariableChange R)

/-- The change of variables over `R` base changed to `A`. -/
@[simps]
def baseChange : VariableChange A :=
  ⟨Units.map (algebraMap R A) C.u, algebraMap R A C.r, algebraMap R A C.s, algebraMap R A C.t⟩

lemma baseChange_id : baseChange A (id : VariableChange R) = id := by
  simp only [id, baseChange]
  ext <;> simp only [map_one, Units.val_one, map_zero]

lemma baseChange_comp (C' : VariableChange R) :
    baseChange A (C.comp C') = (baseChange A C).comp (baseChange A C') := by
  simp only [comp, baseChange]
  ext <;> map_simp <;> simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

/-- The base change to `A` of a change of variables over `R` is a group homomorphism. -/
def baseChangeMap : VariableChange R →* VariableChange A where
  toFun := baseChange A
  map_one' := baseChange_id A
  map_mul' := baseChange_comp A

lemma baseChange_self : C.baseChange R = C :=
  rfl

lemma baseChange_baseChange : (C.baseChange A).baseChange B = C.baseChange B := by
  ext <;> exact (IsScalarTower.algebraMap_apply R A B _).symm

lemma baseChange_injective (h : Function.Injective <| algebraMap R A) :
    Function.Injective <| baseChange (R := R) A := fun C C' h1 => by
  rcases mk.inj h1 with ⟨h1, _, _, _⟩
  replace h1 := (Units.mk.inj h1).left
  ext <;> apply_fun _ using h <;> assumption

end VariableChange

lemma baseChange_variableChange (C : VariableChange R) :
    (W.baseChange A).variableChange (C.baseChange A) = (W.variableChange C).baseChange A := by
  simp only [baseChange, variableChange, VariableChange.baseChange]
  ext <;> map_simp <;> simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

end BaseChange

section TorsionPolynomial

/-! ### 2-torsion polynomials -/

/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If
`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `W`. -/
@[pp_dot]
def twoTorsionPolynomial : Cubic R :=
  ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩
#align weierstrass_curve.two_torsion_polynomial WeierstrassCurve.twoTorsionPolynomial

lemma twoTorsionPolynomial_disc : W.twoTorsionPolynomial.disc = 16 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, twoTorsionPolynomial, Cubic.disc]
  ring1
#align weierstrass_curve.two_torsion_polynomial_disc WeierstrassCurve.twoTorsionPolynomial_disc

lemma twoTorsionPolynomial_disc_isUnit [Invertible (2 : R)] :
    IsUnit W.twoTorsionPolynomial.disc ↔ IsUnit W.Δ := by
  rw [twoTorsionPolynomial_disc, IsUnit.mul_iff, show (16 : R) = 2 ^ 4 by norm_num1]
  exact and_iff_right <| isUnit_of_invertible <| 2 ^ 4
#align weierstrass_curve.two_torsion_polynomial_disc_is_unit WeierstrassCurve.twoTorsionPolynomial_disc_isUnit

lemma twoTorsionPolynomial_disc_ne_zero [Nontrivial R] [Invertible (2 : R)] (hΔ : IsUnit W.Δ) :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  (W.twoTorsionPolynomial_disc_isUnit.mpr hΔ).ne_zero
#align weierstrass_curve.two_torsion_polynomial_disc_ne_zero WeierstrassCurve.twoTorsionPolynomial_disc_ne_zero

end TorsionPolynomial

section ModelsWithJ

/-! ### Models with prescribed j-invariant -/

variable (R)

/-- The Weierstrass curve $Y^2 + Y = X^3$. It is of j-invariant 0 if it is an elliptic curve. -/
def ofJ0 : WeierstrassCurve R :=
  ⟨0, 0, 1, 0, 0⟩

lemma ofJ0_c₄ : (ofJ0 R).c₄ = 0 := by
  rw [ofJ0, c₄, b₂, b₄]
  norm_num1

lemma ofJ0_Δ : (ofJ0 R).Δ = -27 := by
  rw [ofJ0, Δ, b₂, b₄, b₆, b₈]
  norm_num1

/-- The Weierstrass curve $Y^2 = X^3 + X$. It is of j-invariant 1728 if it is an elliptic curve. -/
def ofJ1728 : WeierstrassCurve R :=
  ⟨0, 0, 0, 1, 0⟩

lemma ofJ1728_c₄ : (ofJ1728 R).c₄ = -48 := by
  rw [ofJ1728, c₄, b₂, b₄]
  norm_num1

lemma ofJ1728_Δ : (ofJ1728 R).Δ = -64 := by
  rw [ofJ1728, Δ, b₂, b₄, b₆, b₈]
  norm_num1

variable {R} (j : R)

/-- The Weierstrass curve $Y^2 + (j - 1728)XY = X^3 - 36(j - 1728)^3X - (j - 1728)^5$.
It is of j-invariant j if it is an elliptic curve. -/
def ofJ : WeierstrassCurve R :=
  ⟨j - 1728, 0, 0, -36 * (j - 1728) ^ 3, -(j - 1728) ^ 5⟩

lemma ofJ_c₄ : (ofJ j).c₄ = j * (j - 1728) ^ 3 := by
  simp only [ofJ, c₄, b₂, b₄]
  ring1

lemma ofJ_Δ : (ofJ j).Δ = j ^ 2 * (j - 1728) ^ 9 := by
  simp only [ofJ, Δ, b₂, b₄, b₆, b₈]
  ring1

end ModelsWithJ

end WeierstrassCurve

/-! ## Elliptic curves -/

/-- An elliptic curve over a commutative ring. Note that this definition is only mathematically
accurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID. -/
@[ext]
structure EllipticCurve (R : Type u) [CommRing R] extends WeierstrassCurve R where
  Δ' : Rˣ
  coe_Δ' : ↑Δ' = toWeierstrassCurve.Δ
#align elliptic_curve EllipticCurve

namespace EllipticCurve

/-- The discriminant `Δ'` of an elliptic curve over `R`, which is given as a unit in `R`. -/
add_decl_doc Δ'

/-- The discriminant of `E` is equal to the discriminant of `E` as a Weierstrass curve. -/
add_decl_doc coe_Δ'

variable {R : Type u} [CommRing R] (E : EllipticCurve R)

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`. -/
@[pp_dot]
def j : R :=
  ↑E.Δ'⁻¹ * E.c₄ ^ 3
#align elliptic_curve.j EllipticCurve.j

lemma twoTorsionPolynomial_disc_ne_zero [Nontrivial R] [Invertible (2 : R)] :
    E.twoTorsionPolynomial.disc ≠ 0 :=
  E.toWeierstrassCurve.twoTorsionPolynomial_disc_ne_zero <| E.coe_Δ' ▸ E.Δ'.isUnit
#align elliptic_curve.two_torsion_polynomial_disc_ne_zero EllipticCurve.twoTorsionPolynomial_disc_ne_zero

section VariableChange

/-! ### Variable changes -/

variable (C : WeierstrassCurve.VariableChange R)

-- porting note: was just `@[simps]`
/-- The elliptic curve over `R` induced by an admissible linear change of variables
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$.
When `R` is a field, any two Weierstrass equations isomorphic to `E` are related by this. -/
@[pp_dot, simps (config := { rhsMd := .default }) a₁ a₂ a₃ a₄ a₆ Δ' toWeierstrassCurve]
def variableChange : EllipticCurve R :=
  ⟨E.toWeierstrassCurve.variableChange C, C.u⁻¹ ^ 12 * E.Δ', by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_Δ', E.variableChange_Δ]⟩
#align elliptic_curve.variable_change EllipticCurve.variableChange

lemma variableChange_id : E.variableChange WeierstrassCurve.VariableChange.id = E := by
  simp only [variableChange, WeierstrassCurve.variableChange_id]
  simp only [WeierstrassCurve.VariableChange.id, inv_one, one_pow, one_mul]

lemma variableChange_comp (C C' : WeierstrassCurve.VariableChange R) (E : EllipticCurve R) :
    E.variableChange (C.comp C') = (E.variableChange C').variableChange C := by
  simp only [variableChange, WeierstrassCurve.variableChange_comp]
  simp only [WeierstrassCurve.VariableChange.comp, mul_inv, mul_pow, ← mul_assoc]

instance instMulActionVariableChange :
    MulAction (WeierstrassCurve.VariableChange R) (EllipticCurve R) where
  smul := fun C E => E.variableChange C
  one_smul := variableChange_id
  mul_smul := variableChange_comp

lemma coe_variableChange_Δ' : (↑(E.variableChange C).Δ' : R) = (↑C.u⁻¹ : R) ^ 12 * E.Δ' := by
  rw [variableChange_Δ', Units.val_mul, Units.val_pow_eq_pow_val]
#align elliptic_curve.coe_variable_change_Δ' EllipticCurve.coe_variableChange_Δ'

lemma coe_inv_variableChange_Δ' :
    (↑(E.variableChange C).Δ'⁻¹ : R) = (C.u : R) ^ 12 * ↑E.Δ'⁻¹ := by
  rw [variableChange_Δ', mul_inv, inv_pow, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val]
#align elliptic_curve.coe_inv_variable_change_Δ' EllipticCurve.coe_inv_variableChange_Δ'

@[simp]
lemma variableChange_j : (E.variableChange C).j = E.j := by
  rw [j, coe_inv_variableChange_Δ']
  have hu : (C.u * ↑C.u⁻¹ : R) ^ 12 = 1 := by rw [C.u.mul_inv, one_pow]
  linear_combination (norm := (rw [variableChange_toWeierstrassCurve,
    WeierstrassCurve.variableChange_c₄, j]; ring1)) E.j * hu
#align elliptic_curve.variable_change_j EllipticCurve.variableChange_j

end VariableChange

section BaseChange

/-! ### Base changes -/

variable (A : Type v) [CommRing A] [Algebra R A]

-- porting note: was just `@[simps]`
/-- The elliptic curve over `R` base changed to `A`. -/
@[pp_dot, simps (config := { rhsMd := .default }) a₁ a₂ a₃ a₄ a₆ Δ' toWeierstrassCurve]
def baseChange : EllipticCurve A :=
  ⟨E.toWeierstrassCurve.baseChange A, Units.map (↑(algebraMap R A)) E.Δ',
    by simp only [Units.coe_map, coe_Δ', E.baseChange_Δ]; rfl⟩
#align elliptic_curve.base_change EllipticCurve.baseChange

lemma coeBaseChange_Δ' : ↑(E.baseChange A).Δ' = algebraMap R A E.Δ' :=
  rfl
#align elliptic_curve.coe_base_change_Δ' EllipticCurve.coeBaseChange_Δ'

lemma coe_inv_baseChange_Δ' : ↑(E.baseChange A).Δ'⁻¹ = algebraMap R A ↑E.Δ'⁻¹ :=
  rfl
#align elliptic_curve.coe_inv_base_change_Δ' EllipticCurve.coe_inv_baseChange_Δ'

@[simp]
lemma baseChange_j : (E.baseChange A).j = algebraMap R A E.j := by
  simp only [j, baseChange, E.baseChange_c₄]
  map_simp
  rfl
#align elliptic_curve.base_change_j EllipticCurve.baseChange_j

lemma baseChange_injective (h : Function.Injective <| algebraMap R A) :
    Function.Injective <| baseChange (R := R) (A := A) := fun E E' h1 => by
  rcases mk.inj h1 with ⟨h1, h2⟩
  replace h2 := (Units.mk.inj h2).left
  rcases WeierstrassCurve.mk.inj h1 with ⟨_, _, _, _, _⟩
  ext <;> apply_fun _ using h <;> assumption

end BaseChange

section ModelsWithJ

/-! ### Models with prescribed j-invariant -/

variable (R)

/-- When 3 is invertible, $Y^2 + Y = X^3$ is an elliptic curve.
It is of j-invariant 0 (see `EllipticCurve.ofJ0_j`). -/
def ofJ0 [Invertible (3 : R)] : EllipticCurve R :=
  have := invertibleNeg (3 ^ 3 : R)
  ⟨WeierstrassCurve.ofJ0 R, unitOfInvertible (-3 ^ 3 : R),
    by rw [val_unitOfInvertible, WeierstrassCurve.ofJ0_Δ R]; norm_num1⟩

lemma ofJ0_j [Invertible (3 : R)] : (ofJ0 R).j = 0 := by
  simp only [j, ofJ0, WeierstrassCurve.ofJ0_c₄]
  ring1

/-- When 2 is invertible, $Y^2 = X^3 + X$ is an elliptic curve.
It is of j-invariant 1728 (see `EllipticCurve.ofJ1728_j`). -/
def ofJ1728 [Invertible (2 : R)] : EllipticCurve R :=
  have := invertibleNeg (2 ^ 6 : R)
  ⟨WeierstrassCurve.ofJ1728 R, unitOfInvertible (-2 ^ 6 : R),
    by rw [val_unitOfInvertible, WeierstrassCurve.ofJ1728_Δ R]; norm_num1⟩

lemma ofJ1728_j [Invertible (2 : R)] : (ofJ1728 R).j = 1728 := by
  field_simp [j, ofJ1728, @val_unitOfInvertible _ _ _ <| invertibleNeg _,
    WeierstrassCurve.ofJ1728_c₄]
  norm_num1

variable {R}

/-- When j and j - 1728 are both invertible,
$Y^2 + (j - 1728)XY = X^3 - 36(j - 1728)^3X - (j - 1728)^5$ is an elliptic curve.
It is of j-invariant j (see `EllipticCurve.ofJ'_j`). -/
def ofJ' (j : R) [Invertible j] [Invertible (j - 1728)] : EllipticCurve R :=
  have := invertibleMul (j ^ 2) ((j - 1728) ^ 9)
  ⟨WeierstrassCurve.ofJ j, unitOfInvertible <| j ^ 2 * (j - 1728) ^ 9,
    (WeierstrassCurve.ofJ_Δ j).symm⟩

lemma ofJ'_j (j : R) [Invertible j] [Invertible (j - 1728)] : (ofJ' j).j = j := by
  field_simp [EllipticCurve.j, ofJ', @val_unitOfInvertible _ _ _ <| invertibleMul ..,
    WeierstrassCurve.ofJ_c₄]
  ring1

variable {F : Type u} [Field F] (j : F)

private lemma two_or_three_ne_zero : (2 : F) ≠ 0 ∨ (3 : F) ≠ 0 :=
  ne_zero_or_ne_zero_of_nat_coprime <| by decide

variable [DecidableEq F]

/-- For any element j of a field $F$, there exists an elliptic curve over $F$
with j-invariant equal to j (see `EllipticCurve.ofJ_j`).
Its coefficients are given explicitly (see `EllipticCurve.ofJ0`, `EllipticCurve.ofJ1728`
and `EllipticCurve.ofJ'`). -/
def ofJ : EllipticCurve F :=
  if h0 : j = 0 then
    if h3 : (3 : F) = 0 then @ofJ1728 _ _ <| invertibleOfNonzero <|
      two_or_three_ne_zero.neg_resolve_right h3
    else @ofJ0 _ _ <| invertibleOfNonzero h3
  else if h1728 : j = 1728 then
    @ofJ1728 _ _ <| invertibleOfNonzero fun h => h0 <|
    by rw [h1728, show (1728 : F) = 2 * 864 by norm_num1, h, zero_mul]
  else @ofJ' _ _ j (invertibleOfNonzero h0) (invertibleOfNonzero <| sub_ne_zero_of_ne h1728)

lemma ofJ_0_of_three_ne_zero [h3 : NeZero (3 : F)] :
    ofJ 0 = @ofJ0 _ _ (invertibleOfNonzero h3.out) := by
  rw [ofJ, dif_pos rfl, dif_neg h3.out]

lemma ofJ_0_of_three_eq_zero (h3 : (3 : F) = 0) :
    ofJ 0 = @ofJ1728 _ _ (invertibleOfNonzero <| two_or_three_ne_zero.neg_resolve_right h3) := by
  rw [ofJ, dif_pos rfl, dif_pos h3]

lemma ofJ_0_of_two_eq_zero (h2 : (2 : F) = 0) :
    ofJ 0 = @ofJ0 _ _ (invertibleOfNonzero <| two_or_three_ne_zero.neg_resolve_left h2) :=
  have := neZero_iff.2 <| two_or_three_ne_zero.neg_resolve_left h2
  ofJ_0_of_three_ne_zero

lemma ofJ_1728_of_three_eq_zero (h3 : (3 : F) = 0) :
    ofJ 1728 = @ofJ1728 _ _ (invertibleOfNonzero <| two_or_three_ne_zero.neg_resolve_right h3) := by
  rw [ofJ, dif_pos <| by rw [show (1728 : F) = 3 * 576 by norm_num1, h3, zero_mul], dif_pos h3]

lemma ofJ_1728_of_two_ne_zero [h2 : NeZero (2 : F)] :
    ofJ 1728 = @ofJ1728 _ _ (invertibleOfNonzero h2.out) := by
  by_cases h3 : (3 : F) = 0
  · exact ofJ_1728_of_three_eq_zero h3
  · have h : (1728 : F) ≠ 0 := fun h => or_iff_not_and_not.mp
      (mul_eq_zero.mp <| by rwa [show 2 ^ 6 * 3 ^ 3 = (1728 : F) by norm_num1])
      ⟨pow_ne_zero 6 h2.out, pow_ne_zero 3 h3⟩
    rw [ofJ, dif_neg h, dif_pos rfl]

lemma ofJ_1728_of_two_eq_zero (h2 : (2 : F) = 0) :
    ofJ 1728 = @ofJ0 _ _ (invertibleOfNonzero <| two_or_three_ne_zero.neg_resolve_left h2) := by
  rw [ofJ, dif_pos <| by rw [show (1728 : F) = 2 * 864 by norm_num1, h2, zero_mul], dif_neg]

lemma ofJ_ne_0_ne_1728 (h0 : j ≠ 0) (h1728 : j ≠ 1728) : ofJ j =
    @ofJ' _ _ j (invertibleOfNonzero h0) (invertibleOfNonzero <| sub_ne_zero_of_ne h1728) := by
  rw [ofJ, dif_neg h0, dif_neg h1728]

lemma ofJ_j : (ofJ j).j = j := by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
    · rw [h0, ofJ_0_of_three_eq_zero h3,
        @ofJ1728_j _ _ <| invertibleOfNonzero <| two_or_three_ne_zero.neg_resolve_right h3,
        show (1728 : F) = 3 * 576 by norm_num1, h3, zero_mul]
    · rw [h0, ofJ_0_of_three_ne_zero (h3 := neZero_iff.2 h3), @ofJ0_j _ _ <| invertibleOfNonzero h3]
  · by_cases h1728 : j = 1728
    · have h2 : (2 : F) ≠ 0 :=
        fun h => h0 <| by rw [h1728, show (1728 : F) = 2 * 864 by norm_num1, h, zero_mul]
      rw [h1728, ofJ_1728_of_two_ne_zero (h2 := neZero_iff.2 h2),
        @ofJ1728_j _ _ <| invertibleOfNonzero h2]
    · rw [ofJ_ne_0_ne_1728 j h0 h1728,
        @ofJ'_j _ _ _ (invertibleOfNonzero h0) (invertibleOfNonzero <| sub_ne_zero_of_ne h1728)]

instance instInhabitedEllipticCurve : Inhabited <| EllipticCurve F :=
  ⟨ofJ 37⟩
#align elliptic_curve.inhabited EllipticCurve.instInhabitedEllipticCurve

end ModelsWithJ

end EllipticCurve
