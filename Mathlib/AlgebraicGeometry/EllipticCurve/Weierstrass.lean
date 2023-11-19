/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.RingTheory.Norm
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
 * `WeierstrassCurve.ofJ0`, `WeierstrassCurve.ofJ1728`, `WeierstrassCurve.ofJ`:
    Weierstrass curves whose $j$-invariants are $0$, $1728$ and $j\neq 0,1728$, respectively.
 * `WeierstrassCurve.VariableChange`: a change of variables of Weierstrass curves.
 * `WeierstrassCurve.variableChange`: the Weierstrass curve induced by a change of variables.
 * `WeierstrassCurve.baseChange`: the Weierstrass curve base changed over an algebra.
 * `WeierstrassCurve.twoTorsionPolynomial`: the 2-torsion polynomial of a Weierstrass curve.
 * `WeierstrassCurve.polynomial`: the polynomial associated to a Weierstrass curve.
 * `WeierstrassCurve.equation`: the Weierstrass equation of a Weierstrass curve.
 * `WeierstrassCurve.nonsingular`: the nonsingular condition at a point on a Weierstrass curve.
 * `WeierstrassCurve.CoordinateRing`: the coordinate ring of a Weierstrass curve.
 * `WeierstrassCurve.FunctionField`: the function field of a Weierstrass curve.
 * `WeierstrassCurve.CoordinateRing.basis`: the power basis of the coordinate ring over `R[X]`.
 * `EllipticCurve`: an elliptic curve over a commutative ring.
 * `EllipticCurve.j`: the j-invariant of an elliptic curve.
 * `EllipticCurve.ofJ0`, `EllipticCurve.ofJ1728`, `EllipticCurve.ofJ'`: elliptic curves whose
    $j$-invariants are $0$, $1728$ and $j\neq 0,1728$, respectively.
 * `EllipticCurve.ofJ`: an elliptic curve over a field $F$, whose $j$-invariant equal to $j$.

## Main statements

 * `WeierstrassCurve.twoTorsionPolynomial_disc`: the discriminant of a Weierstrass curve is a
    constant factor of the cubic discriminant of its 2-torsion polynomial.
 * `WeierstrassCurve.nonsingular_of_Δ_ne_zero`: a Weierstrass curve is nonsingular at every point
    if its discriminant is non-zero.
 * `WeierstrassCurve.CoordinateRing.instIsDomainCoordinateRing`: the coordinate ring of a
    Weierstrass curve is an integral domain.
 * `WeierstrassCurve.CoordinateRing.degree_norm_smul_basis`: the degree of the norm of an element
    in the coordinate ring in terms of the power basis.
 * `EllipticCurve.nonsingular`: an elliptic curve is nonsingular at every point.
 * `EllipticCurve.variableChange_j`: the j-invariant of an elliptic curve is invariant under an
    admissible linear change of variables.
 * `EllipticCurve.ofJ_j`: the $j$-invariant of `EllipticCurve.ofJ` is equal to $j$.

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

variable {R : Type u}

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

instance instInhabitedWeierstrassCurve [Inhabited R] : Inhabited <| WeierstrassCurve R :=
  ⟨⟨default, default, default, default, default⟩⟩
#align weierstrass_curve.inhabited WeierstrassCurve.instInhabitedWeierstrassCurve

variable [CommRing R] (W : WeierstrassCurve R)

section Quantity

/-! ### Standard quantities -/

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `b₂` coefficient of a Weierstrass curve. -/
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂
#align weierstrass_curve.b₂ WeierstrassCurve.b₂

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `b₄` coefficient of a Weierstrass curve. -/
def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃
#align weierstrass_curve.b₄ WeierstrassCurve.b₄

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `b₆` coefficient of a Weierstrass curve. -/
def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆
#align weierstrass_curve.b₆ WeierstrassCurve.b₆

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `b₈` coefficient of a Weierstrass curve. -/
def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2
#align weierstrass_curve.b₈ WeierstrassCurve.b₈

lemma b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈]
  ring1
#align weierstrass_curve.b_relation WeierstrassCurve.b_relation

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `c₄` coefficient of a Weierstrass curve. -/
def c₄ : R :=
  W.b₂ ^ 2 - 24 * W.b₄
#align weierstrass_curve.c₄ WeierstrassCurve.c₄

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The `c₆` coefficient of a Weierstrass curve. -/
def c₆ : R :=
  -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆
#align weierstrass_curve.c₆ WeierstrassCurve.c₆

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes
if and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to
sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
def Δ : R :=
  -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
#align weierstrass_curve.Δ WeierstrassCurve.Δ

lemma c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1
#align weierstrass_curve.c_relation WeierstrassCurve.c_relation

end Quantity

section ModelsWithJ

variable (R)

/-- The Weierstrass curve $Y^2 + Y = X^3$.
It is of $j$-invariant $0$ if it is an elliptic curve. -/
def ofJ0 : WeierstrassCurve R :=
  ⟨0, 0, 1, 0, 0⟩

lemma ofJ0_c₄ : (ofJ0 R).c₄ = 0 := by
  rw [ofJ0, c₄, b₂, b₄]
  norm_num1

lemma ofJ0_Δ : (ofJ0 R).Δ = -27 := by
  rw [ofJ0, Δ, b₂, b₄, b₆, b₈]
  norm_num1

/-- The Weierstrass curve $Y^2 = X^3 + X$.
It is of $j$-invariant $1728$ if it is an elliptic curve. -/
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
It is of $j$-invariant $j$ if it is an elliptic curve. -/
def ofJ : WeierstrassCurve R :=
  ⟨j - 1728, 0, 0, -36 * (j - 1728) ^ 3, -(j - 1728) ^ 5⟩

lemma ofJ_c₄ : (ofJ j).c₄ = j * (j - 1728) ^ 3 := by
  simp only [ofJ, c₄, b₂, b₄]
  ring1

lemma ofJ_Δ : (ofJ j).Δ = j ^ 2 * (j - 1728) ^ 9 := by
  simp only [ofJ, Δ, b₂, b₄, b₆, b₈]
  ring1

end ModelsWithJ

section VariableChange

/-! ### Variable changes -/

/-- An admissible linear change of variables of Weierstrass curves defined over a ring `R`.
It consists of a tuple $(u,r,s,t)$ of elements in $R$, with $u$ invertible.
As a matrix, it is $\begin{pmatrix}
u^2 & 0 & r \cr
u^2s & u^3 & t \cr
0 & 0 & 1
\end{pmatrix}$. -/
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

/-- The identity linear change of variables. As a matrix, it is just identity matrix. -/
def id : VariableChange R :=
  ⟨1, 0, 0, 0⟩

/-- The composition of two linear change of variables. As matrices, it is just matrix
multiplcation. -/
def comp : VariableChange R where
  u := C.u * C'.u
  r := C.r * ↑C'.u ^ 2 + C'.r
  s := ↑C'.u * C.s + C'.s
  t := C.t * ↑C'.u ^ 3 + C.r * C'.s * ↑C'.u ^ 2 + C'.t

/-- The inverse of a linear change of variables. As a matrix, it is just matrix inverse. -/
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
  · linear_combination (norm := ring1)
      (C.r * C.s - C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul
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
@[simps]
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
lemma variableChange_b₆ :
    (W.variableChange C).b₆ =
      (↑C.u⁻¹ : R) ^ 6 * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) := by
  simp only [b₂, b₄, b₆, variableChange_a₃, variableChange_a₆]
  ring1
#align weierstrass_curve.variable_change_b₆ WeierstrassCurve.variableChange_b₆

@[simp]
lemma variableChange_b₈ :
    (W.variableChange C).b₈ =
      (↑C.u⁻¹ : R) ^ 8 * (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂
        + 3 * C.r ^ 4) := by
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

variable (A : Type v) [CommRing A] [Algebra R A] (B : Type w) [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

section BaseChange

/-! ### Base changes -/

/-- The Weierstrass curve over `R` base changed to `A`. -/
@[simps]
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
  ext <;> simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe,
    map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow]

/-- The base change of change of variables over `R` to `A` is a group homomorphism. -/
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
  ext <;> simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe,
    map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow]

end BaseChange

section TorsionPolynomial

/-! ### 2-torsion polynomials -/

/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If
`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `W`. -/
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

/-- The notation `Y` for `X` in the `PolynomialPolynomial` scope. -/
scoped[PolynomialPolynomial] notation "Y" => Polynomial.X

/-- The notation `R[X][Y]` for `R[X][X]` in the `PolynomialPolynomial` scope. -/
scoped[PolynomialPolynomial] notation R "[X][Y]" => Polynomial (Polynomial R)

section Polynomial

/-! ### Weierstrass equations -/

open Polynomial

-- porting note: relocated into `Polynomial` section
local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

-- porting note: relocated into `Polynomial` section
local macro "C_simp" : tactic =>
  `(tactic| simp only [C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

open scoped Polynomial PolynomialPolynomial

/-- The polynomial $W(X, Y) := Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$ associated to a
Weierstrass curve `W` over `R`. For ease of polynomial manipulation, this is represented as a term
of type `R[X][X]`, where the inner variable represents $X$ and the outer variable represents $Y$.
For clarity, the alternative notations `Y` and `R[X][Y]` are provided in the `PolynomialPolynomial`
scope to represent the outer variable and the bivariate polynomial ring `R[X][X]` respectively. -/
protected noncomputable def polynomial : R[X][Y] :=
  Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
#align weierstrass_curve.polynomial WeierstrassCurve.polynomial

lemma polynomial_eq :
    W.polynomial =
      Cubic.toPoly
        ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ := by
  simp only [WeierstrassCurve.polynomial, Cubic.toPoly]
  C_simp
  ring1
#align weierstrass_curve.polynomial_eq WeierstrassCurve.polynomial_eq

lemma polynomial_ne_zero [Nontrivial R] : W.polynomial ≠ 0 := by
  rw [polynomial_eq]
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero
#align weierstrass_curve.polynomial_ne_zero WeierstrassCurve.polynomial_ne_zero

@[simp]
lemma degree_polynomial [Nontrivial R] : W.polynomial.degree = 2 := by
  rw [polynomial_eq]
  exact Cubic.degree_of_b_ne_zero' one_ne_zero
#align weierstrass_curve.degree_polynomial WeierstrassCurve.degree_polynomial

@[simp]
lemma natDegree_polynomial [Nontrivial R] : W.polynomial.natDegree = 2 := by
  rw [polynomial_eq]
  exact Cubic.natDegree_of_b_ne_zero' one_ne_zero
#align weierstrass_curve.nat_degree_polynomial WeierstrassCurve.natDegree_polynomial

lemma monic_polynomial : W.polynomial.Monic := by
  nontriviality R
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'
#align weierstrass_curve.monic_polynomial WeierstrassCurve.monic_polynomial

lemma irreducible_polynomial [IsDomain R] : Irreducible W.polynomial := by
  by_contra h
  rcases (W.monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff W.natDegree_polynomial).mp
    h with ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_ne_zero' R, degree_mul] at h0
  apply (h1.symm.le.trans Cubic.degree_of_b_eq_zero').not_lt
  rcases Nat.WithBot.add_eq_three_iff.mp h0.symm with h | h | h | h
  -- porting note: replaced two `any_goals` proofs with two `iterate 2` proofs
  iterate 2 rw [degree_add_eq_right_of_degree_lt] <;> simp only [h] <;> decide
  iterate 2 rw [degree_add_eq_left_of_degree_lt] <;> simp only [h] <;> decide
#align weierstrass_curve.irreducible_polynomial WeierstrassCurve.irreducible_polynomial

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma eval_polynomial (x y : R) :
    (W.polynomial.eval <| C y).eval x =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [WeierstrassCurve.polynomial]
  eval_simp
  rw [add_mul, ← add_assoc]
#align weierstrass_curve.eval_polynomial WeierstrassCurve.eval_polynomial

@[simp]
lemma eval_polynomial_zero : (W.polynomial.eval 0).eval 0 = -W.a₆ := by
  simp only [← C_0, eval_polynomial, zero_add, zero_sub, mul_zero, zero_pow <| Nat.zero_lt_succ _]
#align weierstrass_curve.eval_polynomial_zero WeierstrassCurve.eval_polynomial_zero

-- porting note: added `protected` for consistency with `WeierstrassCurve.polynomial`
/-- The proposition that an affine point $(x, y)$ lies in `W`. In other words, $W(x, y) = 0$. -/
protected def equation (x y : R) : Prop :=
  (W.polynomial.eval <| C y).eval x = 0
#align weierstrass_curve.equation WeierstrassCurve.equation

lemma equation_iff' (x y : R) :
    W.equation x y ↔
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
  rw [WeierstrassCurve.equation, eval_polynomial]
#align weierstrass_curve.equation_iff' WeierstrassCurve.equation_iff'

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma equation_iff (x y : R) :
    W.equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [equation_iff', sub_eq_zero]
#align weierstrass_curve.equation_iff WeierstrassCurve.equation_iff

@[simp]
lemma equation_zero : W.equation 0 0 ↔ W.a₆ = 0 := by
  rw [WeierstrassCurve.equation, C_0, eval_polynomial_zero, neg_eq_zero]
#align weierstrass_curve.equation_zero WeierstrassCurve.equation_zero

lemma equation_iff_variableChange (x y : R) :
    W.equation x y ↔ (W.variableChange ⟨1, x, 0, y⟩).equation 0 0 := by
  rw [equation_iff', ← neg_eq_zero, equation_zero, variableChange_a₆, inv_one, Units.val_one]
  congr! 1
  ring1
#align weierstrass_curve.equation_iff_variable_change WeierstrassCurve.equation_iff_variableChange

lemma equation_iff_baseChange [Nontrivial A] [NoZeroSMulDivisors R A] (x y : R) :
    W.equation x y ↔ (W.baseChange A).equation (algebraMap R A x) (algebraMap R A y) := by
  simp only [equation_iff]
  exact
    ⟨fun h => by convert congr_arg (algebraMap R A) h <;> map_simp <;> rfl,
      fun h => by apply NoZeroSMulDivisors.algebraMap_injective R A; map_simp; exact h⟩
#align weierstrass_curve.equation_iff_base_change WeierstrassCurve.equation_iff_baseChange

lemma equation_iff_baseChange_of_baseChange [Nontrivial B] [NoZeroSMulDivisors A B] (x y : A) :
    (W.baseChange A).equation x y ↔
      (W.baseChange B).equation (algebraMap A B x) (algebraMap A B y) := by
  rw [equation_iff_baseChange (W.baseChange A) B, baseChange_baseChange]
#align weierstrass_curve.equation_iff_base_change_of_base_change WeierstrassCurve.equation_iff_baseChange_of_baseChange

/-! ### Nonsingularity of Weierstrass curves -/

-- porting note: added `protected` for consistency with `WeierstrassCurve.polynomial`
/-- The partial derivative $W_X(X, Y)$ of $W(X, Y)$ with respect to $X$.

TODO: define this in terms of `Polynomial.derivative`. -/
protected noncomputable def polynomialX : R[X][Y] :=
  C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.polynomial_X WeierstrassCurve.polynomialX

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma eval_polynomialX (x y : R) :
    (W.polynomialX.eval <| C y).eval x = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
  simp only [WeierstrassCurve.polynomialX]
  eval_simp
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.eval_polynomial_X WeierstrassCurve.eval_polynomialX

@[simp]
lemma eval_polynomialX_zero : (W.polynomialX.eval 0).eval 0 = -W.a₄ := by
  simp only [← C_0, eval_polynomialX, zero_add, zero_sub, mul_zero, zero_pow zero_lt_two]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.eval_polynomial_X_zero WeierstrassCurve.eval_polynomialX_zero

-- porting note: added `protected` for consistency with `WeierstrassCurve.polynomial`
/-- The partial derivative $W_Y(X, Y)$ of $W(X, Y)$ with respect to $Y$.

TODO: define this in terms of `Polynomial.derivative`. -/
protected noncomputable def polynomialY : R[X][Y] :=
  C (C 2) * Y + C (C W.a₁ * X + C W.a₃)
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.polynomial_Y WeierstrassCurve.polynomialY

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma eval_polynomialY (x y : R) :
    (W.polynomialY.eval <| C y).eval x = 2 * y + W.a₁ * x + W.a₃ := by
  simp only [WeierstrassCurve.polynomialY]
  eval_simp
  rw [← add_assoc]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.eval_polynomial_Y WeierstrassCurve.eval_polynomialY

@[simp]
lemma eval_polynomialY_zero : (W.polynomialY.eval 0).eval 0 = W.a₃ := by
  simp only [← C_0, eval_polynomialY, zero_add, mul_zero]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.eval_polynomial_Y_zero WeierstrassCurve.eval_polynomialY_zero

-- porting note: added `protected` for consistency with `WeierstrassCurve.polynomial`
/-- The proposition that an affine point $(x, y)$ on `W` is nonsingular.
In other words, either $W_X(x, y) \ne 0$ or $W_Y(x, y) \ne 0$. -/
protected def nonsingular (x y : R) : Prop :=
  W.equation x y ∧ ((W.polynomialX.eval <| C y).eval x ≠ 0 ∨ (W.polynomialY.eval <| C y).eval x ≠ 0)
#align weierstrass_curve.nonsingular WeierstrassCurve.nonsingular

lemma nonsingular_iff' (x y : R) :
    W.nonsingular x y ↔
      W.equation x y ∧
        (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0) := by
  rw [WeierstrassCurve.nonsingular, equation_iff', eval_polynomialX, eval_polynomialY]
#align weierstrass_curve.nonsingular_iff' WeierstrassCurve.nonsingular_iff'

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma nonsingular_iff (x y : R) :
    W.nonsingular x y ↔
      W.equation x y ∧ (W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃) := by
  rw [nonsingular_iff', sub_ne_zero, ← @sub_ne_zero _ _ y]
  congr! 3
  ring1
#align weierstrass_curve.nonsingular_iff WeierstrassCurve.nonsingular_iff

@[simp]
lemma nonsingular_zero : W.nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ ≠ 0 ∨ W.a₄ ≠ 0) := by
  rw [WeierstrassCurve.nonsingular, equation_zero, C_0, eval_polynomialX_zero, neg_ne_zero,
    eval_polynomialY_zero, or_comm]
#align weierstrass_curve.nonsingular_zero WeierstrassCurve.nonsingular_zero

lemma nonsingular_iff_variableChange (x y : R) :
    W.nonsingular x y ↔ (W.variableChange ⟨1, x, 0, y⟩).nonsingular 0 0 := by
  rw [nonsingular_iff', equation_iff_variableChange, equation_zero, ← neg_ne_zero, or_comm,
    nonsingular_zero, variableChange_a₃, variableChange_a₄, inv_one, Units.val_one]
  simp only [variableChange]
  congr! 3 <;> ring1
#align weierstrass_curve.nonsingular_iff_variable_change WeierstrassCurve.nonsingular_iff_variableChange

lemma nonsingular_iff_baseChange [Nontrivial A] [NoZeroSMulDivisors R A] (x y : R) :
    W.nonsingular x y ↔ (W.baseChange A).nonsingular (algebraMap R A x) (algebraMap R A y) := by
  rw [nonsingular_iff, nonsingular_iff, and_congr <| W.equation_iff_baseChange A x y]
  refine
    ⟨Or.imp (not_imp_not.mpr fun h => ?_) (not_imp_not.mpr fun h => ?_),
      Or.imp (not_imp_not.mpr fun h => ?_) (not_imp_not.mpr fun h => ?_)⟩
  any_goals apply NoZeroSMulDivisors.algebraMap_injective R A; map_simp; exact h
  any_goals convert congr_arg (algebraMap R A) h <;> map_simp <;> rfl
#align weierstrass_curve.nonsingular_iff_base_change WeierstrassCurve.nonsingular_iff_baseChange

lemma nonsingular_iff_baseChange_of_baseChange [Nontrivial B] [NoZeroSMulDivisors A B] (x y : A) :
    (W.baseChange A).nonsingular x y ↔
      (W.baseChange B).nonsingular (algebraMap A B x) (algebraMap A B y) := by
  rw [nonsingular_iff_baseChange (W.baseChange A) B, baseChange_baseChange]
#align weierstrass_curve.nonsingular_iff_base_change_of_base_change WeierstrassCurve.nonsingular_iff_baseChange_of_baseChange

lemma nonsingular_zero_of_Δ_ne_zero (h : W.equation 0 0) (hΔ : W.Δ ≠ 0) : W.nonsingular 0 0 := by
  simp only [equation_zero, nonsingular_zero] at *
  contrapose! hΔ
  simp only [b₂, b₄, b₆, b₈, Δ, h, hΔ]
  ring1
#align weierstrass_curve.nonsingular_zero_of_Δ_ne_zero WeierstrassCurve.nonsingular_zero_of_Δ_ne_zero

/-- A Weierstrass curve is nonsingular at every point if its discriminant is non-zero. -/
lemma nonsingular_of_Δ_ne_zero {x y : R} (h : W.equation x y) (hΔ : W.Δ ≠ 0) : W.nonsingular x y :=
  (W.nonsingular_iff_variableChange x y).mpr <|
    nonsingular_zero_of_Δ_ne_zero _ ((W.equation_iff_variableChange x y).mp h) <| by
      rwa [variableChange_Δ, inv_one, Units.val_one, one_pow, one_mul]
#align weierstrass_curve.nonsingular_of_Δ_ne_zero WeierstrassCurve.nonsingular_of_Δ_ne_zero

/-! ### Ideals in the coordinate ring -/

-- porting note: in Lean 3, this is a `def` under a `derive comm_ring` tag.
-- This generates a reducible instance of `comm_ring` for `coordinate_ring`. In certain
-- circumstances this might be extremely slow, because all instances in its definition are unified
-- exponentially many times. In this case, one solution is to manually add the local attribute
-- `local attribute [irreducible] coordinate_ring.comm_ring` to block this type-level unification.
-- In Lean 4, this is no longer an issue and is now an `abbrev`. See Zulip thread:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20class_group.2Emk
/-- The coordinate ring $R[W] := R[X, Y] / \langle W(X, Y) \rangle$ of `W`. -/
abbrev CoordinateRing : Type u :=
  AdjoinRoot W.polynomial
#align weierstrass_curve.coordinate_ring WeierstrassCurve.CoordinateRing

/-- The function field $R(W) := \mathrm{Frac}(R[W])$ of `W`. -/
abbrev FunctionField : Type u :=
  FractionRing W.CoordinateRing
#align weierstrass_curve.function_field WeierstrassCurve.FunctionField

namespace CoordinateRing

-- porting note: added the abbreviation `mk` for `AdjoinRoot.mk W.polynomial`
/-- An element of the coordinate ring `R[W]` of `W` over `R`. -/
noncomputable abbrev mk : R[X][Y] →+* W.CoordinateRing :=
  AdjoinRoot.mk W.polynomial

open Ideal

instance instIsDomainCoordinateRing [IsDomain R] [NormalizedGCDMonoid R] :
    IsDomain W.CoordinateRing :=
  (Quotient.isDomain_iff_prime _).mpr <| by
    simpa only [span_singleton_prime W.polynomial_ne_zero, ← GCDMonoid.irreducible_iff_prime] using
      W.irreducible_polynomial
#align weierstrass_curve.coordinate_ring.is_domain WeierstrassCurve.CoordinateRing.instIsDomainCoordinateRing

instance instIsDomainCoordinateRing_of_Field {F : Type u} [Field F] (W : WeierstrassCurve F) :
    IsDomain W.CoordinateRing := by
  classical exact instIsDomainCoordinateRing W
#align weierstrass_curve.coordinate_ring.is_domain_of_field WeierstrassCurve.CoordinateRing.instIsDomainCoordinateRing_of_Field

variable (x : R) (y : R[X])

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The class of the element $X - x$ in $R[W]$ for some $x \in R$. -/
noncomputable def XClass : W.CoordinateRing :=
  mk W <| C <| X - C x
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.X_class WeierstrassCurve.CoordinateRing.XClass

lemma XClass_ne_zero [Nontrivial R] : XClass W x ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt W.monic_polynomial (C_ne_zero.mpr <| X_sub_C_ne_zero x) <|
    by rw [natDegree_polynomial, natDegree_C]; norm_num1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.X_class_ne_zero WeierstrassCurve.CoordinateRing.XClass_ne_zero

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The class of the element $Y - y(X)$ in $R[W]$ for some $y(X) \in R[X]$. -/
noncomputable def YClass : W.CoordinateRing :=
  mk W <| Y - C y
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.Y_class WeierstrassCurve.CoordinateRing.YClass

lemma YClass_ne_zero [Nontrivial R] : YClass W y ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt W.monic_polynomial (X_sub_C_ne_zero y) <|
    by rw [natDegree_polynomial, natDegree_X_sub_C]; norm_num1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.Y_class_ne_zero WeierstrassCurve.CoordinateRing.YClass_ne_zero

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The ideal $\langle X - x \rangle$ of $R[W]$ for some $x \in R$. -/
noncomputable def XIdeal : Ideal W.CoordinateRing :=
  span {XClass W x}
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.X_ideal WeierstrassCurve.CoordinateRing.XIdeal

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The ideal $\langle Y - y(X) \rangle$ of $R[W]$ for some $y(X) \in R[X]$. -/
noncomputable def YIdeal : Ideal W.CoordinateRing :=
  span {YClass W y}
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.Y_ideal WeierstrassCurve.CoordinateRing.YIdeal

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The ideal $\langle X - x, Y - y(X) \rangle$ of $R[W]$ for some $x \in R$ and $y(X) \in R[X]$. -/
noncomputable def XYIdeal (x : R) (y : R[X]) : Ideal W.CoordinateRing :=
  span {XClass W x, YClass W y}
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.XY_ideal WeierstrassCurve.CoordinateRing.XYIdeal

/-! ### The coordinate ring as an `R[X]`-algebra -/

noncomputable instance instAlgebraCoordinateRing : Algebra R[X] W.CoordinateRing :=
  Quotient.algebra R[X]
#align weierstrass_curve.coordinate_ring.algebra WeierstrassCurve.CoordinateRing.instAlgebraCoordinateRing

noncomputable instance instAlgebraCoordinateRing' : Algebra R W.CoordinateRing :=
  Quotient.algebra R
#align weierstrass_curve.coordinate_ring.algebra' WeierstrassCurve.CoordinateRing.instAlgebraCoordinateRing'

instance instIsScalarTowerCoordinateRing : IsScalarTower R R[X] W.CoordinateRing :=
  Quotient.isScalarTower R R[X] _
#align weierstrass_curve.coordinate_ring.is_scalar_tower WeierstrassCurve.CoordinateRing.instIsScalarTowerCoordinateRing

instance instSubsingletonCoordinateRing [Subsingleton R] : Subsingleton W.CoordinateRing :=
  Module.subsingleton R[X] _
#align weierstrass_curve.coordinate_ring.subsingleton WeierstrassCurve.CoordinateRing.instSubsingletonCoordinateRing

/-- The $R$-algebra isomorphism from $R[W] / \langle X - x, Y - y(X) \rangle$ to
$R[X, Y] / \langle X - x, Y - y(X) \rangle$ provided that $W(x, y(x)) = 0$. -/
noncomputable def quotientXYIdealEquiv' {x : R} {y : R[X]} (h : (W.polynomial.eval y).eval x = 0) :
    (W.CoordinateRing ⧸ XYIdeal W x y) ≃ₐ[R]
      R[X][Y] ⧸ (span {C (X - C x), Y - C y} : Ideal <| R[X][Y]) :=
  (quotientEquivAlgOfEq R <| by
    simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← map_span]; rfl).trans <|
    DoubleQuot.quotQuotEquivQuotOfLEₐ R <| (span_singleton_le_iff_mem _).mpr <|
      mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h

-- porting note: split into `quotientXYIdealEquiv'` to avoid deterministic timeout
/-- The $R$-algebra isomorphism from $R[W] / \langle X - x, Y - y(X) \rangle$ to $R$ obtained by
evaluation at $y(X)$ and at $x$ provided that $W(x, y(x)) = 0$. -/
noncomputable def quotientXYIdealEquiv {x : R} {y : R[X]} (h : (W.polynomial.eval y).eval x = 0) :
    (W.CoordinateRing ⧸ XYIdeal W x y) ≃ₐ[R] R :=
  (quotientXYIdealEquiv' W h).trans quotientSpanCXSubCXSubCAlgEquiv
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.quotient_XY_ideal_equiv WeierstrassCurve.CoordinateRing.quotientXYIdealEquiv

-- porting note: added `classical` explicitly
/-- The basis $\{1, Y\}$ for the coordinate ring $R[W]$ over the polynomial ring $R[X]$. -/
protected noncomputable def basis : Basis (Fin 2) R[X] W.CoordinateRing := by
  classical exact (subsingleton_or_nontrivial R).by_cases (fun _ => default) fun _ =>
    (AdjoinRoot.powerBasis' W.monic_polynomial).basis.reindex <| finCongr W.natDegree_polynomial
#align weierstrass_curve.coordinate_ring.basis WeierstrassCurve.CoordinateRing.basis

lemma basis_apply (n : Fin 2) :
    CoordinateRing.basis W n = (AdjoinRoot.powerBasis' W.monic_polynomial).gen ^ (n : ℕ) := by
  classical
  nontriviality R
  rw [CoordinateRing.basis, Or.by_cases, dif_neg <| not_subsingleton R, Basis.reindex_apply,
    PowerBasis.basis_eq_pow]
  rfl
#align weierstrass_curve.coordinate_ring.basis_apply WeierstrassCurve.CoordinateRing.basis_apply

-- porting note: added `@[simp]` in lieu of `coe_basis`
@[simp]
lemma basis_zero : CoordinateRing.basis W 0 = 1 := by
  simpa only [basis_apply] using pow_zero _
#align weierstrass_curve.coordinate_ring.basis_zero WeierstrassCurve.CoordinateRing.basis_zero

-- porting note: added `@[simp]` in lieu of `coe_basis`
@[simp]
lemma basis_one : CoordinateRing.basis W 1 = mk W Y := by
  simpa only [basis_apply] using pow_one _
#align weierstrass_curve.coordinate_ring.basis_one WeierstrassCurve.CoordinateRing.basis_one

-- porting note: removed `@[simp]` in lieu of `basis_zero` and `basis_one`
lemma coe_basis : (CoordinateRing.basis W : Fin 2 → W.CoordinateRing) = ![1, mk W Y] := by
  ext n
  fin_cases n
  exacts [basis_zero W, basis_one W]
#align weierstrass_curve.coordinate_ring.coe_basis WeierstrassCurve.CoordinateRing.coe_basis

variable {W}

lemma smul (x : R[X]) (y : W.CoordinateRing) : x • y = mk W (C x) * y :=
  (algebraMap_smul W.CoordinateRing x y).symm
#align weierstrass_curve.coordinate_ring.smul WeierstrassCurve.CoordinateRing.smul

lemma smul_basis_eq_zero {p q : R[X]} (hpq : p • (1 : W.CoordinateRing) + q • mk W Y = 0) :
    p = 0 ∧ q = 0 := by
  have h := Fintype.linearIndependent_iff.mp (CoordinateRing.basis W).linearIndependent ![p, q]
  erw [Fin.sum_univ_succ, basis_zero, Fin.sum_univ_one, basis_one] at h
  exact ⟨h hpq 0, h hpq 1⟩
#align weierstrass_curve.coordinate_ring.smul_basis_eq_zero WeierstrassCurve.CoordinateRing.smul_basis_eq_zero

lemma exists_smul_basis_eq (x : W.CoordinateRing) :
    ∃ p q : R[X], p • (1 : W.CoordinateRing) + q • mk W Y = x := by
  have h := (CoordinateRing.basis W).sum_equivFun x
  erw [Fin.sum_univ_succ, Fin.sum_univ_one, basis_zero, basis_one] at h
  exact ⟨_, _, h⟩
#align weierstrass_curve.coordinate_ring.exists_smul_basis_eq WeierstrassCurve.CoordinateRing.exists_smul_basis_eq

variable (W)

lemma smul_basis_mul_C (p q : R[X]) :
    (p • (1 : W.CoordinateRing) + q • mk W Y) * mk W (C y) =
      (p * y) • (1 : W.CoordinateRing) + (q * y) • mk W Y := by
  simp only [smul, _root_.map_mul]
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.smul_basis_mul_C WeierstrassCurve.CoordinateRing.smul_basis_mul_C

lemma smul_basis_mul_Y (p q : R[X]) :
    (p • (1 : W.CoordinateRing) + q • mk W Y) * mk W Y =
      (q * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) • (1 : W.CoordinateRing) +
        (p - q * (C W.a₁ * X + C W.a₃)) • mk W Y := by
  have Y_sq :
    mk W Y ^ 2 =
      mk W (C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) - C (C W.a₁ * X + C W.a₃) * Y) := by
    exact AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [WeierstrassCurve.polynomial]; ring1⟩
  simp_rw [smul, add_mul, mul_assoc, ← sq, Y_sq, C_sub, map_sub, C_mul, _root_.map_mul]
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.smul_basis_mul_Y WeierstrassCurve.CoordinateRing.smul_basis_mul_Y

/-! ### Norms on the coordinate ring -/

lemma norm_smul_basis (p q : R[X]) :
    Algebra.norm R[X] (p • (1 : W.CoordinateRing) + q • mk W Y) =
      p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
        q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
  simp_rw [Algebra.norm_eq_matrix_det <| CoordinateRing.basis W, Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, basis_zero, mul_one, basis_one, smul_basis_mul_Y, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← basis_zero, ← basis_one,
    Basis.repr_self_apply, if_pos, one_ne_zero, if_false, smul_eq_mul]
  ring1
#align weierstrass_curve.coordinate_ring.norm_smul_basis WeierstrassCurve.CoordinateRing.norm_smul_basis

lemma coe_norm_smul_basis (p q : R[X]) :
    ↑(Algebra.norm R[X] <| p • (1 : W.CoordinateRing) + q • mk W Y) =
      mk W ((C p + C q * X) * (C p + C q * (-Y - C (C W.a₁ * X + C W.a₃)))) :=
  AdjoinRoot.mk_eq_mk.mpr
    ⟨C q ^ 2, by simp only [norm_smul_basis, WeierstrassCurve.polynomial]; C_simp; ring1⟩
#align weierstrass_curve.coordinate_ring.coe_norm_smul_basis WeierstrassCurve.CoordinateRing.coe_norm_smul_basis

lemma degree_norm_smul_basis [IsDomain R] (p q : R[X]) :
    (Algebra.norm R[X] <| p • (1 : W.CoordinateRing) + q • mk W Y).degree =
      max (2 • p.degree) (2 • q.degree + 3) := by
  have hdp : (p ^ 2).degree = 2 • p.degree := degree_pow p 2
  have hdpq : (p * q * (C W.a₁ * X + C W.a₃)).degree ≤ p.degree + q.degree + 1 := by
    simpa only [degree_mul] using add_le_add_left degree_linear_le (p.degree + q.degree)
  have hdq :
      (q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)).degree = 2 • q.degree + 3 := by
    rw [degree_mul, degree_pow, ← one_mul <| X ^ 3, ← C_1, degree_cubic <| one_ne_zero' R]
  rw [norm_smul_basis]
  by_cases hp : p = 0
  · simpa only [hp, hdq, neg_zero, zero_sub, zero_mul, zero_pow zero_lt_two, degree_neg] using
      (max_bot_left _).symm
  · by_cases hq : q = 0
    · simpa only [hq, hdp, sub_zero, zero_mul, mul_zero, zero_pow zero_lt_two] using
        (max_bot_right _).symm
    · rw [← not_congr degree_eq_bot] at hp hq
      -- porting note: BUG `cases` tactic does not modify assumptions in `hp'` and `hq'`
      rcases hp' : p.degree with _ | dp -- `hp' : ` should be redundant
      · exact (hp hp').elim -- `hp'` should be `rfl`
      · rw [hp'] at hdp hdpq -- line should be redundant
        rcases hq' : q.degree with _ | dq -- `hq' : ` should be redundant
        · exact (hq hq').elim -- `hq'` should be `rfl`
        · rw [hq'] at hdpq hdq -- line should be redundant
          rcases le_or_lt dp (dq + 1) with hpq | hpq
          · convert (degree_sub_eq_right_of_degree_lt <| (degree_sub_le _ _).trans_lt <|
                      max_lt_iff.mpr ⟨hdp.trans_lt _, hdpq.trans_lt _⟩).trans
              (max_eq_right_of_lt _).symm <;> rw [hdq] <;>
              exact WithBot.coe_lt_coe.mpr <| by linarith only [hpq]
          · rw [sub_sub]
            convert (degree_sub_eq_left_of_degree_lt <| (degree_add_le _ _).trans_lt <|
                      max_lt_iff.mpr ⟨hdpq.trans_lt _, hdq.trans_lt _⟩).trans
              (max_eq_left_of_lt _).symm <;> rw [hdp] <;>
              exact WithBot.coe_lt_coe.mpr <| by linarith only [hpq]
#align weierstrass_curve.coordinate_ring.degree_norm_smul_basis WeierstrassCurve.CoordinateRing.degree_norm_smul_basis

variable {W}

lemma degree_norm_ne_one [IsDomain R] (x : W.CoordinateRing) :
    (Algebra.norm R[X] x).degree ≠ 1 := by
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩
  rw [degree_norm_smul_basis]
  rcases p.degree with (_ | _ | _ | _) <;> cases q.degree
  any_goals rintro (_ | _)
  -- porting note: replaced `dec_trivial` with `(cmp_eq_lt_iff _ _).mp rfl` but cannot be inlined
  apply (lt_max_of_lt_right _).ne'
  exact (cmp_eq_lt_iff _ _).mp rfl
#align weierstrass_curve.coordinate_ring.degree_norm_ne_one WeierstrassCurve.CoordinateRing.degree_norm_ne_one

lemma natDegree_norm_ne_one [IsDomain R] (x : W.CoordinateRing) :
    (Algebra.norm R[X] x).natDegree ≠ 1 :=
  mt (degree_eq_iff_natDegree_eq_of_pos zero_lt_one).mpr <| degree_norm_ne_one x
#align weierstrass_curve.coordinate_ring.nat_degree_norm_ne_one WeierstrassCurve.CoordinateRing.natDegree_norm_ne_one

end CoordinateRing

end Polynomial

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

variable [CommRing R] (E : EllipticCurve R)

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`. -/
def j : R :=
  ↑E.Δ'⁻¹ * E.c₄ ^ 3
#align elliptic_curve.j EllipticCurve.j

lemma twoTorsionPolynomial_disc_ne_zero [Nontrivial R] [Invertible (2 : R)] :
    E.twoTorsionPolynomial.disc ≠ 0 :=
  E.toWeierstrassCurve.twoTorsionPolynomial_disc_ne_zero <| E.coe_Δ' ▸ E.Δ'.isUnit
#align elliptic_curve.two_torsion_polynomial_disc_ne_zero EllipticCurve.twoTorsionPolynomial_disc_ne_zero

lemma nonsingular [Nontrivial R] {x y : R} (h : E.equation x y) : E.nonsingular x y :=
  E.nonsingular_of_Δ_ne_zero h <| E.coe_Δ' ▸ E.Δ'.ne_zero
#align elliptic_curve.nonsingular EllipticCurve.nonsingular

section ModelsWithJ

variable (R)

/-- When $3$ is invertible, $Y^2 + Y = X^3$ is an elliptic curve.
It is of $j$-invariant $0$ (see `EllipticCurve.ofJ0_j`). -/
def ofJ0 [Invertible (3 : R)] : EllipticCurve R :=
  have := invertibleNeg (3 ^ 3 : R)
  ⟨WeierstrassCurve.ofJ0 R, unitOfInvertible (-3 ^ 3 : R),
    by rw [val_unitOfInvertible, WeierstrassCurve.ofJ0_Δ R]; norm_num1⟩

lemma ofJ0_j [Invertible (3 : R)] : (ofJ0 R).j = 0 := by
  simp only [j, ofJ0, WeierstrassCurve.ofJ0_c₄]
  ring1

/-- When $2$ is invertible, $Y^2 = X^3 + X$ is an elliptic curve.
It is of $j$-invariant $1728$ (see `EllipticCurve.ofJ1728_j`). -/
def ofJ1728 [Invertible (2 : R)] : EllipticCurve R :=
  have := invertibleNeg (2 ^ 6 : R)
  ⟨WeierstrassCurve.ofJ1728 R, unitOfInvertible (-2 ^ 6 : R),
    by rw [val_unitOfInvertible, WeierstrassCurve.ofJ1728_Δ R]; norm_num1⟩

lemma ofJ1728_j [Invertible (2 : R)] : (ofJ1728 R).j = 1728 := by
  field_simp [j, ofJ1728, @val_unitOfInvertible _ _ _ <| invertibleNeg _,
    WeierstrassCurve.ofJ1728_c₄]
  norm_num1

variable {R}

/-- When $j$ and $j - 1728$ are both invertible,
$Y^2 + (j - 1728)XY = X^3 - 36(j - 1728)^3X - (j - 1728)^5$ is an elliptic curve.
It is of $j$-invariant $j$ (see `EllipticCurve.ofJ'_j`). -/
def ofJ' (j : R) [Invertible j] [Invertible (j - 1728)] : EllipticCurve R :=
  have := invertibleMul (j ^ 2) ((j - 1728) ^ 9)
  ⟨WeierstrassCurve.ofJ j, unitOfInvertible <| j ^ 2 * (j - 1728) ^ 9,
    (WeierstrassCurve.ofJ_Δ j).symm⟩

lemma ofJ'_j (j : R) [Invertible j] [Invertible (j - 1728)] : (ofJ' j).j = j := by
  field_simp [EllipticCurve.j, ofJ', @val_unitOfInvertible _ _ _ <| invertibleMul _ _,
    WeierstrassCurve.ofJ_c₄]
  ring1

variable {F : Type u} [Field F] (j : F)

private lemma two_or_three_ne_zero : (2 : F) ≠ 0 ∨ (3 : F) ≠ 0 :=
  ne_zero_or_ne_zero_of_nat_coprime (show Nat.Coprime 2 3 by norm_num1)

variable [DecidableEq F]

/-- For any element $j$ of a field $F$, there exists an elliptic curve over $F$
with $j$-invariant equal to $j$ (see `EllipticCurve.ofJ_j`).
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

lemma ofJ_ne_0_ne_1728 (h0 : j ≠ 0) (h1728 : j ≠ 1728) :
    ofJ j =
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

section VariableChange

/-! ### Variable changes -/

variable (C : WeierstrassCurve.VariableChange R)

-- porting note: was just `@[simps]`
/-- The elliptic curve over `R` induced by an admissible linear change of variables
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$.
When `R` is a field, any two Weierstrass equations isomorphic to `E` are related by this. -/
@[simps (config := { rhsMd := .default }) a₁ a₂ a₃ a₄ a₆ Δ' toWeierstrassCurve]
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
@[simps (config := { rhsMd := .default }) a₁ a₂ a₃ a₄ a₆ Δ' toWeierstrassCurve]
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

end EllipticCurve
