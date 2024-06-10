/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.ClassGroup

/-!
# Group law on Weierstrass curves

This file proves that the nonsingular rational points on a Weierstrass curve forms an abelian group
under the geometric group law defined in `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F` given by a Weierstrass equation $W(X, Y) = 0$ in
affine coordinates. As in `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`, the set of nonsingular
rational points `W⟮F⟯` of `W` consist of the unique point at infinity $0$ and nonsingular affine
points $(x, y)$. With this description, there is an addition-preserving injection between `W⟮F⟯`
and the ideal class group of the coordinate ring $F[W] := F[X, Y] / \langle W(X, Y)\rangle$ of `W`.
This is defined by mapping the point at infinity $0$ to the trivial ideal class and an affine point
$(x, y)$ to the ideal class of the invertible fractional ideal $\langle X - x, Y - y\rangle$.
Proving that this is well-defined and preserves addition reduce to checking several equalities of
integral ideals, which is done in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul` and in
`WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal` via explicit ideal computations.
Now $F[W]$ is a free rank two $F[X]$-algebra with basis $\{1, Y\}$, so every element of $F[W]$ is
of the form $p + qY$ for some $p, q \in F[X]$, and there is an algebra norm $N : F[W] \to F[X]$.
Injectivity can then be shown by computing the degree of such a norm $N(p + qY)$ in two different
ways, which is done in `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis` and in the
auxiliary lemmas in the proof of `WeierstrassCurve.Affine.Point.instAddCommGroupPoint`.

## Main definitions

 * `WeierstrassCurve.Affine.CoordinateRing`: the coordinate ring `F[W]` of a Weierstrass curve `W`.
 * `WeierstrassCurve.Affine.CoordinateRing.basis`: the power basis of `F[W]` over `F[X]`.

## Main statements

 * `WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing`: the coordinate ring of a
    Weierstrass curve is an integral domain.
 * `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`: the degree of the norm of an
    element in the coordinate ring in terms of the power basis.
 * `WeierstrassCurve.Affine.Point.instAddCommGroupPoint`: the type of nonsingular rational points on
    a Weierstrass curve forms an abelian group under addition.

## References

https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.6/LIPIcs.ITP.2023.6.pdf

## Tags

elliptic curve, group law, class group
-/

open Ideal nonZeroDivisors Polynomial PolynomialPolynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow])

universe u

namespace WeierstrassCurve.Affine

/-! ## Weierstrass curves in affine coordinates -/

variable {R : Type u} [CommRing R] (W : Affine R)

-- Porting note: in Lean 3, this is a `def` under a `derive comm_ring` tag.
-- This generates a reducible instance of `comm_ring` for `coordinate_ring`. In certain
-- circumstances this might be extremely slow, because all instances in its definition are unified
-- exponentially many times. In this case, one solution is to manually add the local attribute
-- `local attribute [irreducible] coordinate_ring.comm_ring` to block this type-level unification.
-- In Lean 4, this is no longer an issue and is now an `abbrev`. See Zulip thread:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20class_group.2Emk
/-- The coordinate ring $R[W] := R[X, Y] / \langle W(X, Y) \rangle$ of `W`. -/
abbrev CoordinateRing : Type u :=
  AdjoinRoot W.polynomial
#align weierstrass_curve.coordinate_ring WeierstrassCurve.Affine.CoordinateRing

/-- The function field $R(W) := \mathrm{Frac}(R[W])$ of `W`. -/
abbrev FunctionField : Type u :=
  FractionRing W.CoordinateRing
#align weierstrass_curve.function_field WeierstrassCurve.Affine.FunctionField

namespace CoordinateRing

section Ring

/-! ### Ideals in the coordinate ring over a ring -/

instance instIsDomainCoordinateRing [IsDomain R] [NormalizedGCDMonoid R] :
    IsDomain W.CoordinateRing :=
  (Quotient.isDomain_iff_prime _).mpr <| by
    simpa only [span_singleton_prime W.polynomial_ne_zero, ← irreducible_iff_prime]
      using W.irreducible_polynomial
#align weierstrass_curve.coordinate_ring.is_domain WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing

instance instIsDomainCoordinateRing_of_Field {F : Type u} [Field F] (W : Affine F) :
    IsDomain W.CoordinateRing := by
  classical exact instIsDomainCoordinateRing W
#align weierstrass_curve.coordinate_ring.is_domain_of_field WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing_of_Field

-- Porting note: added the abbreviation `mk` for `AdjoinRoot.mk W.polynomial`
/-- An element of the coordinate ring `R[W]` of `W` over `R`. -/
noncomputable abbrev mk : R[X][Y] →+* W.CoordinateRing :=
  AdjoinRoot.mk W.polynomial

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
/-- The class of the element $X - x$ in $R[W]$ for some $x \in R$. -/
noncomputable def XClass (x : R) : W.CoordinateRing :=
  mk W <| C <| X - C x
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.X_class WeierstrassCurve.Affine.CoordinateRing.XClass

lemma XClass_ne_zero [Nontrivial R] (x : R) : XClass W x ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt W.monic_polynomial (C_ne_zero.mpr <| X_sub_C_ne_zero x) <|
    by rw [natDegree_polynomial, natDegree_C]; norm_num1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.X_class_ne_zero WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
/-- The class of the element $Y - y(X)$ in $R[W]$ for some $y(X) \in R[X]$. -/
noncomputable def YClass (y : R[X]) : W.CoordinateRing :=
  mk W <| Y - C y
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.Y_class WeierstrassCurve.Affine.CoordinateRing.YClass

lemma YClass_ne_zero [Nontrivial R] (y : R[X]) : YClass W y ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt W.monic_polynomial (X_sub_C_ne_zero y) <|
    by rw [natDegree_polynomial, natDegree_X_sub_C]; norm_num1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.Y_class_ne_zero WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero

lemma C_addPolynomial (x y L : R) : mk W (C <| W.addPolynomial x y L) =
    mk W ((Y - C (linePolynomial x y L)) * (W.negPolynomial - C (linePolynomial x y L))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [W.C_addPolynomial, add_sub_cancel_left, mul_one]⟩
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.C_add_polynomial WeierstrassCurve.Affine.CoordinateRing.C_addPolynomial

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
/-- The ideal $\langle X - x \rangle$ of $R[W]$ for some $x \in R$. -/
noncomputable def XIdeal (x : R) : Ideal W.CoordinateRing :=
  span {XClass W x}
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.X_ideal WeierstrassCurve.Affine.CoordinateRing.XIdeal

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
/-- The ideal $\langle Y - y(X) \rangle$ of $R[W]$ for some $y(X) \in R[X]$. -/
noncomputable def YIdeal (y : R[X]) : Ideal W.CoordinateRing :=
  span {YClass W y}
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.Y_ideal WeierstrassCurve.Affine.CoordinateRing.YIdeal

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
/-- The ideal $\langle X - x, Y - y(X) \rangle$ of $R[W]$ for some $x \in R$ and $y(X) \in R[X]$. -/
noncomputable def XYIdeal (x : R) (y : R[X]) : Ideal W.CoordinateRing :=
  span {XClass W x, YClass W y}
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.XY_ideal WeierstrassCurve.Affine.CoordinateRing.XYIdeal

lemma XYIdeal_eq₁ (x y L : R) : XYIdeal W x (C y) = XYIdeal W x (linePolynomial x y L) := by
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_mul_right <| mk W <| C <| C <| -L, ← _root_.map_mul, ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  C_simp
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_eq₁ WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq₁

lemma XYIdeal_add_eq (x₁ x₂ y₁ L : R) : XYIdeal W (W.addX x₁ x₂ L) (C <| W.addY x₁ x₂ y₁ L) =
    span {mk W <| W.negPolynomial - C (linePolynomial x₁ y₁ L)} ⊔ XIdeal W (W.addX x₁ x₂ L) := by
  simp only [XYIdeal, XIdeal, XClass, YClass, addY, negAddY, negY, negPolynomial, linePolynomial]
  rw [sub_sub <| -(Y : R[X][Y]), neg_sub_left (Y : R[X][Y]), map_neg, span_singleton_neg, sup_comm,
    ← span_insert, ← span_pair_add_mul_right <| mk W <| C <| C <| W.a₁ + L, ← _root_.map_mul,
    ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  C_simp
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_add_eq WeierstrassCurve.Affine.CoordinateRing.XYIdeal_add_eq

end Ring

section Field

/-! ### Ideals in the coordinate ring over a field -/

variable {F : Type u} [Field F] {W : Affine F}

lemma C_addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) : mk W (C <| W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -(XClass W x₁ * XClass W x₂ * XClass W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) := by
  simp only [addPolynomial_slope h₁ h₂ hxy, C_neg, mk, map_neg, neg_inj, _root_.map_mul]
  rfl
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.C_add_polynomial_slope WeierstrassCurve.Affine.CoordinateRing.C_addPolynomial_slope

lemma XYIdeal_eq₂ {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    XYIdeal W x₂ (C y₂) = XYIdeal W x₂ (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have hy₂ : y₂ = (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂).eval x₂ := by
    by_cases hx : x₁ = x₂
    · rcases hx, Y_eq_of_Y_ne h₁ h₂ hx <| hxy hx with ⟨rfl, rfl⟩
      field_simp [linePolynomial, sub_ne_zero_of_ne <| hxy rfl]
    · field_simp [linePolynomial, slope_of_X_ne hx, sub_ne_zero_of_ne hx]
      ring1
  nth_rw 1 [hy₂]
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_mul_right <| mk W <| C <| C <| -W.slope x₁ x₂ y₁ y₂, ← _root_.map_mul,
    ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  eval_simp
  C_simp
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_eq₂ WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq₂

lemma XYIdeal_neg_mul {x y : F} (h : W.Nonsingular x y) :
    XYIdeal W x (C <| W.negY x y) * XYIdeal W x (C y) = XIdeal W x := by
  have Y_rw : (Y - C (C y)) * (Y - C (C <| W.negY x y)) -
      C (X - C x) * (C (X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)) - C (C W.a₁) * Y) =
        W.polynomial * 1 := by
    linear_combination (norm := (rw [negY, polynomial]; C_simp; ring1))
      congr_arg C (congr_arg C ((W.equation_iff _ _).mp h.left).symm)
  simp_rw [XYIdeal, XClass, YClass, span_pair_mul_span_pair, mul_comm, ← _root_.map_mul,
    AdjoinRoot.mk_eq_mk.mpr ⟨1, Y_rw⟩, _root_.map_mul, span_insert,
    ← span_singleton_mul_span_singleton, ← Ideal.mul_sup, ← span_insert]
  convert mul_top (_ : Ideal W.CoordinateRing) using 2
  simp_rw [← @Set.image_singleton _ _ <| mk W, ← Set.image_insert_eq, ← map_span]
  convert map_top (R := F[X][Y]) (mk W) using 1
  apply congr_arg
  simp_rw [eq_top_iff_one, mem_span_insert', mem_span_singleton']
  rcases ((W.nonsingular_iff' _ _).mp h).right with hx | hy
  · let W_X := W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
    refine
      ⟨C <| C W_X⁻¹ * -(X + C (2 * x + W.a₂)), C <| C <| W_X⁻¹ * W.a₁, 0, C <| C <| W_X⁻¹ * -1, ?_⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hx]
    C_simp
    ring1
  · let W_Y := 2 * y + W.a₁ * x + W.a₃
    refine ⟨0, C <| C W_Y⁻¹, C <| C <| W_Y⁻¹ * -1, 0, ?_⟩
    rw [negY, ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hy]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hy]
    C_simp
    ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_neg_mul WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul

private lemma XYIdeal'_mul_inv {x y : F} (h : W.Nonsingular x y) :
    XYIdeal W x (C y) * (XYIdeal W x (C <| W.negY x y) *
        (XIdeal W x : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)⁻¹) = 1 := by
  rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul, mul_comm <| XYIdeal W _ _, XYIdeal_neg_mul h,
    XIdeal, FractionalIdeal.coe_ideal_span_singleton_mul_inv W.FunctionField <| XClass_ne_zero W x]

lemma XYIdeal_mul_XYIdeal {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    XIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) * (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)) =
      YIdeal W (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) *
        XYIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)
          (C <| W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have sup_rw : ∀ a b c d : Ideal W.CoordinateRing, a ⊔ (b ⊔ (c ⊔ d)) = a ⊔ d ⊔ b ⊔ c :=
    fun _ _ c _ => by rw [← sup_assoc, sup_comm c, sup_sup_sup_comm, ← sup_assoc]
  rw [XYIdeal_add_eq, XIdeal, mul_comm, XYIdeal_eq₁ W x₁ y₁ <| W.slope x₁ x₂ y₁ y₂, XYIdeal,
    XYIdeal_eq₂ h₁ h₂ hxy, XYIdeal, span_pair_mul_span_pair]
  simp_rw [span_insert, sup_rw, Ideal.sup_mul, span_singleton_mul_span_singleton]
  rw [← neg_eq_iff_eq_neg.mpr <| C_addPolynomial_slope h₁ h₂ hxy, span_singleton_neg,
    C_addPolynomial, _root_.map_mul, YClass]
  simp_rw [mul_comm <| XClass W x₁, mul_assoc, ← span_singleton_mul_span_singleton, ← Ideal.mul_sup]
  rw [span_singleton_mul_span_singleton, ← span_insert,
    ← span_pair_add_mul_right <| -(XClass W <| W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂), mul_neg,
    ← sub_eq_add_neg, ← sub_mul, ← map_sub <| mk W, sub_sub_sub_cancel_right, span_insert,
    ← span_singleton_mul_span_singleton, ← sup_rw, ← Ideal.sup_mul, ← Ideal.sup_mul]
  apply congr_arg (_ ∘ _)
  convert top_mul (_ : Ideal W.CoordinateRing)
  simp_rw [XClass, ← @Set.image_singleton _ _ <| mk W, ← map_span, ← Ideal.map_sup, eq_top_iff_one,
    mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective, ← span_insert, mem_span_insert',
    mem_span_singleton']
  by_cases hx : x₁ = x₂
  · rcases hx, Y_eq_of_Y_ne h₁ h₂ hx (hxy hx) with ⟨rfl, rfl⟩
    let y := (y₁ - W.negY x₁ y₁) ^ 2
    replace hxy := pow_ne_zero 2 <| sub_ne_zero_of_ne <| hxy rfl
    refine ⟨1 + C (C <| y⁻¹ * 4) * W.polynomial,
      ⟨C <| C y⁻¹ * (C 4 * X ^ 2 + C (4 * x₁ + W.b₂) * X + C (4 * x₁ ^ 2 + W.b₂ * x₁ + 2 * W.b₄)),
        0, C (C y⁻¹) * (Y - W.negPolynomial), ?_⟩, by
      rw [map_add, map_one, _root_.map_mul <| mk W, AdjoinRoot.mk_self, mul_zero, add_zero]⟩
    rw [polynomial, negPolynomial, ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hxy]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hxy]
    linear_combination (norm := (rw [b₂, b₄, negY]; C_simp; ring1))
      -4 * congr_arg C (congr_arg C <| (W.equation_iff _ _).mp h₁)
  · replace hx := sub_ne_zero_of_ne hx
    refine ⟨_, ⟨⟨C <| C (x₁ - x₂)⁻¹, C <| C <| (x₁ - x₂)⁻¹ * -1, 0, ?_⟩, map_one _⟩⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [← mul_assoc, mul_add, ← C_mul, mul_inv_cancel hx]
    C_simp
    ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_mul_XY_ideal WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
/-- The non-zero fractional ideal $\langle X - x, Y - y \rangle$ of $F(W)$ for some $x, y \in F$. -/
noncomputable def XYIdeal' {x y : F} (h : W.Nonsingular x y) :
    (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  Units.mkOfMulEqOne _ _ <| XYIdeal'_mul_inv h
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal' WeierstrassCurve.Affine.CoordinateRing.XYIdeal'

lemma XYIdeal'_eq {x y : F} (h : W.Nonsingular x y) :
    (XYIdeal' h : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = XYIdeal W x (C y) :=
  rfl
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal'_eq WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq

lemma mk_XYIdeal'_mul_mk_XYIdeal'_of_Yeq {x y : F} (h : W.Nonsingular x y) :
    ClassGroup.mk (XYIdeal' <| nonsingular_neg h) * ClassGroup.mk (XYIdeal' h) = 1 := by
  rw [← _root_.map_mul]
  exact
    (ClassGroup.mk_eq_one_of_coe_ideal <| by exact (FractionalIdeal.coeIdeal_mul _ _).symm.trans <|
      FractionalIdeal.coeIdeal_inj.mpr <| XYIdeal_neg_mul h).mpr ⟨_, XClass_ne_zero W _, rfl⟩
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.mk_XY_ideal'_mul_mk_XY_ideal'_of_Yeq WeierstrassCurve.Affine.CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal'_of_Yeq

lemma mk_XYIdeal'_mul_mk_XYIdeal' {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    ClassGroup.mk (XYIdeal' h₁) * ClassGroup.mk (XYIdeal' h₂) =
      ClassGroup.mk (XYIdeal' <| nonsingular_add h₁ h₂ hxy) := by
  rw [← _root_.map_mul]
  exact (ClassGroup.mk_eq_mk_of_coe_ideal (by exact (FractionalIdeal.coeIdeal_mul _ _).symm) <|
      XYIdeal'_eq _).mpr
    ⟨_, _, XClass_ne_zero W _, YClass_ne_zero W _, XYIdeal_mul_XYIdeal h₁.left h₂.left hxy⟩
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.mk_XY_ideal'_mul_mk_XY_ideal' WeierstrassCurve.Affine.CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal'

end Field

section Algebra

/-! ### The coordinate ring as an `R[X]`-algebra -/

noncomputable instance instAlgebraCoordinateRing : Algebra R[X] W.CoordinateRing :=
  Quotient.algebra R[X]
#align weierstrass_curve.coordinate_ring.algebra WeierstrassCurve.Affine.CoordinateRing.instAlgebraCoordinateRing

noncomputable instance instAlgebraCoordinateRing' : Algebra R W.CoordinateRing :=
  Quotient.algebra R
#align weierstrass_curve.coordinate_ring.algebra' WeierstrassCurve.Affine.CoordinateRing.instAlgebraCoordinateRing'

instance instIsScalarTowerCoordinateRing : IsScalarTower R R[X] W.CoordinateRing :=
  Quotient.isScalarTower R R[X] _
#align weierstrass_curve.coordinate_ring.is_scalar_tower WeierstrassCurve.Affine.CoordinateRing.instIsScalarTowerCoordinateRing

instance instSubsingletonCoordinateRing [Subsingleton R] : Subsingleton W.CoordinateRing :=
  Module.subsingleton R[X] _
#align weierstrass_curve.coordinate_ring.subsingleton WeierstrassCurve.Affine.CoordinateRing.instSubsingletonCoordinateRing

/-- The $R$-algebra isomorphism from $R[W] / \langle X - x, Y - y(X) \rangle$ to $R$ obtained by
evaluation at $y(X)$ and at $x$ provided that $W(x, y(x)) = 0$. -/
noncomputable def quotientXYIdealEquiv {x : R} {y : R[X]} (h : (W.polynomial.eval y).eval x = 0) :
    (W.CoordinateRing ⧸ XYIdeal W x y) ≃ₐ[R] R :=
  ((quotientEquivAlgOfEq R <| by
      simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← map_span]; rfl).trans <|
        DoubleQuot.quotQuotEquivQuotOfLEₐ R <| (span_singleton_le_iff_mem _).mpr <|
          mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h).trans
    quotientSpanCXSubCXSubCAlgEquiv
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.quotient_XY_ideal_equiv WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv

-- Porting note: added `classical` explicitly
/-- The basis $\{1, Y\}$ for the coordinate ring $R[W]$ over the polynomial ring $R[X]$. -/
protected noncomputable def basis : Basis (Fin 2) R[X] W.CoordinateRing := by
  classical exact (subsingleton_or_nontrivial R).by_cases (fun _ => default) fun _ =>
    (AdjoinRoot.powerBasis' W.monic_polynomial).basis.reindex <| finCongr W.natDegree_polynomial
#align weierstrass_curve.coordinate_ring.basis WeierstrassCurve.Affine.CoordinateRing.basis

lemma basis_apply (n : Fin 2) :
    CoordinateRing.basis W n = (AdjoinRoot.powerBasis' W.monic_polynomial).gen ^ (n : ℕ) := by
  classical
  nontriviality R
  rw [CoordinateRing.basis, Or.by_cases, dif_neg <| not_subsingleton R, Basis.reindex_apply,
    PowerBasis.basis_eq_pow]
  rfl
#align weierstrass_curve.coordinate_ring.basis_apply WeierstrassCurve.Affine.CoordinateRing.basis_apply

-- Porting note: added `@[simp]` in lieu of `coe_basis`
@[simp]
lemma basis_zero : CoordinateRing.basis W 0 = 1 := by
  simpa only [basis_apply] using pow_zero _
#align weierstrass_curve.coordinate_ring.basis_zero WeierstrassCurve.Affine.CoordinateRing.basis_zero

-- Porting note: added `@[simp]` in lieu of `coe_basis`
@[simp]
lemma basis_one : CoordinateRing.basis W 1 = mk W Y := by
  simpa only [basis_apply] using pow_one _
#align weierstrass_curve.coordinate_ring.basis_one WeierstrassCurve.Affine.CoordinateRing.basis_one

-- Porting note: removed `@[simp]` in lieu of `basis_zero` and `basis_one`
lemma coe_basis : (CoordinateRing.basis W : Fin 2 → W.CoordinateRing) = ![1, mk W Y] := by
  ext n
  fin_cases n
  exacts [basis_zero W, basis_one W]
#align weierstrass_curve.coordinate_ring.coe_basis WeierstrassCurve.Affine.CoordinateRing.coe_basis

variable {W}

lemma smul (x : R[X]) (y : W.CoordinateRing) : x • y = mk W (C x) * y :=
  (algebraMap_smul W.CoordinateRing x y).symm
#align weierstrass_curve.coordinate_ring.smul WeierstrassCurve.Affine.CoordinateRing.smul

lemma smul_basis_eq_zero {p q : R[X]} (hpq : p • (1 : W.CoordinateRing) + q • mk W Y = 0) :
    p = 0 ∧ q = 0 := by
  have h := Fintype.linearIndependent_iff.mp (CoordinateRing.basis W).linearIndependent ![p, q]
  erw [Fin.sum_univ_succ, basis_zero, Fin.sum_univ_one, basis_one] at h
  exact ⟨h hpq 0, h hpq 1⟩
#align weierstrass_curve.coordinate_ring.smul_basis_eq_zero WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero

lemma exists_smul_basis_eq (x : W.CoordinateRing) :
    ∃ p q : R[X], p • (1 : W.CoordinateRing) + q • mk W Y = x := by
  have h := (CoordinateRing.basis W).sum_equivFun x
  erw [Fin.sum_univ_succ, Fin.sum_univ_one, basis_zero, basis_one] at h
  exact ⟨_, _, h⟩
#align weierstrass_curve.coordinate_ring.exists_smul_basis_eq WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq

variable (W)

lemma smul_basis_mul_C (y : R[X]) (p q : R[X]) :
    (p • (1 : W.CoordinateRing) + q • mk W Y) * mk W (C y) =
      (p * y) • (1 : W.CoordinateRing) + (q * y) • mk W Y := by
  simp only [smul, _root_.map_mul]
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.smul_basis_mul_C WeierstrassCurve.Affine.CoordinateRing.smul_basis_mul_C

lemma smul_basis_mul_Y (p q : R[X]) :
    (p • (1 : W.CoordinateRing) + q • mk W Y) * mk W Y =
      (q * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) • (1 : W.CoordinateRing) +
        (p - q * (C W.a₁ * X + C W.a₃)) • mk W Y := by
  have Y_sq : mk W Y ^ 2 =
      mk W (C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) - C (C W.a₁ * X + C W.a₃) * Y) := by
    exact AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [polynomial]; ring1⟩
  simp_rw [smul, add_mul, mul_assoc, ← sq, Y_sq, C_sub, map_sub, C_mul, _root_.map_mul]
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.smul_basis_mul_Y WeierstrassCurve.Affine.CoordinateRing.smul_basis_mul_Y

end Algebra

section Norm

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
#align weierstrass_curve.coordinate_ring.norm_smul_basis WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis

lemma coe_norm_smul_basis (p q : R[X]) :
    Algebra.norm R[X] (p • (1 : W.CoordinateRing) + q • mk W Y) =
      mk W ((C p + C q * X) * (C p + C q * (-(Y : R[X][Y]) - C (C W.a₁ * X + C W.a₃)))) :=
  AdjoinRoot.mk_eq_mk.mpr
    ⟨C q ^ 2, by simp only [norm_smul_basis, polynomial]; C_simp; ring1⟩
#align weierstrass_curve.coordinate_ring.coe_norm_smul_basis WeierstrassCurve.Affine.CoordinateRing.coe_norm_smul_basis

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
  · simpa only [hp, hdq, neg_zero, zero_sub, zero_mul, zero_pow two_ne_zero, degree_neg] using
      (max_bot_left _).symm
  · by_cases hq : q = 0
    · simpa only [hq, hdp, sub_zero, zero_mul, mul_zero, zero_pow two_ne_zero] using
        (max_bot_right _).symm
    · rw [← not_congr degree_eq_bot] at hp hq
      -- Porting note: BUG `cases` tactic does not modify assumptions in `hp'` and `hq'`
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
                exact WithBot.coe_lt_coe.mpr <| by dsimp; linarith only [hpq]
          · rw [sub_sub]
            convert (degree_sub_eq_left_of_degree_lt <| (degree_add_le _ _).trans_lt <|
                      max_lt_iff.mpr ⟨hdpq.trans_lt _, hdq.trans_lt _⟩).trans
              (max_eq_left_of_lt _).symm <;> rw [hdp] <;>
                exact WithBot.coe_lt_coe.mpr <| by dsimp; linarith only [hpq]
#align weierstrass_curve.coordinate_ring.degree_norm_smul_basis WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis

variable {W}

lemma degree_norm_ne_one [IsDomain R] (x : W.CoordinateRing) :
    (Algebra.norm R[X] x).degree ≠ 1 := by
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩
  rw [degree_norm_smul_basis]
  rcases p.degree with (_ | _ | _ | _) <;> cases q.degree
  any_goals rintro (_ | _)
  -- Porting note: replaced `dec_trivial` with `by exact (cmp_eq_lt_iff ..).mp rfl`
  exact (lt_max_of_lt_right <| by exact (cmp_eq_lt_iff ..).mp rfl).ne'
#align weierstrass_curve.coordinate_ring.degree_norm_ne_one WeierstrassCurve.Affine.CoordinateRing.degree_norm_ne_one

lemma natDegree_norm_ne_one [IsDomain R] (x : W.CoordinateRing) :
    (Algebra.norm R[X] x).natDegree ≠ 1 :=
  degree_norm_ne_one x ∘ (degree_eq_iff_natDegree_eq_of_pos zero_lt_one).mpr
#align weierstrass_curve.coordinate_ring.nat_degree_norm_ne_one WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_ne_one

end Norm

end CoordinateRing

namespace Point

/-! ### The axioms for nonsingular rational points on a Weierstrass curve -/

variable {F : Type u} [Field F] {W : Affine F}

/-- The set function mapping an affine point $(x, y)$ of `W` to the class of the non-zero fractional
ideal $\langle X - x, Y - y \rangle$ of $F(W)$ in the class group of $F[W]$. -/
@[simp]
noncomputable def toClassFun : W.Point → Additive (ClassGroup W.CoordinateRing)
  | 0 => 0
  | some h => Additive.ofMul <| ClassGroup.mk <| CoordinateRing.XYIdeal' h
#align weierstrass_curve.point.to_class_fun WeierstrassCurve.Affine.Point.toClassFun

/-- The group homomorphism mapping an affine point $(x, y)$ of `W` to the class of the non-zero
fractional ideal $\langle X - x, Y - y \rangle$ of $F(W)$ in the class group of $F[W]$. -/
@[simps]
noncomputable def toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing) where
  toFun := toClassFun
  map_zero' := rfl
  map_add' := by
    rintro (_ | @⟨x₁, y₁, h₁⟩) (_ | @⟨x₂, y₂, h₂⟩)
    any_goals simp only [zero_def, toClassFun, _root_.zero_add, _root_.add_zero]
    by_cases hx : x₁ = x₂
    · by_cases hy : y₁ = W.negY x₂ y₂
      · substs hx hy
        rw [add_of_Y_eq rfl rfl]
        exact (CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal'_of_Yeq h₂).symm
      · rw [add_of_Y_ne hx hy]
        exact (CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal' h₁ h₂ fun _ => hy).symm
    · rw [add_of_X_ne hx]
      exact (CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal' h₁ h₂ fun h => (hx h).elim).symm
#align weierstrass_curve.point.to_class WeierstrassCurve.Affine.Point.toClass

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
lemma toClass_zero : toClass (0 : W.Point) = 0 :=
  rfl
#align weierstrass_curve.point.to_class_zero WeierstrassCurve.Affine.Point.toClass_zero

lemma toClass_some {x y : F} (h : W.Nonsingular x y) :
    toClass (some h) = ClassGroup.mk (CoordinateRing.XYIdeal' h) :=
  rfl
#align weierstrass_curve.point.to_class_some WeierstrassCurve.Affine.Point.toClass_some

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
lemma add_eq_zero (P Q : W.Point) : P + Q = 0 ↔ P = -Q := by
  rcases P, Q with ⟨_ | @⟨x₁, y₁, _⟩, _ | @⟨x₂, y₂, _⟩⟩
  any_goals rfl
  · rw [zero_def, zero_add, ← neg_eq_iff_eq_neg, neg_zero, eq_comm]
  · rw [neg_some, some.injEq]
    constructor
    · intro h
      by_cases hx : x₁ = x₂
      · by_cases hy : y₁ = W.negY x₂ y₂
        · exact ⟨hx, hy⟩
        · rw [add_of_Y_ne hx hy] at h
          contradiction
      · rw [add_of_X_ne hx] at h
        contradiction
    · exact fun ⟨hx, hy⟩ => add_of_Y_eq hx hy
#align weierstrass_curve.point.add_eq_zero WeierstrassCurve.Affine.Point.add_eq_zero

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
lemma add_left_neg (P : W.Point) : -P + P = 0 := by
  rw [add_eq_zero]
#align weierstrass_curve.point.add_left_neg WeierstrassCurve.Affine.Point.add_left_neg

-- Porting note (#10619): removed `@[simp]` to avoid a `simpNF` linter error
lemma neg_add_eq_zero (P Q : W.Point) : -P + Q = 0 ↔ P = Q := by
  rw [add_eq_zero, neg_inj]
#align weierstrass_curve.point.neg_add_eq_zero WeierstrassCurve.Affine.Point.neg_add_eq_zero

lemma toClass_eq_zero (P : W.Point) : toClass P = 0 ↔ P = 0 := by
  constructor
  · intro hP
    rcases P with (_ | @⟨_, _, ⟨h, _⟩⟩)
    · rfl
    · rcases (ClassGroup.mk_eq_one_of_coe_ideal <| by rfl).mp hP with ⟨p, h0, hp⟩
      apply (p.natDegree_norm_ne_one _).elim
      rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) h0,
        ← (quotientEquivAlgOfEq F hp).toLinearEquiv.finrank_eq,
        (CoordinateRing.quotientXYIdealEquiv W h).toLinearEquiv.finrank_eq,
        FiniteDimensional.finrank_self]
  · exact congr_arg toClass
#align weierstrass_curve.point.to_class_eq_zero WeierstrassCurve.Affine.Point.toClass_eq_zero

lemma toClass_injective : Function.Injective <| @toClass _ _ W := by
  rintro (_ | h) _ hP
  all_goals rw [← neg_add_eq_zero, ← toClass_eq_zero, map_add, ← hP]
  · exact zero_add 0
  · exact CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal'_of_Yeq h
#align weierstrass_curve.point.to_class_injective WeierstrassCurve.Affine.Point.toClass_injective

lemma add_comm (P Q : W.Point) : P + Q = Q + P :=
  toClass_injective <| by simp only [map_add, _root_.add_comm]
#align weierstrass_curve.point.add_comm WeierstrassCurve.Affine.Point.add_comm

lemma add_assoc (P Q R : W.Point) : P + Q + R = P + (Q + R) :=
  toClass_injective <| by simp only [map_add, _root_.add_assoc]
#align weierstrass_curve.point.add_assoc WeierstrassCurve.Affine.Point.add_assoc

noncomputable instance instAddCommGroupPoint : AddCommGroup W.Point where
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_add := zero_add
  add_zero := add_zero
  add_left_neg := add_left_neg
  add_comm := add_comm
  add_assoc := add_assoc

end Point

end WeierstrassCurve.Affine

namespace EllipticCurve.Affine

/-! ## Elliptic curves in affine coordinates -/

namespace Point

variable {R : Type} [Nontrivial R] [CommRing R] (E : EllipticCurve R)

/-- An affine point on an elliptic curve `E` over `R`. -/
def mk {x y : R} (h : E.toAffine.Equation x y) : E.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some <| nonsingular E h
#align elliptic_curve.point.mk EllipticCurve.Affine.Point.mk

end Point

end EllipticCurve.Affine
