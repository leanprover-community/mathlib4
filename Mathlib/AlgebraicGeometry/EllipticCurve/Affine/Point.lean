/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Order.Compare
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Nonsingular points and the group law in affine coordinates

Let `W` be a Weierstrass curve over a field `F` given by a Weierstrass equation `W(X, Y) = 0` in
affine coordinates. The type of nonsingular points in affine coordinates is an inductive, consisting
of the unique point at infinity `𝓞` and nonsingular affine points `(x, y)`. It can be endowed with a
group law, with `𝓞` as the identity nonsingular point, which is uniquely determined by the formulae
in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.

With this description, there is an addition-preserving injection from the nonsingular points to the
ideal class group of the *affine coordinate ring* `F[W] := F[X, Y] / ⟨W(X, Y)⟩`. This is given by
mapping `𝓞` to the trivial ideal class and a nonsingular affine point `(x, y)` to the ideal class of
the invertible ideal `⟨X - x, Y - y⟩`. Proving that this is well-defined and preserves addition
reduces to equalities of ideals checked in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul`
and in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal` via explicit ideal computations.
Now `F[W]` is a free rank two `F[X]`-algebra with basis `{1, Y}`, so every element of `F[W]` is of
the form `p + qY` for some `p, q` in `F[X]`, and there is an algebra norm `N : F[W] → F[X]`.
Injectivity can then be shown by computing the degree of such a norm `N(p + qY)` in two different
ways, which is done in `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis` and in the
auxiliary lemmas in the proof of `WeierstrassCurve.Affine.Point.instAddCommGroup`.

This file defines the group law on nonsingular points in affine coordinates.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing`: the affine coordinate ring `F[W]`.
* `WeierstrassCurve.Affine.CoordinateRing.basis`: the power basis of `F[W]` over `F[X]`.
* `WeierstrassCurve.Affine.Point`: a nonsingular point in affine coordinates.
* `WeierstrassCurve.Affine.Point.neg`: the negation of a nonsingular point in affine coordinates.
* `WeierstrassCurve.Affine.Point.add`: the addition of a nonsingular point in affine coordinates.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing`: the affine coordinate ring
  of a Weierstrass curve is an integral domain.
* `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`: the degree of the norm of an
  element in the affine coordinate ring in terms of its power basis.
* `WeierstrassCurve.Affine.Point.instAddCommGroup`: the type of nonsingular points in affine
  coordinates forms an abelian group under addition.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
* https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.6/LIPIcs.ITP.2023.6.pdf

## Tags

elliptic curve, affine, point, group law, class group
-/

@[expose] public section

open FractionalIdeal (coeIdeal_mul)

open Ideal hiding map_mul

open Module Polynomial

open scoped nonZeroDivisors Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} {L : Type w} [CommRing R]
  [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] [Field L] {W' : Affine R}
  {W : Affine F}

namespace Affine

/-! ## The affine coordinate ring -/

variable (W') in
/-- The affine coordinate ring `R[W] := R[X, Y] / ⟨W(X, Y)⟩` of a Weierstrass curve `W`. -/
abbrev CoordinateRing : Type r :=
  AdjoinRoot W'.polynomial

variable (W') in
/-- The function field `R(W) := Frac(R[W])` of a Weierstrass curve `W`. -/
abbrev FunctionField : Type r :=
  FractionRing W'.CoordinateRing

namespace CoordinateRing

noncomputable instance : Algebra R W'.CoordinateRing := inferInstance

noncomputable instance : Algebra R[X] W'.CoordinateRing := inferInstance

instance : IsScalarTower R R[X] W'.CoordinateRing := inferInstance

instance [Subsingleton R] : Subsingleton W'.CoordinateRing :=
  Module.subsingleton R[X] _

variable (W') in
/-- The natural ring homomorphism mapping `R[X][Y]` to `R[W]`. -/
noncomputable abbrev mk : R[X][Y] →+* W'.CoordinateRing :=
  AdjoinRoot.mk W'.polynomial

open scoped Classical in
variable (W') in
/-- The power basis `{1, Y}` for `R[W]` over `R[X]`. -/
protected noncomputable def basis : Basis (Fin 2) R[X] W'.CoordinateRing :=
  (subsingleton_or_nontrivial R).by_cases (fun _ => default) fun _ =>
    (AdjoinRoot.powerBasis' monic_polynomial).basis.reindex <| finCongr natDegree_polynomial

lemma basis_apply (n : Fin 2) :
    CoordinateRing.basis W' n = (AdjoinRoot.powerBasis' monic_polynomial).gen ^ (n : ℕ) := by
  classical
  nontriviality R
  rw [CoordinateRing.basis, Or.by_cases, dif_neg <| not_subsingleton R, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast]

@[simp]
lemma basis_zero : CoordinateRing.basis W' 0 = 1 := by
  simpa only [basis_apply] using pow_zero _

@[simp]
lemma basis_one : CoordinateRing.basis W' 1 = mk W' Y := by
  simpa only [basis_apply] using pow_one _

lemma coe_basis : (CoordinateRing.basis W' : Fin 2 → W'.CoordinateRing) = ![1, mk W' Y] := by
  ext n
  fin_cases n
  exacts [basis_zero, basis_one]

lemma smul (x : R[X]) (y : W'.CoordinateRing) : x • y = mk W' (C x) * y :=
  (algebraMap_smul W'.CoordinateRing x y).symm

lemma smul_basis_eq_zero {p q : R[X]} (hpq : p • (1 : W'.CoordinateRing) + q • mk W' Y = 0) :
    p = 0 ∧ q = 0 := by
  have h := Fintype.linearIndependent_iff.mp (CoordinateRing.basis W').linearIndependent ![p, q]
  rw [Fin.sum_univ_succ, basis_zero, Fin.sum_univ_one, Fin.succ_zero_eq_one, basis_one] at h
  exact ⟨h hpq 0, h hpq 1⟩

lemma exists_smul_basis_eq (x : W'.CoordinateRing) :
    ∃ p q : R[X], p • (1 : W'.CoordinateRing) + q • mk W' Y = x := by
  have h := (CoordinateRing.basis W').sum_equivFun x
  rw [Fin.sum_univ_succ, Fin.sum_univ_one, basis_zero, Fin.succ_zero_eq_one, basis_one] at h
  exact ⟨_, _, h⟩

lemma smul_basis_mul_C (y : R[X]) (p q : R[X]) :
    (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' (C y) =
      (p * y) • (1 : W'.CoordinateRing) + (q * y) • mk W' Y := by
  simp only [smul, map_mul]
  ring1

lemma smul_basis_mul_Y (p q : R[X]) : (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' Y =
    (q * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)) • (1 : W'.CoordinateRing) +
      (p - q * (C W'.a₁ * X + C W'.a₃)) • mk W' Y := by
  have Y_sq : mk W' Y ^ 2 = mk W' (C (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) -
      C (C W'.a₁ * X + C W'.a₃) * Y) := AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [polynomial]; ring1⟩
  simp only [smul, add_mul, mul_assoc, ← sq, Y_sq, map_sub, map_mul]
  ring1

variable (W') in
/-- The ring homomorphism `R[W] →+* S[W.map f]` induced by a ring homomorphism `f : R →+* S`. -/
noncomputable def map (f : R →+* S) : W'.CoordinateRing →+* (W'.map f).CoordinateRing :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp <| mapRingHom f) (AdjoinRoot.root (W'.map f).polynomial)
    (by rw [← eval₂_map, ← map_polynomial, AdjoinRoot.eval₂_root])

lemma map_mk (f : R →+* S) (x : R[X][Y]) :
    map W' f (mk W' x) = mk (W'.map f) (x.map <| mapRingHom f) := by
  rw [map, AdjoinRoot.lift_mk, ← eval₂_map]
  exact AdjoinRoot.aeval_eq <| x.map <| mapRingHom f

protected lemma map_smul (f : R →+* S) (x : R[X]) (y : W'.CoordinateRing) :
    map W' f (x • y) = x.map f • map W' f y := by
  rw [smul, map_mul, map_mk, map_C, smul]
  rfl

lemma map_injective {f : R →+* S} (hf : Function.Injective f) : Function.Injective <| map W' f :=
  (injective_iff_map_eq_zero _).mpr fun y hy => by
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq y
    simp_rw [map_add, CoordinateRing.map_smul, map_one, map_mk, map_X] at hy
    obtain ⟨hp, hq⟩ := smul_basis_eq_zero hy
    rw [Polynomial.map_eq_zero_iff hf] at hp hq
    simp_rw [hp, hq, zero_smul, add_zero]

instance [IsDomain R] : IsDomain W'.CoordinateRing :=
  have : IsDomain (W'.map <| algebraMap R <| FractionRing R).CoordinateRing :=
    AdjoinRoot.isDomain_of_prime irreducible_polynomial.prime
  (map_injective <| IsFractionRing.injective R <| FractionRing R).isDomain

/-! ## Ideals in the affine coordinate ring -/

variable (W') in
/-- The class of the element `X - x` in `R[W]` for some `x` in `R`. -/
noncomputable def XClass (x : R) : W'.CoordinateRing :=
  mk W' <| C <| X - C x

lemma XClass_ne_zero [Nontrivial R] (x : R) : XClass W' x ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (C_ne_zero.mpr <| X_sub_C_ne_zero x) <|
    by rw [natDegree_polynomial, natDegree_C]; norm_num1

variable (W') in
/-- The class of the element `Y - y(X)` in `R[W]` for some `y(X)` in `R[X]`. -/
noncomputable def YClass (y : R[X]) : W'.CoordinateRing :=
  mk W' <| Y - C y

lemma YClass_ne_zero [Nontrivial R] (y : R[X]) : YClass W' y ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (X_sub_C_ne_zero y) <|
    by rw [natDegree_polynomial, natDegree_X_sub_C]; norm_num1

lemma C_addPolynomial (x y ℓ : R) : mk W' (C <| W'.addPolynomial x y ℓ) =
    mk W' ((Y - C (linePolynomial x y ℓ)) * (W'.negPolynomial - C (linePolynomial x y ℓ))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [W'.C_addPolynomial, add_sub_cancel_left, mul_one]⟩

lemma C_addPolynomial_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    mk W (C <| W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -(XClass W x₁ * XClass W x₂ * XClass W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) :=
  congr_arg (mk W) <| W.C_addPolynomial_slope h₁ h₂ hxy

variable (W') in
/-- The ideal `⟨X - x⟩` of `R[W]` for some `x` in `R`. -/
noncomputable def XIdeal (x : R) : Ideal W'.CoordinateRing :=
  .span {XClass W' x}

variable (W') in
/-- The ideal `⟨Y - y(X)⟩` of `R[W]` for some `y(X)` in `R[X]`. -/
noncomputable def YIdeal (y : R[X]) : Ideal W'.CoordinateRing :=
  .span {YClass W' y}

variable (W') in
/-- The ideal `⟨X - x, Y - y(X)⟩` of `R[W]` for some `x` in `R` and `y(X)` in `R[X]`. -/
noncomputable def XYIdeal (x : R) (y : R[X]) : Ideal W'.CoordinateRing :=
  .span {XClass W' x, YClass W' y}

/-- The `R`-algebra isomorphism from `R[W] / ⟨X - x, Y - y(X)⟩` to `R` obtained by evaluation at
some `y(X)` in `R[X]` and at some `x` in `R` provided that `W(x, y(x)) = 0`. -/
noncomputable def quotientXYIdealEquiv {x : R} {y : R[X]} (h : (W'.polynomial.eval y).eval x = 0) :
    (W'.CoordinateRing ⧸ XYIdeal W' x y) ≃ₐ[R] R :=
  ((quotientEquivAlgOfEq R <| by
      simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← map_span]; rfl).trans <|
        DoubleQuot.quotQuotEquivQuotOfLEₐ R <| (span_singleton_le_iff_mem _).mpr <|
          mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h).trans
    quotientSpanCXSubCXSubCAlgEquiv

lemma XYIdeal_add_eq (x₁ x₂ y₁ ℓ : R) : XYIdeal W' (W'.addX x₁ x₂ ℓ) (C <| W'.addY x₁ x₂ y₁ ℓ) =
    .span {mk W' <| W'.negPolynomial - C (linePolynomial x₁ y₁ ℓ)} ⊔
      XIdeal W' (W'.addX x₁ x₂ ℓ) := by
  simp only [XYIdeal, XIdeal, XClass, YClass, addY, negAddY, negY, negPolynomial, linePolynomial]
  rw [sub_sub <| -(Y : R[X][Y]), neg_sub_left (Y : R[X][Y]), map_neg, span_singleton_neg, sup_comm,
    ← span_insert, ← span_pair_add_left_mul _ _ <| mk W' <| C <| C <| W'.a₁ + ℓ, ← map_mul,
    ← map_add]
  congr 4
  C_simp
  ring1

lemma XYIdeal_eq₁ (x y ℓ : R) : XYIdeal W' x (C y) = XYIdeal W' x (linePolynomial x y ℓ) := by
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_left_mul _ _ <| mk W' <| C <| C <| -ℓ, ← map_mul, ← map_add]
  congr 4
  C_simp
  ring1

-- Non-terminal simp, used to be field_simp
set_option linter.flexible false in
-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
lemma XYIdeal_eq₂ [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    XYIdeal W x₂ (C y₂) = XYIdeal W x₂ (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have hy₂ : y₂ = (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂).eval x₂ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
      simp [linePolynomial]
    · simp [field, linePolynomial, slope_of_X_ne hx, sub_ne_zero_of_ne hx]
      ring1
  nth_rw 1 [hy₂]
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_left_mul _ _ <| mk W <| C <| C <| -W.slope x₁ x₂ y₁ y₂, ← map_mul, ← map_add]
  congr 4
  simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul]
  C_simp
  ring1

lemma XYIdeal_neg_mul {x y : F} (h : W.Nonsingular x y) :
    XYIdeal W x (C <| W.negY x y) * XYIdeal W x (C y) = XIdeal W x := by
  have Y_rw : (Y - C (C y)) * (Y - C (C <| W.negY x y)) -
      C (X - C x) * (C (X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)) - C (C W.a₁) * Y) =
        W.polynomial * 1 := by
    linear_combination (norm := (rw [negY, polynomial]; C_simp; ring1))
      congr_arg C (congr_arg C ((equation_iff ..).mp h.left).symm)
  simp_rw [XYIdeal, XClass, YClass, span_pair_mul_span_pair, mul_comm, ← map_mul,
    AdjoinRoot.mk_eq_mk.mpr ⟨1, Y_rw⟩, map_mul, span_insert, ← span_singleton_mul_span_singleton,
    ← Ideal.mul_sup, ← span_insert]
  convert mul_top (_ : Ideal W.CoordinateRing) using 2
  on_goal 2 => infer_instance
  simp_rw [← Set.image_singleton (f := mk W), ← Set.image_insert_eq, ← map_span]
  convert map_top (R := F[X][Y]) (mk W) using 1
  apply congr_arg
  simp_rw [eq_top_iff_one, mem_span_insert', mem_span_singleton']
  rcases ((nonsingular_iff' ..).mp h).right with hx | hy
  · let W_X := W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
    refine
      ⟨C <| C W_X⁻¹ * -(X + C (2 * x + W.a₂)), C <| C <| W_X⁻¹ * W.a₁, 0, C <| C <| W_X⁻¹ * -1, ?_⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [W_X, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hx]
    C_simp
    ring1
  · let W_Y := 2 * y + W.a₁ * x + W.a₃
    refine ⟨0, C <| C W_Y⁻¹, C <| C <| W_Y⁻¹ * -1, 0, ?_⟩
    rw [negY, ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hy]
    simp only [W_Y, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hy]
    C_simp
    ring1

lemma XYIdeal_mul_XYIdeal [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    XIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) * (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)) =
      YIdeal W (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) *
        XYIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)
          (C <| W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have sup_rw : ∀ a b c d : Ideal W.CoordinateRing, a ⊔ (b ⊔ (c ⊔ d)) = a ⊔ d ⊔ b ⊔ c :=
    fun _ _ c _ => by rw [← sup_assoc, sup_comm c, sup_sup_sup_comm, ← sup_assoc]
  rw [XYIdeal_add_eq, XIdeal, mul_comm, XYIdeal_eq₁ x₁ y₁ <| W.slope x₁ x₂ y₁ y₂, XYIdeal,
    XYIdeal_eq₂ h₁ h₂ hxy, XYIdeal, span_pair_mul_span_pair]
  simp_rw [span_insert, sup_rw, Ideal.sup_mul, span_singleton_mul_span_singleton]
  rw [← neg_eq_iff_eq_neg.mpr <| C_addPolynomial_slope h₁ h₂ hxy, span_singleton_neg,
    C_addPolynomial, map_mul, YClass]
  simp_rw [mul_comm <| XClass W x₁, mul_assoc, ← span_singleton_mul_span_singleton, ← Ideal.mul_sup]
  rw [span_singleton_mul_span_singleton, ← span_insert,
    ← span_pair_add_left_mul _ _ <| -(XClass W <| W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂), mul_neg,
    ← sub_eq_add_neg, ← sub_mul, ← map_sub <| mk W, sub_sub_sub_cancel_right, span_insert,
    ← span_singleton_mul_span_singleton, ← sup_rw, ← Ideal.sup_mul, ← Ideal.sup_mul]
  apply congr_arg (_ ∘ _)
  convert top_mul (_ : Ideal W.CoordinateRing)
  simp_rw [XClass, ← Set.image_singleton (f := mk W), ← map_span, ← Ideal.map_sup, eq_top_iff_one,
    mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective, ← span_insert, mem_span_insert',
    mem_span_singleton']
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
    let y := (y₁ - W.negY x₁ y₁) ^ 2
    replace hxy := pow_ne_zero 2 <| sub_ne_zero_of_ne hy
    refine ⟨1 + C (C <| y⁻¹ * 4) * W.polynomial,
      ⟨C <| C y⁻¹ * (C 4 * X ^ 2 + C (4 * x₁ + W.b₂) * X + C (4 * x₁ ^ 2 + W.b₂ * x₁ + 2 * W.b₄)),
        0, C (C y⁻¹) * (Y - W.negPolynomial), ?_⟩, by
      rw [map_add, map_one, map_mul <| mk W, AdjoinRoot.mk_self, mul_zero, add_zero]⟩
    rw [polynomial, negPolynomial, ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hxy]
    simp only [y, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hxy]
    linear_combination (norm := (rw [b₂, b₄, negY]; C_simp; ring1))
      -4 * congr_arg C (congr_arg C <| (equation_iff ..).mp h₁)
  · replace hx := sub_ne_zero_of_ne hx
    refine ⟨_, ⟨⟨C <| C (x₁ - x₂)⁻¹, C <| C <| (x₁ - x₂)⁻¹ * -1, 0, ?_⟩, map_one _⟩⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [← mul_assoc, mul_add, ← C_mul, mul_inv_cancel₀ hx]
    C_simp
    ring1

/-- The non-zero fractional ideal `⟨X - x, Y - y⟩` of `F(W)` for some `x` and `y` in `F`. -/
noncomputable def XYIdeal' {x y : F} (h : W.Nonsingular x y) :
    (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  Units.mkOfMulEqOne (XYIdeal W x (C y)) (XYIdeal W x (C <| W.negY x y) *
      (XIdeal W x : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)⁻¹) <| by
    rw [← mul_assoc, ← coeIdeal_mul, mul_comm <| XYIdeal W .., XYIdeal_neg_mul h, XIdeal,
      FractionalIdeal.coe_ideal_span_singleton_mul_inv W.FunctionField <| XClass_ne_zero x]

lemma XYIdeal'_eq {x y : F} (h : W.Nonsingular x y) :
    (XYIdeal' h : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = XYIdeal W x (C y) :=
  rfl

-- note: giving `W` to `XYIdeal'` explicitly hugely speeds up elaboration for some reason.
-- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Field.20.28FunctionField.20.3Fm.2E19.29/near/594011283
lemma mk_XYIdeal'_neg_mul {x y : F} (h : W.Nonsingular x y) :
    ClassGroup.mk (XYIdeal' (W := W) <| (nonsingular_neg ..).mpr h) *
      ClassGroup.mk (XYIdeal' (W := W) h) = 1 := by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_one_of_coe_ideal <| (coeIdeal_mul ..).symm.trans <|
    FractionalIdeal.coeIdeal_inj.mpr <| XYIdeal_neg_mul h).mpr ⟨_, XClass_ne_zero x, rfl⟩

-- note: giving `W` to `XYIdeal'` explicitly hugely speeds up elaboration for some reason.
-- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Field.20.28FunctionField.20.3Fm.2E19.29/near/594011283
lemma mk_XYIdeal'_mul_mk_XYIdeal' [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    ClassGroup.mk (XYIdeal' (W := W) h₁) * ClassGroup.mk (XYIdeal' (W := W) h₂) =
      ClassGroup.mk (XYIdeal' (W := W) <| nonsingular_add h₁ h₂ hxy) := by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_mk_of_coe_ideal (coeIdeal_mul ..).symm <| XYIdeal'_eq _).mpr
    ⟨_, _, XClass_ne_zero _, YClass_ne_zero _, XYIdeal_mul_XYIdeal h₁.left h₂.left hxy⟩

/-! ## Norms on the affine coordinate ring -/

lemma norm_smul_basis (p q : R[X]) : Algebra.norm R[X] (p • (1 : W'.CoordinateRing) + q • mk W' Y) =
    p ^ 2 - p * q * (C W'.a₁ * X + C W'.a₃) -
      q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) := by
  simp_rw [Algebra.norm_eq_matrix_det <| CoordinateRing.basis W', Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, basis_zero, mul_one, basis_one, smul_basis_mul_Y, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← basis_zero, ← basis_one,
    Basis.repr_self_apply, if_pos, one_ne_zero, if_false, smul_eq_mul]
  ring1

lemma coe_norm_smul_basis (p q : R[X]) : Algebra.norm R[X] (p • 1 + q • mk W' Y) =
    mk W' ((C p + C q * X) * (C p + C q * (-(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨C q ^ 2, by simp only [norm_smul_basis, polynomial]; C_simp; ring1⟩

lemma degree_norm_smul_basis [IsDomain R] (p q : R[X]) :
    (Algebra.norm R[X] <| p • 1 + q • mk W' Y).degree = max (2 • p.degree) (2 • q.degree + 3) := by
  have hdp : (p ^ 2).degree = 2 • p.degree := degree_pow p 2
  have hdpq : (p * q * (C W'.a₁ * X + C W'.a₃)).degree ≤ p.degree + q.degree + 1 := by
    grw [degree_mul, degree_mul, degree_linear_le]
  have hdq :
      (q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)).degree = 2 • q.degree + 3 := by
    rw [degree_mul, degree_pow, ← one_mul <| X ^ 3, ← C_1, degree_cubic <| one_ne_zero' R]
  rw [norm_smul_basis]
  by_cases hp : p = 0
  · simp only [hp, hdq, neg_zero, zero_sub, zero_mul, zero_pow two_ne_zero, degree_neg]
    exact (max_bot_left _).symm
  · by_cases hq : q = 0
    · simp only [hq, hdp, sub_zero, zero_mul, mul_zero, zero_pow two_ne_zero]
      exact (max_bot_right _).symm
    · rw [← not_congr degree_eq_bot] at hp hq
      -- Porting note: BUG `cases` tactic does not modify assumptions in `hp'` and `hq'`
      rcases hp' : p.degree with _ | dp -- `hp' : ` should be redundant
      · exact (hp hp').elim -- `hp'` should be `rfl`
      · rw [hp'] at hdp hdpq -- line should be redundant
        rcases hq' : q.degree with _ | dq -- `hq' : ` should be redundant
        · exact (hq hq').elim -- `hq'` should be `rfl`
        · rw [hq'] at hdpq hdq -- line should be redundant
          rcases le_or_gt dp (dq + 1) with hpq | hpq
          · convert (degree_sub_eq_right_of_degree_lt <| (degree_sub_le _ _).trans_lt <|
                      max_lt_iff.mpr ⟨hdp.trans_lt _, hdpq.trans_lt _⟩).trans
              (max_eq_right_of_lt _).symm <;> rw [hdq] <;>
                exact WithBot.coe_lt_coe.mpr <| by dsimp; linarith only [hpq]
          · rw [sub_sub]
            convert (degree_sub_eq_left_of_degree_lt <| (degree_add_le _ _).trans_lt <|
                      max_lt_iff.mpr ⟨hdpq.trans_lt _, hdq.trans_lt _⟩).trans
              (max_eq_left_of_lt _).symm <;> rw [hdp] <;>
                exact WithBot.coe_lt_coe.mpr <| by dsimp; linarith only [hpq]

lemma degree_norm_ne_one [IsDomain R] (x : W'.CoordinateRing) :
    (Algebra.norm R[X] x).degree ≠ 1 := by
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩
  rw [degree_norm_smul_basis]
  rcases p.degree with (_ | _ | _ | _) <;> cases q.degree
  any_goals rintro (_ | _)
  exact (lt_max_of_lt_right <| (cmp_eq_lt_iff ..).mp rfl).ne'

lemma natDegree_norm_ne_one [IsDomain R] (x : W'.CoordinateRing) :
    (Algebra.norm R[X] x).natDegree ≠ 1 :=
  degree_norm_ne_one x ∘ (degree_eq_iff_natDegree_eq_of_pos zero_lt_one).mpr

end CoordinateRing

/-! ## Nonsingular points in affine coordinates -/

variable (W') in
/-- A nonsingular point on a Weierstrass curve `W` in affine coordinates. This is either the unique
point at infinity `WeierstrassCurve.Affine.Point.zero` or a nonsingular affine point
`WeierstrassCurve.Affine.Point.some (x, y)` satisfying the Weierstrass equation of `W`. -/
inductive Point
  | zero
  | some (x y : R) (h : W'.Nonsingular x y)
deriving DecidableEq

/-- The equivalence between the nonsingular points on a Weierstrass curve `W` in affine coordinates
satisfying a predicate and the set of pairs `⟨x, y⟩` satisfying `W.Nonsingular x y` with zero. -/
def nonsingularPointEquivSubtype {p : W'.Point → Prop} (p0 : p .zero) : {P : W'.Point // p P} ≃
    WithZero {xy : R × R // ∃ h : W'.Nonsingular xy.fst xy.snd, p <| .some _ _ h} where
  toFun
    | ⟨.zero, _⟩ => none
    | ⟨.some _ _ h, ph⟩ => .some ⟨⟨_, _⟩, h, ph⟩
  invFun P := P.casesOn ⟨.zero, p0⟩ fun xy => ⟨.some _ _ xy.prop.choose, xy.prop.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

@[simp]
lemma nonsingularPointEquivSubtype_zero {p : W'.Point → Prop} (p0 : p .zero) :
    nonsingularPointEquivSubtype p0 ⟨.zero, p0⟩ = none :=
  rfl

@[simp]
lemma nonsingularPointEquivSubtype_some {x y : R} {h : W'.Nonsingular x y} {p : W'.Point → Prop}
    (p0 : p .zero) (ph : p <| .some _ _ h) :
    nonsingularPointEquivSubtype p0 ⟨.some _ _ h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩ :=
  rfl

@[simp]
lemma nonsingularPointEquivSubtype_symm_none {p : W'.Point → Prop} (p0 : p .zero) :
    (nonsingularPointEquivSubtype p0).symm none = ⟨.zero, p0⟩ :=
  rfl

@[simp]
lemma nonsingularPointEquivSubtype_symm_some {x y : R} {h : W'.Nonsingular x y}
    {p : W'.Point → Prop} (p0 : p .zero) (ph : p <| .some _ _ h) :
    (nonsingularPointEquivSubtype p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨.some _ _ h, ph⟩ :=
  rfl

variable (W') in
/-- The equivalence between the nonsingular points on a Weierstrass curve `W` in affine coordinates
and the set of pairs `⟨x, y⟩` satisfying `W.Nonsingular x y` with zero. -/
def nonsingularPointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Nonsingular xy.fst xy.snd} :=
  (Equiv.Set.univ W'.Point).symm.trans <| (nonsingularPointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]
lemma nonsingularPointEquiv_zero : nonsingularPointEquiv W' .zero = none :=
  rfl

@[simp]
lemma nonsingularPointEquiv_some {x y : R} (h : W'.Nonsingular x y) :
    W'.nonsingularPointEquiv (.some _ _ h) = .some ⟨⟨x, y⟩, h⟩ := by
  rfl

@[simp]
lemma nonsingularPointEquiv_symm_none : W'.nonsingularPointEquiv.symm none = .zero :=
  rfl

@[simp]
lemma nonsingularPointEquiv_symm_some {x y : R} (h : W'.Nonsingular x y) :
    W'.nonsingularPointEquiv.symm (.some ⟨⟨x, y⟩, h⟩) = .some _ _ h :=
  rfl

section IsElliptic

variable [Nontrivial R] [W'.IsElliptic]

/-- A point on an elliptic curve `W` over `R`. -/
def Point.mk {x y : R} (h : W'.Equation x y) : W'.Point :=
  .some _ _ <| equation_iff_nonsingular.mp h

/-- The equivalence between the points on an elliptic curve `W` in affine coordinates satisfying a
predicate and the set of pairs `⟨x, y⟩` satisfying `W.Equation x y` with zero. -/
def pointEquivSubtype {p : W'.Point → Prop} (p0 : p .zero) :
    {P : W'.Point // p P} ≃ WithZero {xy : R × R // ∃ h : W'.Equation xy.fst xy.snd, p <| .mk h} :=
  (nonsingularPointEquivSubtype p0).trans
    (Equiv.subtypeEquivProp <| by ext; simp [equation_iff_nonsingular, Point.mk]).optionCongr

@[simp]
lemma pointEquivSubtype_zero {p : W'.Point → Prop} (p0 : p .zero) :
    pointEquivSubtype p0 ⟨.zero, p0⟩ = none :=
  rfl

@[simp]
lemma pointEquivSubtype_some {x y : R} {h : W'.Equation x y} {p : W'.Point → Prop} (p0 : p .zero)
    (ph : p <| .mk h) : pointEquivSubtype p0 ⟨.mk h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩ :=
  rfl

@[simp]
lemma pointEquivSubtype_symm_none {p : W'.Point → Prop} (p0 : p .zero) :
    (pointEquivSubtype p0).symm none = ⟨.zero, p0⟩ :=
  rfl

@[simp]
lemma pointEquivSubtype_symm_some {x y : R} {h : W'.Equation x y} {p : W'.Point → Prop}
    (p0 : p .zero) (ph : p <| .mk h) :
    (pointEquivSubtype p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨.mk h, ph⟩ :=
  rfl

variable (W') in
/-- The equivalence between the rational points on an elliptic curve `E` and the set of pairs
`⟨x, y⟩` satisfying `E.Equation x y` with zero. -/
def pointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Equation xy.fst xy.snd} :=
  (Equiv.Set.univ W'.Point).symm.trans <| (pointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]
lemma pointEquiv_zero : W'.pointEquiv .zero = none :=
  rfl

@[simp]
lemma pointEquiv_some {x y : R} (h : W'.Equation x y) :
    pointEquiv W' (.mk h) = .some ⟨⟨x, y⟩, h⟩ := by
  rfl

@[simp]
lemma pointEquiv_symm_none : (pointEquiv W').symm none = .zero :=
  rfl

@[simp]
lemma pointEquiv_symm_some {x y : R} (h : W'.Equation x y) :
    (pointEquiv W').symm (.some ⟨⟨x, y⟩, h⟩) = .mk h :=
  rfl

end IsElliptic

namespace Point

/-! ## Group law in affine coordinates -/

instance : Inhabited W'.Point :=
  ⟨zero⟩

instance : Zero W'.Point :=
  ⟨zero⟩

lemma zero_def : 0 = (zero : W'.Point) :=
  rfl

lemma some_ne_zero {x y : R} (h : W'.Nonsingular x y) : some _ _ h ≠ 0 := by
  rintro (_ | _)

/-- The negation of a nonsingular point on a Weierstrass curve in affine coordinates.

Given a nonsingular point `P` in affine coordinates, use `-P` instead of `neg P`. -/
def neg : W'.Point → W'.Point
  | 0 => 0
  | some _ _ h => some _ _ <| (nonsingular_neg ..).mpr h

instance : Neg W'.Point :=
  ⟨neg⟩

lemma neg_def (P : W'.Point) : -P = P.neg :=
  rfl

@[simp]
lemma neg_zero : (-0 : W'.Point) = 0 :=
  rfl

@[simp]
lemma neg_some {x y : R} (h : W'.Nonsingular x y) :
    -some _ _ h = some _ _ ((nonsingular_neg ..).mpr h) :=
  rfl

instance : InvolutiveNeg W'.Point where
  neg_neg := by
    rintro (_ | _)
    · rfl
    · simp only [neg_some, negY_negY]

lemma X_eq_iff {x₁ y₁ x₂ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} :
    x₁ = x₂ ↔ some x₁ y₁ h₁ = some x₂ y₂ h₂ ∨ some x₁ y₁ h₁ = -some x₂ y₂ h₂ := by
  refine ⟨fun H ↦ ?_, fun H ↦ by grind [neg_some]⟩
  simp_rw [neg_some, some.injEq, ← and_or_left]
  exact ⟨H, Y_eq_of_X_eq h₁.1 h₂.1 H⟩

variable [DecidableEq F] [DecidableEq K] [DecidableEq L]

/-- The addition of two nonsingular points on a Weierstrass curve in affine coordinates.

Given two nonsingular points `P` and `Q` in affine coordinates, use `P + Q` instead of `add P Q`. -/
def add : W.Point → W.Point → W.Point
  | 0, P => P
  | P, 0 => P
  | some x₁ y₁ h₁, some x₂ y₂ h₂ =>
    if hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0 else some _ _ <| nonsingular_add h₁ h₂ hxy

instance : Add W.Point :=
  ⟨add⟩

instance : AddZeroClass W.Point where
  zero_add := by rintro (_ | _) <;> rfl
  add_zero := by rintro (_ | _) <;> rfl

lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

lemma add_some {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.Nonsingular x₁ y₁}
    {h₂ : W.Nonsingular x₂ y₂} :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ hxy) := by
  simp only [add_def, add, dif_neg hxy]

@[simp]
lemma add_of_Y_eq {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some _ _ h₁ + some _ _ h₂ = 0 := by
  simpa only [add_def, add] using dif_pos ⟨hx, hy⟩

-- Removing `@[simp]`, because `hy` causes a maximum recursion depth error in the simpNF linter.
lemma add_self_of_Y_eq {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ = W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = 0 :=
  add_of_Y_eq rfl hy

-- @[simp] -- Not a good simp lemma, since `hy` is not in simp normal form.
lemma add_of_Y_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ W.negY x₂ y₂) :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ fun hxy => hy hxy.right) :=
  add_some fun hxy => hy hxy.right

lemma add_of_Y_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ W.negY x₂ y₂) :
    some _ _ h₁ + some _ _ h₂ = -some _ _ (nonsingular_negAdd h₁ h₂ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

-- @[simp] -- Not a good simp lemma, since `hy` is not in simp normal form.
lemma add_self_of_Y_ne {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ ≠ W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = some _ _ (nonsingular_add h₁ h₁ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

lemma add_self_of_Y_ne' {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ ≠ W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = -some _ _ (nonsingular_negAdd h₁ h₁ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

@[simp]
lemma add_of_X_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ fun hxy => hx hxy.left) :=
  add_some fun hxy => hx hxy.left

lemma add_of_X_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    some _ _ h₁ + some _ _ h₂ = -some _ _ (nonsingular_negAdd h₁ h₂ fun hxy => hx hxy.left) :=
  add_of_X_ne hx

/-- The group homomorphism mapping a nonsingular affine point `(x, y)` of a Weierstrass curve `W` to
the class of the non-zero fractional ideal `⟨X - x, Y - y⟩` in the ideal class group of `F[W]`. -/
@[simps]
noncomputable def toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing) where
  toFun P := match P with
    | 0 => 0
    | some _ _ h => ClassGroup.mk <| CoordinateRing.XYIdeal' h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals simp only [← zero_def, zero_add, add_zero]
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · simp only [hxy.left, hxy.right, add_of_Y_eq rfl rfl]
      exact (CoordinateRing.mk_XYIdeal'_neg_mul h₂).symm
    · simp only [add_some hxy]
      exact (CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal' h₁ h₂ hxy).symm

lemma toClass_zero : toClass (0 : W.Point) = 0 :=
  rfl

-- note: giving `W` to `XYIdeal'` explicitly hugely speeds up elaboration for some reason.
-- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Field.20.28FunctionField.20.3Fm.2E19.29/near/594011283
lemma toClass_some {x y : F} (h : W.Nonsingular x y) :
    toClass (some _ _ h) = ClassGroup.mk (CoordinateRing.XYIdeal' (W := W) h) :=
  rfl

private lemma add_eq_zero (P Q : W.Point) : P + Q = 0 ↔ P = -Q := by
  rcases P, Q with ⟨_ | ⟨x₁, y₁, _⟩, _ | ⟨x₂, y₂, _⟩⟩
  any_goals rfl
  · rw [← zero_def, zero_add, eq_comm (a := 0), neg_eq_iff_eq_neg, neg_zero]
  · rw [neg_some, some.injEq]
    constructor
    · contrapose
      exact fun hxy => by simpa only [add_some hxy] using some_ne_zero _
    · exact fun ⟨hx, hy⟩ => add_of_Y_eq hx hy

lemma toClass_eq_zero (P : W.Point) : toClass P = 0 ↔ P = 0 := by
  constructor
  · intro hP
    rcases P with (_ | ⟨_, _, h, _⟩)
    · rfl
    · rcases (ClassGroup.mk_eq_one_of_coe_ideal <| by rfl).mp hP with ⟨p, h0, hp⟩
      apply (p.natDegree_norm_ne_one _).elim
      rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) h0,
        ← (quotientEquivAlgOfEq F hp).toLinearEquiv.finrank_eq,
        (CoordinateRing.quotientXYIdealEquiv h).toLinearEquiv.finrank_eq, Module.finrank_self]
  · exact congr_arg toClass

lemma toClass_injective : Function.Injective <| toClass (W := W) := by
  rintro (_ | ⟨_, _, h⟩) _ hP
  all_goals rw [← neg_inj, ← add_eq_zero, ← toClass_eq_zero, map_add, ← hP]
  · exact zero_add 0
  · exact CoordinateRing.mk_XYIdeal'_neg_mul h

instance : AddCommSemigroup W.Point where
  add_comm _ _ := toClass_injective <| by simp only [map_add, add_comm]
  add_assoc _ _ _ := toClass_injective <| by simp only [map_add, add_assoc]

instance : AddCommGroup W.Point where
  nsmul := nsmulBinRec
  nsmul_succ := nsmulBinRec_succ
  zsmul := zsmulRec nsmulBinRec
  zsmul_succ' := nsmulBinRec_succ
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel _ := by rw [add_eq_zero]

/-! ## Maps and base changes -/

variable [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] [Algebra R L] [Algebra S L] [IsScalarTower R S L] (f : F →ₐ[S] K)
  (g : K →ₐ[S] L)

/-- The group homomorphism on nonsingular points induced by an algebra homomorphism `f : F →ₐ[S] K`,
where `W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
noncomputable def map : (W'⁄F).Point →+ (W'⁄K).Point where
  toFun P := match P with
    | 0 => 0
    | some _ _ h => some _ _ <| (W'.baseChange_nonsingular f.injective ..).mpr h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (W'⁄F).negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right,
        add_of_Y_eq (congr_arg _ hxy.left) <| by rw [hxy.right, baseChange_negY]]
    · simpa only [add_some hxy, ← baseChange_addX, ← baseChange_addY, ← baseChange_slope] using
        (add_some fun h ↦ hxy ⟨f.injective h.1, f.injective (W'.baseChange_negY f .. ▸ h).2⟩).symm

lemma map_zero : map f (0 : (W'⁄F).Point) = 0 :=
  rfl

lemma map_some {x y : F} (h : (W'⁄F).Nonsingular x y) :
    map f (some _ _ h) = some _ _ ((W'.baseChange_nonsingular f.injective ..).mpr h) :=
  rfl

lemma map_id (P : (W'⁄F).Point) : map (Algebra.ofId F F) P = P := by
  cases P <;> rfl

lemma map_map (P : (W'⁄F).Point) : map g (map f P) = map (g.comp f) P := by
  cases P <;> rfl

lemma map_injective : Function.Injective <| map (W' := W') f := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [some.injEq] using ⟨f.injective (some.inj h).left, f.injective (some.inj h).right⟩

variable (F K) in
/-- The group homomorphism on nonsingular points induced by the base change from `F` to `K`, where
`W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
noncomputable abbrev baseChange [Algebra F K] [IsScalarTower R F K] :
    (W'⁄F).Point →+ (W'⁄K).Point :=
  map <| Algebra.ofId F K

lemma map_baseChange [Algebra F K] [IsScalarTower R F K] [Algebra F L] [IsScalarTower R F L]
    (f : K →ₐ[F] L) (P : (W'⁄F).Point) : map f (baseChange F K P) = baseChange F L P := by
  have : Subsingleton (F →ₐ[F] L) := inferInstance
  convert map_map (Algebra.ofId F K) f P

end Point

/-!
### The x-coordinate map to ℙ¹

We define the map from points on an affine Weierstrass curve over `R` to the projective line
by producing a coordinate vector in `Fin 2 → R` that represents the projective point.
-/

namespace Point

/-- This map sends a point `P` on a Weierstrass curve `W'` in affine coordinates
to a representative of its image on ℙ¹ under the x-coordinate map.
We take `![1, 0]` for the point at infinity and `![x, 1]`,
where `x` is the x-coordinate of `P`, for an affine point.

We define it in the general setting of a commutative base ring, even though the definition
of points in this setting is not really correct. For Weierstrass curves over fields, this
gives the correct notion. -/
noncomputable def xRep : W'.Point → Fin 2 → R
  | 0 => ![1, 0]
  | some x _ _ => ![x, 1]

@[simp]
lemma xRep_zero : (0 : W'.Point).xRep = ![1, 0] :=
  rfl

@[simp]
lemma xRep_some {x y : R} (h : W'.Nonsingular x y) : (some x y h).xRep = ![x, 1] :=
  rfl

lemma xRep_ne_zero [Nontrivial R] (P : W'.Point) : P.xRep ≠ 0 := by
  cases P <;> simp [xRep]

@[simp]
lemma xRep_neg (P : W'.Point) : (-P).xRep = P.xRep := by
  cases P <;> simp [← zero_def]

-- The following lemmas need a field as base ring.

lemma eq_or_eq_neg_of_xRep_eq_xRep {P Q : W.Point} (h : P.xRep = Q.xRep) : P = Q ∨ P = -Q := by
  match P, Q with
  | 0, 0 => exact .inl rfl
  | 0, some .. => simp [xRep] at h
  | some .., 0 => simp [xRep] at h
  | some x₁ .., some x₂ .. =>
    simp only [xRep, Matrix.vecCons_inj, and_true] at h
    exact X_eq_iff.mp h

lemma xRep_eq_xRep_iff {P Q : W.Point} : P.xRep = Q.xRep ↔ P = Q ∨ P = -Q := by
  refine ⟨eq_or_eq_neg_of_xRep_eq_xRep, fun H ↦ ?_⟩
  rcases H with rfl | rfl <;> simp

end Point

end Affine

end WeierstrassCurve
