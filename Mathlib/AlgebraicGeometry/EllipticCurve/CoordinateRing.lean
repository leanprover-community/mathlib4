/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Coordinate ring of an elliptic curve

We show that the (affine) coordinate ring of an elliptic curve is a Dedekind domain.

See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Non-principal.20ideal.20in.20Dedekind.20domain/near/538662428
for a proof outline.
-/

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

abbrev Polynomial.toRatFunc {R} [CommRing R] : R[X] →+* FractionRing R[X] :=
  algebraMap ..

namespace WeierstrassCurve.Affine
/- A type synonym of WeierstrassCurve to give access to affine versions of the Weierstrass
polynomial and coordinate ring, etc. -/

variable {K : Type*} [Field K] (E : WeierstrassCurve.Affine K)

notation:10000 K"(X)" => FractionRing K[X]

/-- Another implementation of the function field of a Weierstrass curve, as `K(X)[Y]` modulo
the Weierstrass polynomial. -/
abbrev FunctionField' := AdjoinRoot <| E.polynomial.map (algebraMap K[X] K(X))
-- another implementation could be K(X) ⊗[K[X]] E.CoordinateRing

instance : Fact (Irreducible <| E.polynomial.map (algebraMap K[X] K(X))) := by
  sorry
  -- use Gauss lemma: Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map

attribute [local instance] Polynomial.algebra in
instance : Algebra E.CoordinateRing E.FunctionField' :=
  Ideal.Quotient.algebraQuotientOfLEComap <| by
    sorry

instance : IsScalarTower K[X] E.CoordinateRing E.FunctionField' := by
  sorry

instance : FiniteDimensional K(X) E.FunctionField' := by
  sorry

instance : FaithfulSMul E.CoordinateRing E.FunctionField' :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr <| by
    sorry
  /- Write an element in the coordinate ring K[E] as p • 1 + q • Y using
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq,
    and show its image can't be zero unless p = q = 0. -/

instance : IsFractionRing E.CoordinateRing E.FunctionField' := .of_field _ _ <| by
  sorry

-- An arbitrary element of the function field can be written in the form p(X) + q(X)Y
theorem FunctionField'.exists_smul_basis_eq (f : E.FunctionField') :
    ∃ p q : K(X), p • 1 + q • .mk _ X = f := by
  sorry
  -- mimic the proof of WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
  -- may need to develop some basis API

-- may be unnecessary for the final goal
theorem isIntegral_coordinateRing_iff {f : E.FunctionField'} :
    IsIntegral E.CoordinateRing f ↔ IsIntegral K[X] f := by
  sorry -- use that E.CoordinateRing is integral over K[X]

-- this deals with the q = 0 case
theorem isIntegral_algebraMap_iff {p : K(X)} :
    IsIntegral K[X] (algebraMap _ E.FunctionField' p) ↔ p ∈ toRatFunc.range := by
  sorry -- use that K[X] is integrally closed in K(X), and `isIntegral_algHom_iff`

variable (p q : K(X))

def comb : E.FunctionField' := p • 1 + q • .mk _ X

def trace : K(X) :=
  2 * p - q * (C E.a₁ * X + C E.a₃).toRatFunc

def norm : K(X) :=
  p ^ 2 - p * q * (C E.a₁ * X + C E.a₃).toRatFunc -
    q ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆).toRatFunc

-- If q ≠ 0, the minimal polynomial of f = p + qY is quadratic, given by Z² - Tr(f)Z + N(f).
theorem minpoly_smul_basis (hq : q ≠ 0) :
    minpoly K(X) (E.comb p q) = X ^ 2 - C (E.trace p q) * X + C (E.norm p q) := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · sorry
  · sorry
  · sorry

theorem trace_sq_sub_four_mul_norm :
    E.trace p q ^ 2 - 4 * E.norm p q = q ^ 2 * E.twoTorsionPolynomial.toPoly.toRatFunc := by
  sorry

variable (int : IsIntegral K[X] (E.comb p q))
include int

theorem trace_mem_of_isIntegral : E.trace p q ∈ toRatFunc.range := by
  sorry -- use minpoly.isIntegrallyClosed_eq_field_fractions'

theorem norm_mem_of_isIntegral : E.norm p q ∈ toRatFunc.range := by
  sorry -- ditto

variable [E.IsElliptic]

section IsUnit2

variable (h2 : IsUnit (2 : K))

-- `E.twoTorsionPolynomial` is nonzero (if char K ≠ 2) and separable since E is an elliptic curve.
theorem separable_twoTorsionPolynomial : E.twoTorsionPolynomial.toPoly.Separable := by
  sorry
  /- use `WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero`,
    `Cubic.discr_ne_zero_iff_roots_nodup`,
    `Polynomial.nodup_aroots_iff_of_splits` with `AlgebraicClosure K` -/
  -- need to convert between `l ≠ 2` and `IsUnit (2 : K)`

/- By `trace_sq_sub_four_mul_norm`, `q² * E.twoTorsionPolynomial` is in K[X],
but `E.twoTorsionPolynomial` is separable, hence squarefree, so q ∈ K[X].
Use  `Polynomial.Separable.squarefree` and
`UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`.
Maybe extract a lemma for `UniqueFactorizationMonoid`. -/
theorem right_mem_of_isIntegral : q ∈ toRatFunc.range := by
  sorry

/- Since q ∈ K[X], `norm_mem_of_isIntegral` shows that p satisfies a monic quadratic equation
with coefficients in K[X], so p is integral over K[X] and therefore in K[X]. -/
theorem left_mem_of_isIntegral : p ∈ toRatFunc.range := by
  sorry

end IsUnit2

section Char2

variable [CharP K 2]

-- TODO: fill in details for the char 2 case, see Zulip reference for now.
-- need to construct isomorphism of coordinate rings from variableChange.

theorem mem_of_isIntegral : p ∈ toRatFunc.range ∧ q ∈ toRatFunc.range := by
  sorry

end Char2

theorem comb_mem_of_isIntegral : E.comb p q ∈ (algebraMap E.CoordinateRing _).range := by
  sorry

omit int

/-- The affine coordinate ring of an elliptic curve is the integral closure of the
1-variable polynomial ring in the function field. -/
instance : IsIntegralClosure E.CoordinateRing K[X] E.FunctionField' := by
  sorry

instance : Algebra.IsSeparable K(X) E.FunctionField' := by
  sorry
  /- The generator Y is separable over K(X), since in characteristic 2,
    a₁ and a₃ cannot both vanish (otherwise the discriminant Δ vanishes),
    so the linear term of the minimal polynomial of Y does not vanish. -/

instance : IsDedekindDomain E.CoordinateRing :=
  IsIntegralClosure.isDedekindDomain K[X] K(X) E.FunctionField' _

end WeierstrassCurve.Affine
