/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.NumberField.FinitePlaces
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The L-function of an elliptic curve

In this file, we define the L-function of an elliptic curve.

## Main definitions

* `WeierstrassCurve.Lfunction`: the L-function of a minimal Weierstrass equation.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
-/

@[expose] public section

namespace WeierstrassCurve

open NumberField

variable {K : Type*} [Field K] [NumberField K]

open Classical Polynomial in
/-- The polynomial associated to an elliptic curve at a finite place `p`. -/
noncomputable def localPolynomial (W : WeierstrassCurve K)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℤ[X] :=
  letI R := p.adicCompletionIntegers K
  letI W' := (W.baseChange (p.adicCompletion K)).minimal R
  letI q : ℤ := p.asIdeal.absNorm
  letI a : ℤ := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
  if W'.IsGoodReduction R then 1 - C a * X + C q * X ^ 2
  else if W'.IsAdditiveReduction R then 1
  else if W'.IsSplitMultiplicativeReduction R then 1 - X
  else 1 + X

/-- The power series associated to an elliptic curve at a finite place `p`. -/
noncomputable def localPowerSeries (W : WeierstrassCurve K)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (W.localPolynomial p) 1

/-- The local Euler factor associated to an elliptic curve at a finite place `p`. -/
noncomputable def localEulerFactor (W : WeierstrassCurve K)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ArithmeticFunction ℤ :=
  .ofPowerSeries (Ideal.absNorm p.asIdeal) (W.localPowerSeries p)

-- todo: generalize to `HasFiniteQuotients`
instance {S : Type u_1} [CommRing S] [Nontrivial S] [IsDedekindDomain S] [Module.Free ℤ S]
  [Module.Finite ℤ S] [CharZero S] :
    Northcott (fun p : IsDedekindDomain.HeightOneSpectrum S ↦ p.asIdeal.absNorm) := by
  constructor
  intro B
  refine ((Ideal.finite_setOf_absNorm_le B).preimage
    (f := IsDedekindDomain.HeightOneSpectrum.asIdeal) (Function.Injective.injOn ?_)).subset ?_
  · exact fun _ _ ↦ IsDedekindDomain.HeightOneSpectrum.ext
  · grind

/-- The L-function of an elliptic curve is the product over places of `1 / fₚ(‖p‖⁻ˢ)` where:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` if `E` has good reduction at `p`,
* `fₚ = 1 - T` if `E` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `E` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `E` has additive reduction at `p`.
-/
noncomputable def LFunction (W : WeierstrassCurve K) : ArithmeticFunction ℤ :=
  ArithmeticFunction.eulerProduct W.localEulerFactor

/-- The L-series of an elliptic curve. -/
noncomputable def LSeries (W : WeierstrassCurve K) (s : ℂ) :=
  _root_.LSeries (fun n ↦ W.LFunction n) s

end WeierstrassCurve
