/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The t-adic closing of the orbit-product argument over `F(t)`

The orbit-product equation (`GMC2.OrbitProduct.prod_pow_card_group_eq`) instantiated at the Galois
group of `Φ(X) = X^M − t·R(X)` yields, in the base field `F(t) = RatFunc F`, an equation

  `Π ^ |G| = C_Φ ^ (|S|·|Stab|)`,

where (the small-root product identity) the small-root product is `Π = c·t` (`c ≠ 0`) and (Vieta)
`C_Φ = (−1)^d r_0/r_d ∈ F` is a nonzero *constant*. This module proves that such an equation is
impossible for `|G| ≥ 1`: a monomial `c·tᴺ` (`N ≥ 1`) is never a constant in `F(t)`. This is the
concrete valuation-free closing step — the `t`-adic contradiction realized by a degree comparison in
`F[t]` after pulling back along the injection `F[t] ↪ F(t)`. No splitting-field valuation is needed;
the only missing input is the small-root product identity (that `Π = c·t`), the unramified-Hensel
gap.
-/

open Polynomial

namespace GMC2.RatFuncClosing

variable {F : Type*} [Field F]

/-- In `F(t)`, a monomial `a·tᴺ` with `a ≠ 0` and `N ≥ 1` is never equal to a constant `b`. Pulling
back along the injective `F[t] ↪ F(t)` turns this into `C a * Xᴺ = C b` in `F[t]`, refuted by
degree. -/
theorem monomial_pow_ne_const (a b : F) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    RatFunc.C a * RatFunc.X ^ N ≠ RatFunc.C b := by
  intro h
  -- rewrite both sides as images of `F[t]` under the injective algebra map
  have hX : (RatFunc.X : RatFunc F) = algebraMap (Polynomial F) (RatFunc F) Polynomial.X :=
    (RatFunc.algebraMap_X).symm
  have hCa : (RatFunc.C a : RatFunc F) = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C a) :=
    (RatFunc.algebraMap_C a).symm
  have hCb : (RatFunc.C b : RatFunc F) = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C b) :=
    (RatFunc.algebraMap_C b).symm
  rw [hCa, hX, hCb, ← map_pow, ← map_mul] at h
  have hinj : Function.Injective (algebraMap (Polynomial F) (RatFunc F)) :=
    IsFractionRing.injective (Polynomial F) (RatFunc F)
  have hpoly : Polynomial.C a * Polynomial.X ^ N = Polynomial.C b := hinj h
  -- degree comparison: LHS has natDegree N, RHS natDegree 0
  have hdeg : (Polynomial.C a * Polynomial.X ^ N).natDegree = N := by
    rw [Polynomial.natDegree_C_mul ha, Polynomial.natDegree_X_pow]
  rw [hpoly, Polynomial.natDegree_C] at hdeg
  omega

end GMC2.RatFuncClosing

