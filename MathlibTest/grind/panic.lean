import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.IsAdjoinRoot

/-!
From `v4.23.0-rc2` through to `nightly-2025-09-02`, `grind` panics here.

Once this is fixed in `grind`, we can keep this example as a regression test in Mathlib.
-/

open Polynomial UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

open Classical in
theorem normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span.extracted_1_3
  {R : Type} {S : Type} [CommRing R] [CommRing S] [Algebra R S] {x : S} {I : Ideal R}
  (hI : I.IsMaximal) {Q : R[X]}
  (hQ : Polynomial.map (Ideal.Quotient.mk I) Q ∈
    normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)))
  (a : S) (b : S) : b * (aeval x) Q + (a - (aeval x) Q * b) = a := by grind
