/-
Copyright (c) 2026 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Localization.Integral

/-!
# Minimal polynomials over a normalized GCD monoid

Let `R` be a normalized GCD monoid, `M` a submonoid of `R` and `S` a localization of `R` at `M`
(e.g. `R = ℤ`, `M = R⁰`, `S = ℚ`, or `R = k[X]`, `M = R⁰`, `S = k(X)`). For `x` in an
`S`-algebra `K`, `intMinpoly S M x` is the minimal polynomial of `x` over `R`: the polynomial
obtained from `minpoly S x` by clearing denominators (via
`IsLocalization.normalizedPrimPartIntegerNormalization`) and dividing out the content, so it is
primitive, normalized, and associated to `minpoly S x` after mapping to `S[X]`. As with
`minpoly`, it is `0` when `x` is not integral over `S`.

## Main definitions

* `intMinpoly S M x`: the minimal polynomial over `R` of `x : K`.

## Main results

* `intMinpoly_eq_zero_iff`: `intMinpoly S M x = 0` iff `x` is not integral over `S`.
* `intMinpoly_dvd`: `intMinpoly S M x`, mapped to `S[X]`, divides `minpoly S x`.
* `aeval_intMinpoly`: `x` is a root of `intMinpoly S M x`.
* `intMinpoly_isPrimitive`: `intMinpoly S M x` is primitive when `x` is integral over `S`.
* `intMinpoly_irreducible`: `intMinpoly S M x` is irreducible when `minpoly S x` is.
* `degree_intMinpoly`/`natDegree_intMinpoly`: same degree as `minpoly S x`.
-/

@[expose] public section

open Polynomial IsLocalization

variable {R K : Type*} [CommRing R] [NormalizedGCDMonoid R] (S : Type*) [CommRing S]
variable (M : Submonoid R) [Algebra R S] [IsLocalization M S] [Ring K]
variable [Algebra S K] {x : K}

/-- The minimal polynomial over `R` of an element `x` of a ring `K` that is an `S`-algebra,
where `S` is a localization of `R` at `M`: the polynomial in `R[X]` obtained from `minpoly S x`
by clearing denominators and then dividing out the content, so that the result is primitive and
normalized. If `x` is not integral over `S`, this is `0`. -/
noncomputable def intMinpoly (x : K) : R[X] :=
  normalizedPrimPartIntegerNormalization M (minpoly S x)

theorem intMinpoly_eq_zero (hx : ¬IsIntegral S x) : intMinpoly S M x = 0 := by
  rw [intMinpoly, minpoly.eq_zero hx, normalizedPrimPartIntegerNormalization_zero]

theorem intMinpoly_eq_zero_iff [Nontrivial S] : intMinpoly S M x = 0 ↔ ¬IsIntegral S x := by
  rw [intMinpoly, normalizedPrimPartIntegerNormalization_eq_zero_iff]
  exact ⟨fun h hx => minpoly.ne_zero hx h, minpoly.eq_zero⟩

theorem intMinpoly_ne_zero [Nontrivial S] (hx : IsIntegral S x) : intMinpoly S M x ≠ 0 :=
  fun h => (intMinpoly_eq_zero_iff S M).mp h hx

theorem intMinpoly_ne_zero_iff [Nontrivial S] : intMinpoly S M x ≠ 0 ↔ IsIntegral S x := by
  rw [Ne, intMinpoly_eq_zero_iff, not_not]

/-- `intMinpoly S M x`, mapped to `S[X]`, divides `minpoly S x`. -/
theorem intMinpoly_dvd : (intMinpoly S M x).map (algebraMap R S) ∣ minpoly S x :=
  normalizedPrimPartIntegerNormalization_dvd M (minpoly S x)

/-- `minpoly S x` is an `S`-multiple of `intMinpoly S M x` (mapped to `S[X]`). -/
theorem intMinpoly_exists_eq_C_mul_map :
    ∃ c : S, minpoly S x = C c * (intMinpoly S M x).map (algebraMap R S) :=
  normalizedPrimPartIntegerNormalization_dvd' M (minpoly S x)

/-- `x` is a root of `intMinpoly S M x`. -/
theorem aeval_intMinpoly [Nontrivial S] [IsDomain K] [FaithfulSMul S K] [Algebra R K]
    [IsScalarTower R S K] : Polynomial.aeval x (intMinpoly S M x) = 0 := by
  rw [← Polynomial.aeval_map_algebraMap S]
  obtain ⟨c, hc⟩ := intMinpoly_exists_eq_C_mul_map S M (x := x)
  by_cases hx : IsIntegral S x
  · have hc0 : c ≠ 0 := by
      rintro rfl
      simp only [Polynomial.C_0, zero_mul] at hc
      exact minpoly.ne_zero hx hc
    have h0 := minpoly.aeval S x
    rw [hc, map_mul, Polynomial.aeval_C] at h0
    have hcK : algebraMap S K c ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective S K).ne hc0
    exact (mul_eq_zero.mp h0).resolve_left hcK
  · simp [intMinpoly_eq_zero S M hx]

theorem intMinpoly_isPrimitive [Nontrivial S] (hx : IsIntegral S x) :
    (intMinpoly S M x).IsPrimitive :=
  normalizedPrimPartIntegerNormalization_isPrimitive M (minpoly.ne_zero hx)

theorem content_intMinpoly [Nontrivial S] (hx : IsIntegral S x) : (intMinpoly S M x).content = 1 :=
  (intMinpoly_isPrimitive S M hx).content_eq_one

@[simp]
theorem normalize_intMinpoly : normalize (intMinpoly S M x) = intMinpoly S M x :=
  normalize_normalizedPrimPartIntegerNormalization M (minpoly S x)

@[simp]
theorem natDegree_intMinpoly : (intMinpoly S M x).natDegree = (minpoly S x).natDegree :=
  natDegree_normalizedPrimPartIntegerNormalization M (minpoly S x)

@[simp]
theorem degree_intMinpoly : (intMinpoly S M x).degree = (minpoly S x).degree :=
  degree_normalizedPrimPartIntegerNormalization M (minpoly S x)

/-- The minimal polynomial over `R` of an element with irreducible minimal polynomial over `S`
is irreducible. Note that `minpoly S x` is irreducible, e.g., whenever `S` is a field and `x` is
integral over `S` (`minpoly.prime`). -/
theorem intMinpoly_irreducible (hdeg : (minpoly S x).natDegree ≠ 0)
    (hirr : Irreducible (minpoly S x)) : Irreducible (intMinpoly S M x) :=
  normalizedPrimPartIntegerNormalization_irreducible M hdeg hirr
