/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Denominators of elements of an algebra

For an element `x` of an `R`-algebra `S`, with `R` a principal ideal ring, the **denominator**
`Algebra.denominator R x` is a generator of the colon ideal `(integralClosure R S).colon {x}`,
that is, of the ideal of scalars `r : R` clearing the denominators of `x`, in the sense that
`r • x` is integral over `R`. When `R = ℤ`, its absolute value is the natural-number denominator
`Algebra.natDenominator x`.

The definition needs no hypothesis on `x`, but it is only meaningful for `x` algebraic over `R`:
`IsAlgebraic.denominator_ne_zero` shows the denominator is then nonzero, whereas no nonzero
multiple of a transcendental element is integral, so that the colon ideal is trivial and the
denominator is `0`. See the `example` below, taking `x` to be the variable in `ℤ[X]`.

## Main definitions

* `Algebra.denominator`: the denominator of an element, over a principal ideal ring
* `Algebra.natDenominator`: the natural-number denominator of an element, over `ℤ`

## Main results

* `Algebra.denominator_dvd_iff`: `denominator R x` divides exactly the `r : R` with `r • x`
  integral over `R`
* `IsAlgebraic.denominator_ne_zero`: the denominator of an algebraic element is nonzero
-/

public section

variable (R : Type*) {S : Type*} [CommRing R]
variable [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
namespace Algebra

/-- The denominator of an element `x` of an `R`-algebra: a generator of the ideal of scalars
`r : R` such that `r • x` is integral over `R`. It is nonzero as soon as `x` is algebraic over
`R`; see `IsAlgebraic.denominator_ne_zero`. -/
noncomputable def denominator (x : S) : R :=
  Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x})

lemma denominator_def (x : S) :
    denominator R x =
      Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x}) := by
  rfl

variable {R}

theorem denominator_dvd_iff {r : R} {x : S} :
    denominator R x ∣ r ↔ IsIntegral R (r • x) := by
  rw [denominator_def, ← Submodule.IsPrincipal.mem_iff_generator_dvd,
    Submodule.mem_colon_singleton, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]

theorem isIntegral_denominator_smul (x : S) : IsIntegral R (denominator R x • x) :=
  denominator_dvd_iff.mp dvd_rfl

/-- The natural-number denominator of an element `x` of a ring: it is the absolute value of the
denominator of `x` over `ℤ`. -/
noncomputable def natDenominator (x : S) : ℕ :=
  (denominator ℤ x).natAbs

theorem natDenominator_def (x : S) : natDenominator x = (denominator ℤ x).natAbs := by
  rfl

theorem natDenominator_dvd_iff {n : ℕ} {x : S} :
    natDenominator x ∣ n ↔ IsIntegral ℤ (n • x) := by
  rw [natDenominator_def, ← Int.ofNat_dvd_right, denominator_dvd_iff, natCast_zsmul]

theorem isIntegral_natDenominator_smul (x : S) : IsIntegral ℤ (natDenominator x • x) :=
  natDenominator_dvd_iff.mp dvd_rfl

end Algebra

namespace IsAlgebraic

theorem denominator_ne_zero {x : S} (hx : IsAlgebraic R x) : Algebra.denominator R x ≠ 0 := by
  obtain ⟨r, hr0, hr⟩ := hx.exists_integral_multiple
  exact ne_zero_of_dvd_ne_zero hr0 (Algebra.denominator_dvd_iff.mpr hr)

theorem natDenominator_ne_zero {x : S} (hx : IsAlgebraic ℤ x) : Algebra.natDenominator x ≠ 0 := by
  rw [Algebra.natDenominator_def, Int.natAbs_ne_zero]
  exact hx.denominator_ne_zero

end IsAlgebraic

/- The algebraicity hypothesis in `IsAlgebraic.denominator_ne_zero` cannot be dropped: the
variable `X` of `ℤ[X]` is transcendental over `ℤ`, so no nonzero multiple of it is integral and
its denominator vanishes. -/
example : Algebra.denominator ℤ (Polynomial.X : Polynomial ℤ) = 0 := by
  by_contra h
  exact Polynomial.transcendental_X ℤ
    ((Algebra.isIntegral_denominator_smul _).isAlgebraic.of_smul
      (mem_nonZeroDivisors_of_ne_zero h))
