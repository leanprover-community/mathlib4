/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Denominators of algebraic elements

For an element `x` of an `R`-algebra, the **denominator** is a generator of the colon ideal
`(integralClosure R S).colon {x}`. When `R = ℤ`, its absolute value is the natural-number
denominator `natDenominator x`.

## Main definitions

* `IsAlgebraic.denominator`: the denominator in a principal ideal ring
* `IsAlgebraic.natDenominator`: the natural-number denominator over `ℤ`
-/

@[expose] public section

namespace IsAlgebraic

variable (R : Type*) [CommRing R] [IsPrincipalIdealRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The denominator of an algebraic element. -/
noncomputable def denominator (x : S) : R :=
  Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x})

variable {R}

theorem denominator_dvd_iff {r : R} {x : S} :
    denominator R x ∣ r ↔ IsIntegral R (r • x) := by
  rw [denominator, ← Submodule.IsPrincipal.mem_iff_generator_dvd, Submodule.mem_colon_singleton,
    Subalgebra.mem_toSubmodule, mem_integralClosure_iff]

theorem isIntegral_denominator_smul (x : S) : IsIntegral R (denominator R x • x) :=
  denominator_dvd_iff.mp dvd_rfl

theorem denominator_ne_zero {x : S} (hx : IsAlgebraic R x) : denominator R x ≠ 0 := by
  obtain ⟨r, hr0, hr⟩ := IsAlgebraic.exists_integral_multiple hx
  exact ne_zero_of_dvd_ne_zero hr0 (denominator_dvd_iff.mpr hr)

/-- The natural-number denominator of an algebraic element over `ℤ`. -/
noncomputable def natDenominator (x : S) : ℕ :=
  (denominator ℤ x).natAbs

theorem natDenominator_dvd_iff {n : ℕ} {x : S} :
    natDenominator x ∣ n ↔ IsIntegral ℤ (n • x) := by
  rw [natDenominator, ← Int.ofNat_dvd_right, denominator_dvd_iff, natCast_zsmul]

theorem isIntegral_natDenominator_smul (x : S) : IsIntegral ℤ (natDenominator x • x) :=
  natDenominator_dvd_iff.mp dvd_rfl

theorem natDenominator_ne_zero {x : S} (hx : IsAlgebraic ℤ x) : natDenominator x ≠ 0 := by
  rw [natDenominator, Int.natAbs_ne_zero]
  exact denominator_ne_zero hx

end IsAlgebraic
