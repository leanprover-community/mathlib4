/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Ramification theory for valuations

- `A` is a Dedekind domain with field of fractions `K`.
- `B` is a Dedekind domain with field of fractions `L`.
- `L` is a field extension of `K`.
- `v` is a height one prime ideal of `A`.
- `w` is a height one prime ideal of `B` lying over `v`.

This file establishes the relationship between the adic valuation on `K` associated to `v` and the
adic valuation on `L` associated to `w`, in terms of ramification indices.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open WithZero Ideal.IsDedekindDomain

section AKLB

variable {A B K : Type*} (L : Type*) [CommRing A] [CommRing B] [Field K] [Algebra A B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A] [Algebra A L]
    [Algebra K L] [IsDedekindDomain B] [IsScalarTower A B L] [IsScalarTower A K L]
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)

theorem intValuation_liesOver [NoZeroSMulDivisors A B] (x : A) [w.asIdeal.LiesOver v.asIdeal] :
    v.intValuation x ^ (v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal) =
      w.intValuation (algebraMap A B x) := by
  rcases eq_or_ne x 0 with rfl | hx; · simp [ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  rw [intValuation_eq_coe_neg_multiplicity v hx, intValuation_eq_coe_neg_multiplicity w (by simpa),
    ← Set.image_singleton, ← Ideal.map_span, exp_neg, exp_neg, inv_pow, ← exp_nsmul,
    Int.nsmul_eq_mul, inv_inj, exp_inj, ← Nat.cast_mul, Nat.cast_inj]
  refine multiplicity_eq_of_emultiplicity_eq_some ?_ |>.symm
  replace hx : Ideal.span {x} ≠ ⊥ := by simp [hx]
  rw [emultiplicity_map_eq_ramificationIdx_mul hx v.irreducible w.irreducible w.ne_bot,
    Nat.cast_mul, (FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]

theorem valuation_liesOver [IsFractionRing B L] [NoZeroSMulDivisors A B]
    [w.asIdeal.LiesOver v.asIdeal] (x : WithVal (v.valuation K)) :
    v.valuation K x ^ v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal =
      w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [WithVal.algebraMap_apply', valuation_of_algebraMap, div_pow,
    ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    intValuation_liesOver v w]

variable (K) in
theorem uniformContinuous_algebraMap_liesOver [IsFractionRing B L] [NoZeroSMulDivisors A B]
    [w.asIdeal.LiesOver v.asIdeal] :
    UniformContinuous (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  use expEquiv ((WithZero.log γ) / v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal)
  simp only [adicValued_apply', coe_expEquiv_apply, Set.mem_setOf_eq, true_and]
  intro x hx
  rw [WithVal.algebraMap_apply, WithVal.algebraMap_apply', ← valuation_liesOver L]
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp [ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  · rw [← log_lt_iff_lt_exp (by simpa)] at hx
    rw [← log_lt_log (by simp_all) (by simp), log_pow, Int.nsmul_eq_mul, mul_comm]
    exact Int.mul_lt_of_lt_ediv
      (mod_cast Nat.pos_of_ne_zero (ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx

end AKLB

end IsDedekindDomain.HeightOneSpectrum
