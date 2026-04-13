/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Order.Hom.Units
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology


/-!
# Ramification theory for valuations

- `A` is a Dedekind domain with field of fractions `K`.
- `B` is a Dedekind domain with field of fractions `L`.
- `L` is a field extension of `K`.
- `v` is a height one prime ideal of `A`.
- `w` is a height one prime ideal of `B` lying over `v`.

This file establishes the relationship between the adic valuation on `K` associated to `v` and the
adic valuation on `L` associated to `w`, in terms of the ramification index.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open WithZero Ideal.IsDedekindDomain Valuation.IsRankOneDiscrete

section AKLB

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

theorem intValuation_liesOver (x : A) :
    v.intValuation x ^ (v.asIdeal.ramificationIdx w.asIdeal) =
      w.intValuation (algebraMap A B x) := by
  rcases eq_or_ne x 0 with rfl | hx; · simp [ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  rw [intValuation_eq_coe_neg_multiplicity v hx, intValuation_eq_exp_neg_multiplicity w (by simpa),
    ← Set.image_singleton, ← Ideal.map_span, exp_neg, exp_neg, inv_pow, ← exp_nsmul,
    Int.nsmul_eq_mul, inv_inj, exp_inj, ← Nat.cast_mul, Nat.cast_inj]
  refine multiplicity_eq_of_emultiplicity_eq_some ?_ |>.symm
  replace hx : Ideal.span {x} ≠ ⊥ := by simp [hx]
  rw [emultiplicity_map_eq_ramificationIdx_mul hx v.irreducible w.irreducible w.ne_bot,
    Nat.cast_mul, (FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]

theorem valuation_liesOver (x : K) :
    v.valuation K x ^ v.asIdeal.ramificationIdx w.asIdeal =
      w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation_of_algebraMap, div_pow, ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply A B L, intValuation_liesOver v w]

variable (K)

attribute [-instance] ValuativeRel.isUniformAddGroup in
theorem uniformContinuous_algebraMap_liesOver :
    UniformContinuous (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero _)]
  intro γL _
  /-
  `ValueGroup₀ (w.valuation L)` <-------->  `ℤᵐ⁰` <--------> `ValueGroup₀ (v.valuation K)`
            ^                                                         ^
            |                                                         |
            |                                                         |
            v                                                         v
  `ValueGroup₀ (WithVal.valuation _)`             `ValueGroup₀ (WithVal.valuation _)`
            ^                                                         ^
            |                                                         |
            |                                                         |
            v                                                         v
  `γL : ValuativeRel.ValueGroupWithZero Lʷ`       `γK: ValuativeRel.ValueGroupWithZero Kᵛ`
  -/
  let e := v.asIdeal.ramificationIdx w.asIdeal
  -- push `γL` to `ℤᵐ⁰`
  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let σwV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (w.valuation L))
  let m : ℤᵐ⁰ := σw (σL (σwV γL))
  -- `ℤᵐ⁰` values in `K` exponentiate by `e` in `L` so take the `e`th root and pull back to `γK`
  let σvV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (v.valuation K))
  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := WithVal.valueGroupOrderIso₀ (v.valuation K)
  let γK := σvV.symm (σK.symm (σv.symm (exp (m.log / e))))
  have hγK : γK ≠ 0 := by simp [γK, EmbeddingLike.map_eq_zero_iff (f := σK.symm)]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_setOf_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σvV.lt_symm_apply, σK.lt_symm_apply, σv.lt_symm_apply,
    ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀,
    ← Valuation.restrict_def, WithVal.valueGroupOrderIso₀_restrict,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K),
    ← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σwV.strictMono.lt_iff_lt, ← σL.strictMono.lt_iff_lt,
    ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀, ← Valuation.restrict_def,
    WithVal.valueGroupOrderIso₀_restrict, ← σw.strictMono.lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L),
    WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, ← valuation_liesOver L v,
    ← log_lt_log (by simp_all) (by simp [EmbeddingLike.map_eq_zero_iff (f := σwV)]), log_pow,
    nsmul_eq_mul, mul_comm]
  exact Int.mul_lt_of_lt_ediv
    (mod_cast pos_of_ne_zero (ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx

end AKLB

end IsDedekindDomain.HeightOneSpectrum
