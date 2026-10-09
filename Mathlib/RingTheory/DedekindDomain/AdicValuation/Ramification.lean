/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.Valuation.Extension


/-!
# Ramification theory for adic valuations

- `A` is a Dedekind domain with field of fractions `K`.
- `B` is a Dedekind domain with field of fractions `L`.
- `L` is a field extension of `K`.
- `v` is a height one prime ideal of `A`.
- `w` is a height one prime ideal of `B` lying over `v`.

This file establishes the relationship between the adic valuation on `K` associated to `v` and the
adic valuation on `L` associated to `w`, in terms of the ramification index, and extends it to the
adic completions.

The algebra `K → L` extends to a continuous ring homomorphism
`completionMap K L v w : v.adicCompletion K →+* w.adicCompletion L`. Any algebra
`v.adicCompletion K → w.adicCompletion L` that is continuous and compatible with `K → L` is equal to
the one induced by `completionMap K L v w`. This is the analogue for finite places of
`Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances`, but does not assume that `K` and
`L` are number fields.

## Main definitions

- `IsDedekindDomain.HeightOneSpectrum.completionMap`: the ring homomorphism
  `v.adicCompletion K →+* w.adicCompletion L` extending `algebraMap K L`.
- `IsDedekindDomain.HeightOneSpectrum.algebraOfLiesOver`: the algebra induced by `completionMap`.

## Main results

- `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`: the valuation on `L` restricts to the
  `e`-th power of the valuation on `K`, where `e` is the ramification index of `w` over `v`.
- `IsDedekindDomain.HeightOneSpectrum.algebra_eq`: a continuous algebra
  `v.adicCompletion K → w.adicCompletion L` compatible with `K → L` is `algebraOfLiesOver`.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion_valuation_liesOver`: the analogue of
  `valuation_liesOver` for the adic completions.
- The valuation on `w.adicCompletion L` extends the valuation on `v.adicCompletion K`, so
  `w.adicCompletionIntegers L` is an algebra over `v.adicCompletionIntegers K`.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

open WithZero Ideal.IsDedekindDomain Valuation.IsRankOneDiscrete UniformSpace.Completion

section AKLB

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

theorem intValuation_liesOver (x : A) :
    v.intValuation x ^ (w.asIdeal.ramificationIdx A) =
      w.intValuation (algebraMap A B x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [(Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot).ne']
  rw [intValuation_eq_exp_neg_multiplicity v hx, intValuation_eq_exp_neg_multiplicity w (by simpa),
    ← Set.image_singleton, ← Ideal.map_span, exp_neg, exp_neg, inv_pow, ← exp_nsmul,
    Int.nsmul_eq_mul, inv_inj, exp_inj, ← Nat.cast_mul, Nat.cast_inj]
  refine multiplicity_eq_of_emultiplicity_eq_some ?_ |>.symm
  replace hx : Ideal.span {x} ≠ ⊥ := by simp [hx]
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  rw [emultiplicity_map_eq_ramificationIdx'_mul hx v.irreducible w.irreducible w.ne_bot,
    Nat.cast_mul, (FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]

theorem valuation_liesOver (x : K) :
    v.valuation K x ^ w.asIdeal.ramificationIdx A =
      w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation_of_algebraMap, div_pow, ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply A B L, intValuation_liesOver v w]

variable (K)

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
  let e := w.asIdeal.ramificationIdx A
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
  simp only [Units.val_mk0, Set.mem_ofPred_eq, true_and]
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
    (mod_cast (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot)) hx

/-- The ring homomorphism `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`,
when `w` lies over `v`. -/
noncomputable abbrev completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  ((adicCompletion.equiv L w).symm.toRingHom.comp <|
    mapRingHom _ (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
    (adicCompletion.equiv K v).toRingHom

theorem continuous_completionMap : Continuous (completionMap K L v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

@[simp]
theorem completionMap_coe (x : WithVal (v.valuation K)) :
    completionMap K L v w (x : v.adicCompletion K) =
      algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)) x :=
  adicCompletion.ext _ _ <| mapRingHom_coe _ x

@[instance_reducible]
noncomputable def algebraOfLiesOver : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap K L v w).toAlgebra

instance : letI := algebraOfLiesOver K L v w
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  let := algebraOfLiesOver K L v w
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, adicCompletion.algebraMap_eq_coe', completionMap_coe]
    apply adicCompletion.ext
    rw [algebraMap_adicCompletion_toCompletion, algebraMap_def]
    simp [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply]

instance : letI := algebraOfLiesOver K L v w
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) :=
  let := algebraOfLiesOver K L v w
  continuousSMul_of_algebraMap (v.adicCompletion K) (w.adicCompletion L)
    (continuous_completionMap K L v w)

variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem algebraMap_eq : algebraMap (v.adicCompletion K) (w.adicCompletion L) =
    completionMap K L v w := by
  refine DFunLike.ext' <| adicCompletion.ext_of_continuous K v (continuous_algebraMap _ _)
    (continuous_completionMap K L v w) fun k ↦ ?_
  rw [adicCompletion.algebraMap_coe]
  exact (completionMap_coe K L v w (WithVal.toVal _ k)).symm

theorem algebraMap_apply (x : v.adicCompletion K) :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) x = completionMap K L v w x := by
  rw [algebraMap_eq]

theorem algebra_eq : ‹_› = algebraOfLiesOver K L v w :=
  Algebra.algebra_ext _ _ (algebraMap_apply K L v w)

open WithZeroTopology in
theorem adicCompletion_valuation_liesOver (x : v.adicCompletion K) :
    adicCompletion.valuation K v x ^ w.asIdeal.ramificationIdx A =
      adicCompletion.valuation L w (algebraMap _ (w.adicCompletion L) x) := by
  induction x using adicCompletion.induction_on with
  | hp =>
    refine isClosed_eq ?_ ?_
    · exact (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)).pow _
    · exact (Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective L)).comp
        (continuous_algebraMap _ _)
  | ih k =>
    rw [algebraMap_eq]
    simpa [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply]
      using valuation_liesOver L v w _

instance : (adicCompletion.valuation K v).HasExtension (adicCompletion.valuation L w) where
  val_isEquiv_comap := by
    simp only [Valuation.isEquiv_iff_val_eq_one, Valuation.comap_apply,
      ← adicCompletion_valuation_liesOver]
    intro x
    exact ⟨by simp_all, fun h ↦ by
      grind [pow_eq_one_iff, Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot]⟩

noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  Valuation.HasExtension.instAlgebra_valuationSubring _ _

instance : IsLocalHom (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) :=
  Valuation.HasExtension.instIsLocalHomValuationSubring _ _

instance :
    IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) (w.adicCompletion L) :=
  Valuation.HasExtension.instIsScalarTower_valuationSubring' _ _

instance :
    IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L) :=
  Valuation.HasExtension.instIsScalarTower_valuationSubring _

end AKLB

end IsDedekindDomain.HeightOneSpectrum
