/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.Topology.Algebra.Algebra

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

open WithZero Ideal.IsDedekindDomain

section AKLB

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

theorem intValuation_liesOver (x : A) :
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

theorem valuation_liesOver (x : K) :
    v.valuation K x ^ v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal =
      w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation_of_algebraMap, div_pow, ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply A B L, intValuation_liesOver v w]

def _root_.IsDedekindDomain.HeightOneSpectrum.valueGroup_eq :
    MonoidWithZeroHom.valueGroup (v.valuation K) = ⊤ := by
  ext; simp [MonoidWithZeroHom.valueGroup, MonoidWithZeroHom.valueMonoid,
    (v.valuation_surjective K).range_eq]

variable (K) in
@[simps! apply symm_apply]
def _root_.IsDedekindDomain.HeightOneSpectrum.valueGroupEquiv :
    MonoidWithZeroHom.valueGroup (v.valuation K) ≃* ℤᵐ⁰ˣ where
  __ := (Equiv.setCongr (by simp [valueGroup_eq v])).trans
    (Equiv.subtypeUnivEquiv (Subgroup.mem_top))
  map_mul' _ _ := by simp [Equiv.setCongr, Equiv.subtypeEquivProp]

-- noncomputable example : MonoidWithZeroHom.valueGroup (v.valuation K) ≃ Multiplicative ℤ :=
--   (v.valueGroupEquiv K).trans (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ))

variable (K) in
@[simps!]
noncomputable
def _root_.IsDedekindDomain.HeightOneSpectrum.valueGroupOrderIso₀ :
    MonoidWithZeroHom.ValueGroup₀ (v.valuation K) ≃*o ℤᵐ⁰ where
  __ := WithZero.map' ((v.valueGroupEquiv K).trans WithZero.unitsWithZeroEquiv)
  invFun := WithZero.map' ((v.valueGroupEquiv K).trans WithZero.unitsWithZeroEquiv).symm.toMonoidHom
  left_inv := sorry
  right_inv := sorry
  map_le_map_iff' := sorry

open MonoidWithZeroHom ValueGroup₀

variable (K) in
lemma _root_.IsDedekindDomain.HeightOneSpectrum.valueGroupOrderIso₀_restrict (b : K) :
    v.valueGroupOrderIso₀ K ((v.valuation K).restrict b) = v.valuation K b := by
  simp [(v.valuation K).restrict_def, restrict₀_apply]
  by_cases hb : v.valuation K b = 0;
  · simp [hb]
  · simp [hb, Equiv.setCongr, Equiv.subtypeEquivProp]

variable (K) in
lemma _root_.IsDedekindDomain.HeightOneSpectrum.valueGroupOrderIso₀_symm_restrict (b : K) :
    (v.valueGroupOrderIso₀ K).symm (v.valuation K b) = (v.valuation K).restrict b := by
  simp [(v.valuation K).restrict_def, restrict₀_apply, valueGroupEquiv]
  by_cases hb : v.valuation K b = 0 <;> simp [hb]; sorry

lemma _root_.OrderMonoidIso.lt_symm_apply {α β : Type*} [Preorder α] [Preorder β] [Mul α] [Mul β]
    (e : α ≃*o β) {x : α} {y : β} : x < e.symm y ↔ e x < y :=
  e.toOrderIso.lt_symm_apply

lemma _root_.OrderMonoidIso.symm_apply_lt {α β : Type*} [Preorder α] [Preorder β] [Mul α] [Mul β]
    (e : α ≃*o β) {x : α} {y : β} : e.symm y < x ↔ y < e x :=
  e.toOrderIso.symm_apply_lt

variable (K) in
theorem uniformContinuous_algebraMap_liesOver :
    UniformContinuous (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  let eL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let ew := w.valueGroupOrderIso₀ L
  let ev := (v.valueGroupOrderIso₀ K)
  let eK := (WithVal.valueGroupOrderIso₀ (v.valuation K))
  let γ' := eK.symm (ev.symm
    (expEquiv ((WithZero.log (ew (eL γ))) / v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal)))
  have hγ' : γ' ≠ 0 := by simp [γ']
  use .mk0 _ hγ'
  simp only [Units.val_mk0, Set.mem_setOf_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp
  simp only [γ'] at hx
  simp only [coe_expEquiv_apply] at hx
  erw [← eL.strictMono.lt_iff_lt]
  rw [WithVal.valueGroupOrderIso₀_restrict]
  rw [← ew.strictMono.lt_iff_lt]
  rw [w.valueGroupOrderIso₀_restrict L]
  simp_rw [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply,
    ← valuation_liesOver L v w]
  rw [← log_lt_log (by simp_all) (by simp), log_pow, Int.nsmul_eq_mul, mul_comm]
  erw [eK.lt_symm_apply] at hx
  rw [ev.lt_symm_apply] at hx
  rw [WithVal.valueGroupOrderIso₀_restrict, v.valueGroupOrderIso₀_restrict K,
    ← log_lt_log (by simp_all) (by simp)] at hx
  exact Int.mul_lt_of_lt_ediv
    (mod_cast Nat.pos_of_ne_zero (ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx

variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

set_option backward.isDefEq.respectTransparency false in
open WithZeroTopology UniformSpace.Completion in
theorem valued_liesOver (x : v.adicCompletion K) :
    Valued.v x ^ v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal =
      Valued.v (algebraMap _ (w.adicCompletion L) x) := by
  induction x using induction_on with
  | hp =>
    refine isClosed_eq ?_ ?_
    · exact Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K) |>.pow _
    · exact (Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective L)).comp
        (continuous_algebraMap _ _)
  | ih a =>
    have := IsScalarTower.algebraMap_apply _ (v.adicCompletion K) (w.adicCompletion L) a
    simp only [algebraMap_def, WithVal.algebraMap_right_apply, WithVal.algebraMap_left_apply,
      Algebra.algebraMap_self, RingHom.id_apply] at this
    simp only [Valued.valuedCompletion_apply, ← this, WithVal.valued_toVal,
      ← valuation_liesOver L v]
    rw [WithVal.valued_toVal]

instance : (Valued.v : Valuation (v.adicCompletion K) _).HasExtension
      (Valued.v : Valuation (w.adicCompletion L) _) where
  val_isEquiv_comap := by
    simp only [Valuation.isEquiv_iff_val_eq_one, Valuation.comap_apply, ← valued_liesOver]
    intro x
    exact ⟨by simp_all, fun h ↦ by
      grind [pow_eq_one_iff, ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]⟩

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
