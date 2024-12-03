/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.Data.Int.WithZero
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Finite places of number fields
This file defines finite places of a number field `K` as absolute values coming from an embedding
into a completion of `K` associated to a non-zero prime ideal of `𝓞 K`.

## Main Definitions and Results
* `NumberField.vadic_abv`: a `v`-adic absolute value on `K`.
* `NumberField.FinitePlace`: the type of finite places of a number field `K`.
* `NumberField.FinitePlace.mulSupport_Finite`: the `v`-adic absolute value of a non-zero element of
`K` is different from 1 for at most finitely many `v`.

## Tags
number field, places, finite places
-/

open Ideal IsDedekindDomain HeightOneSpectrum NumberField WithZeroMulInt

namespace NumberField

section absoluteValue

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The norm of a maximal ideal as an element of `ℝ≥0` is `> 1`  -/
lemma one_lt_norm : 1 < (absNorm v.asIdeal : NNReal) := by
  norm_cast
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero, absNorm_ne_zero_iff]
    exact (v.asIdeal.fintypeQuotientOfFreeOfNeBot v.ne_bot).finite
  omega

private lemma norm_ne_zero : (absNorm v.asIdeal : NNReal) ≠ 0 := ne_zero_of_lt (one_lt_norm v)

/-- The `v`-adic absolute value on `K` defined as the norm of `v` raised to negative `v`-adic
valuation.-/
noncomputable def vadic_abv : AbsoluteValue K ℝ where
  toFun := fun x ↦ toNNReal (norm_ne_zero v) (v.valuation x)
  map_mul' := fun _ _ ↦ by simp only [_root_.map_mul, NNReal.coe_mul]
  nonneg' := fun _ ↦ NNReal.zero_le_coe
  eq_zero' := fun _ ↦ by simp only [NNReal.coe_eq_zero, map_eq_zero]
  add_le' := by
    intro x y
    simp only
    norm_cast
    -- the triangle inequality is implied by the ultrametric one
    apply le_trans _ <| max_le_add_of_nonneg (zero_le ((toNNReal (norm_ne_zero v)) (v.valuation x)))
      (zero_le ((toNNReal (norm_ne_zero v)) (v.valuation y)))
    have h_mono := (toNNReal_strictMono (one_lt_norm v)).monotone
    rw [← h_mono.map_max] --max goes inside withZeroMultIntToNNReal
    exact h_mono (v.valuation.map_add x y)

theorem vadic_abv_def {x : K} : vadic_abv v x = toNNReal (norm_ne_zero v) (v.valuation x) := rfl

end absoluteValue

section FinitePlace
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The embedding of a number field inside its completion with respect to `v`. -/
def embedding : K →+* adicCompletion K v :=
  @UniformSpace.Completion.coeRingHom K _ v.adicValued.toUniformSpace _ _

noncomputable instance instRankOneValuedAdicCompletion :
    Valuation.RankOne (valuedAdicCompletion K v).v where
  hom := {
    toFun := toNNReal (norm_ne_zero v)
    map_zero' := rfl
    map_one' := rfl
    map_mul' := MonoidWithZeroHom.map_mul (toNNReal (norm_ne_zero v))
  }
  strictMono' := toNNReal_strictMono (one_lt_norm v)
  nontrivial' := by
    rcases Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot with ⟨x, hx1, hx2⟩
    use (x : K)
    rw [valuedAdicCompletion_eq_valuation' v (x : K)]
    constructor
    · simpa only [ne_eq, map_eq_zero, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rw [valuation_eq_intValuationDef, intValuation_lt_one_iff_dvd]
      exact dvd_span_singleton.mpr hx1

/-- The `v`-adic completion of `K` is a normed field. -/
noncomputable instance instNormedFieldValuedAdicCompletion : NormedField (adicCompletion K v) :=
  Valued.toNormedField (adicCompletion K v) (WithZero (Multiplicative ℤ))

/-- A finite place of a number field `K` is a place associated to an embedding into a completion
with respect to a maximal ideal. -/
def FinitePlace (K : Type*) [Field K] [NumberField K] := {w : AbsoluteValue K ℝ //
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (embedding v) = w}

/-- Return the finite place defined by a maximal ideal `v`. -/
noncomputable def FinitePlace.mk (v : HeightOneSpectrum (𝓞 K)) : FinitePlace K :=
  ⟨place (embedding v), ⟨v, rfl⟩⟩

/-- The norm of the image after the embedding associated to `v` is equal to the `v`-adic absolute
value. -/
theorem FinitePlace.norm_def (x : K) : ‖embedding v x‖ = vadic_abv v x := by
  simp only [NormedField.toNorm, instNormedFieldValuedAdicCompletion, Valued.toNormedField,
    instFieldAdicCompletion, Valued.norm, Valuation.RankOne.hom, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, embedding, UniformSpace.Completion.coeRingHom, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, Valued.valuedCompletion_apply, NNReal.coe_inj]
  rfl

open FinitePlace

/-- The `v`-adic norm of an integer is at most 1. -/
theorem norm_le_one (x : 𝓞 K) : ‖embedding v x‖ ≤ 1 := by
  rw [norm_def, vadic_abv_def, NNReal.coe_le_one, toNNReal_le_one_iff (one_lt_norm v)]
  exact valuation_le_one v x

/-- The `v`-adic norm of an integer is 1 if and only if it is not in the ideal. -/
theorem norm_eq_one_iff_not_mem (x : 𝓞 K) : ‖(embedding v) x‖ = 1 ↔ x ∉ v.asIdeal := by
  rw [norm_def, vadic_abv_def, NNReal.coe_eq_one, toNNReal_eq_one_iff (v.valuation (x : K))
    (norm_ne_zero v) (one_lt_norm v).ne', valuation_eq_intValuationDef,
    ← dvd_span_singleton, ← intValuation_lt_one_iff_dvd, not_lt]
  exact (intValuation_le_one v x).ge_iff_eq.symm

/-- The `v`-adic norm of an integer is less than 1 if and only if it is in the ideal. -/
theorem norm_lt_one_iff_mem (x : 𝓞 K) : ‖embedding v x‖ < 1 ↔ x ∈ v.asIdeal := by
  rw [norm_def, vadic_abv_def, NNReal.coe_lt_one, toNNReal_lt_one_iff (one_lt_norm v),
    valuation_eq_intValuationDef, intValuation_lt_one_iff_dvd]
  exact dvd_span_singleton

end FinitePlace

namespace FinitePlace
variable {K : Type*} [Field K] [NumberField K]

instance : FunLike (FinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective' _ _ h := Subtype.eq (AbsoluteValue.ext <| congr_fun h)

instance : MonoidWithZeroHomClass (FinitePlace K) K ℝ where
  map_mul w := w.1.map_mul
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

instance : NonnegHomClass (FinitePlace K) K ℝ where
  apply_nonneg w := w.1.nonneg

@[simp]
theorem apply (v : HeightOneSpectrum (𝓞 K)) (x : K) : mk v x =  ‖embedding v x‖ := rfl

/-- For a finite place `w`, return a maximal ideal `v` such that `w = finite_place v` . -/
noncomputable def maximal_ideal (w : FinitePlace K) : HeightOneSpectrum (𝓞 K) := w.2.choose

@[simp]
theorem mk_max_ideal (w : FinitePlace K) : mk (maximal_ideal w) = w := Subtype.ext w.2.choose_spec

@[simp]
theorem norm_embedding_eq (w : FinitePlace K) (x : K) :
    ‖embedding (maximal_ideal w) x‖ = w x := by
  have h : w x = (mk (maximal_ideal w)) x := by simp only [mk_max_ideal]
  rw [h]
  rfl

theorem eq_iff_eq (x : K) (r : ℝ) : (∀ w : FinitePlace K, w x = r) ↔
    ∀ v : HeightOneSpectrum (𝓞 K), ‖embedding v x‖ = r :=
  Set.forall_subtype_range_iff

theorem le_iff_le (x : K) (r : ℝ) : (∀ w : FinitePlace K, w x ≤ r) ↔
    ∀ v : HeightOneSpectrum (𝓞 K), ‖embedding v x‖ ≤ r :=
  Set.forall_subtype_range_iff

theorem pos_iff {w : FinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := AbsoluteValue.pos_iff w.1

@[simp]
theorem mk_eq_iff {v₁ v₂ : HeightOneSpectrum (𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂ := by
  refine ⟨?_, fun a ↦ by rw [a]⟩
  contrapose!
  intro h
  rw [DFunLike.ne_iff]
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h <| HeightOneSpectrum.ext_iff.mpr (IsMaximal.eq_of_le (isMaximal v₁) IsPrime.ne_top' H)
  use x
  simp only [apply]
  rw [← norm_lt_one_iff_mem ] at hx1
  rw [← norm_eq_one_iff_not_mem] at hx2
  linarith

theorem max_ideal_mk (v : HeightOneSpectrum (𝓞 K)) : maximal_ideal (mk v) = v := by
  rw [← mk_eq_iff, mk_max_ideal]

theorem mulSupport_Finite_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K ↦ w x).Finite := by
  have (w : FinitePlace K) : w x ≠ 1 ↔ w x < 1 := by
    have := norm_le_one w.maximal_ideal x
    rw [norm_embedding_eq] at this
    exact ne_iff_lt_iff_le.mpr this
  simp_rw [Function.mulSupport, this, ← norm_embedding_eq, norm_lt_one_iff_mem,
    ← Ideal.dvd_span_singleton]
  have h : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  have h_inj : Set.InjOn FinitePlace.maximal_ideal {w | w.maximal_ideal.asIdeal ∣ span {x}} := by
    apply Function.Injective.injOn
    intro w₁ w₂ h
    rw [← mk_max_ideal w₁, ← mk_max_ideal w₂]
    exact congrArg mk h
  apply Set.Finite.of_finite_image _ h_inj
  have h_subs : ((fun w : FinitePlace K ↦ w.maximal_ideal) ''
      {x_1 : FinitePlace K | x_1.maximal_ideal.asIdeal ∣ span {x}}) ⊆
      {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}} := by
    simp only [dvd_span_singleton, Set.image_subset_iff, Set.preimage_setOf_eq, subset_refl]
  exact Set.Finite.subset h h_subs

theorem mulSupport_Finite {x : K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K ↦ w x).Finite := by
  rcases IsFractionRing.div_surjective (A := 𝓞 K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, not_or,
    map_div₀]
  obtain ⟨ha, hb⟩ := h_x_nezero
  rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap]
  apply Set.Finite.subset (Set.Finite.union (mulSupport_Finite_int ha) (mulSupport_Finite_int hb))
  intro w
  contrapose!
  intro a_1
  simp_all only [Set.mem_union, Function.mem_mulSupport, ne_eq, not_or, Decidable.not_not,
    one_ne_zero, not_false_eq_true, div_self, not_true_eq_false]

end FinitePlace

end NumberField
