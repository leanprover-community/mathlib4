/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.Archimedean.Submonoid
public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Data.Int.WithZero
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Valuation.Archimedean
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Finite places of number fields
This file defines finite places of a number field `K` as absolute values coming from an embedding
into a completion of `K` associated to a non-zero prime ideal of `𝓞 K`.

## Main Definitions and Results
* `NumberField.adicAbv`: a `v`-adic absolute value on `K`.
* `NumberField.FinitePlace`: the type of finite places of a number field `K`.
* `NumberField.FinitePlace.embedding`: the canonical embedding of a number field `K` to the
  `v`-adic completion `v.adicCompletion K` of `K`, where `v` is a non-zero prime ideal of `𝓞 K`
* `NumberField.FinitePlace.norm_def`: the norm of `embedding v x` is the same as the `v`-adic
  absolute value of `x`. See also `NumberField.FinitePlace.norm_def'` and
  `NumberField.FinitePlace.norm_def_int` for versions where the `v`-adic absolute value is
  unfolded.
* `NumberField.FinitePlace.hasFiniteMulSupport`: the `v`-adic absolute value of a non-zero element
  of `K` is different from 1 for at most finitely many `v`.
*  The valuation subrings of the field at the `v`-valuation and it's adic completion are
   discrete valuation rings.

## Tags
number field, places, finite places
-/

@[expose] public section

open Ideal IsDedekindDomain HeightOneSpectrum WithZeroMulInt WithZero

open scoped WithZero NNReal

section DVR

variable (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (v : HeightOneSpectrum A) (hv : Finite (A ⧸ v.asIdeal))

instance : IsPrincipalIdealRing (v.valuation K).integer := by
  rw [(Valuation.integer.integers (v.valuation K)).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using (v.valuation K).toMonoidWithZeroHom.range_nontrivial

-- TODO: make this inferred from `IsRankOneDiscrete`
instance : IsDiscreteValuationRing (v.valuation K).integer where
  not_a_field' := by
    simp only [ne_eq, Ideal.ext_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one, Ideal.mem_bot, Subtype.forall, not_forall]
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    use π
    simp [Valuation.mem_integer_iff, ← exp_zero, Subtype.ext_iff, -exp_neg,
      ← (v.valuation K).map_eq_zero_iff, hπ]

instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  unfold HeightOneSpectrum.adicCompletionIntegers
  rw [(Valuation.valuationSubring.integers (Valued.v)).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using Valued.v.range_nontrivial

-- TODO: make this inferred from `IsRankOneDiscrete`, or
-- develop the API for a completion of a base `IsDVR` ring
instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    unfold HeightOneSpectrum.adicCompletionIntegers
    simp only [ne_eq, Ideal.ext_iff, Valuation.mem_maximalIdeal_iff, Ideal.mem_bot, Subtype.ext_iff,
      ZeroMemClass.coe_zero, Subtype.forall, Valuation.mem_valuationSubring_iff, not_forall,
      exists_prop]
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    use (WithVal.equiv (v.valuation K)).symm π
    simp [hπ, ← exp_zero, -exp_neg,
      ← (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_eq_zero_iff]

end DVR

namespace NumberField.RingOfIntegers.HeightOneSpectrum

section AbsoluteValue

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The norm of a maximal ideal is `> 1` -/
lemma one_lt_absNorm : 1 < absNorm v.asIdeal := by
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero, absNorm_ne_zero_iff]
    exact v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  lia

/-- The norm of a maximal ideal as an element of `ℝ≥0` is `> 1` -/
lemma one_lt_absNorm_nnreal : 1 < (absNorm v.asIdeal : ℝ≥0) := mod_cast one_lt_absNorm v

/-- The norm of a maximal ideal as an element of `ℝ≥0` is `≠ 0` -/
lemma absNorm_ne_zero : (absNorm v.asIdeal : ℝ≥0) ≠ 0 :=
  ne_zero_of_lt (one_lt_absNorm_nnreal v)

/-- The `v`-adic absolute value on `K` defined as the norm of `v` raised to negative `v`-adic
valuation -/
noncomputable def adicAbv : AbsoluteValue K ℝ := v.adicAbv <| one_lt_absNorm_nnreal v

theorem adicAbv_def {x : K} : adicAbv v x = toNNReal (absNorm_ne_zero v) (v.valuation K x) := rfl

/-- The `v`-adic absolute value is nonarchimedean -/
theorem isNonarchimedean_adicAbv : IsNonarchimedean (adicAbv v) :=
  v.isNonarchimedean_adicAbv <| one_lt_absNorm_nnreal v

end AbsoluteValue

end RingOfIntegers.HeightOneSpectrum

section FinitePlace
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open RingOfIntegers.HeightOneSpectrum

/-- The embedding of a number field inside its completion with respect to `v`. -/
noncomputable def FinitePlace.embedding : K →+* adicCompletion K v :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (v.valuation K)).symm

theorem FinitePlace.embedding_apply (x : K) : embedding v x = ↑x := rfl

noncomputable instance : (v.valuation K).RankOne where
  hom := toNNReal (absNorm_ne_zero v)
  strictMono' := toNNReal_strictMono (one_lt_absNorm_nnreal v)
  exists_val_nontrivial := by
    rcases Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot with ⟨x, hx1, hx2⟩
    use x
    rw [valuation_of_algebraMap]
    exact ⟨v.intValuation_ne_zero _ hx2, ((intValuation_lt_one_iff_mem _ _).2 hx1).ne⟩

noncomputable instance instRankOneValuedAdicCompletion :
    Valuation.RankOne (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) where
  hom := toNNReal (absNorm_ne_zero v)
  strictMono' := toNNReal_strictMono (one_lt_absNorm_nnreal v)
  exists_val_nontrivial := by
    rcases Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot with ⟨x, hx1, hx2⟩
    use x
    rw [valuedAdicCompletion_eq_valuation' v (x : K)]
    simpa [valuation_of_algebraMap] using ⟨v.intValuation_ne_zero _ hx2, hx1⟩

/-- The `v`-adic completion of `K` is a normed field. -/
noncomputable instance instNormedFieldValuedAdicCompletion : NormedField (adicCompletion K v) :=
  Valued.toNormedField (adicCompletion K v) ℤᵐ⁰

/-- A finite place of a number field `K` is a place associated to an embedding into a completion
with respect to a maximal ideal. -/
def FinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : AbsoluteValue K ℝ // ∃ v : HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w}

/-- Return the finite place defined by a maximal ideal `v`. -/
noncomputable def FinitePlace.mk (v : HeightOneSpectrum (𝓞 K)) : FinitePlace K :=
  ⟨place (embedding v), ⟨v, rfl⟩⟩

lemma toNNReal_valued_eq_adicAbv (x : WithVal (v.valuation K)) :
    toNNReal (absNorm_ne_zero v) (Valued.v x) = adicAbv v (WithVal.equiv _ x) := rfl

/-- A predicate singling out finite places among the absolute values on a number field `K`. -/
def IsFinitePlace (w : AbsoluteValue K ℝ) : Prop :=
  ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w

lemma FinitePlace.isFinitePlace (v : FinitePlace K) : IsFinitePlace v.val := by
  simp [IsFinitePlace, v.prop]

lemma isFinitePlace_iff (v : AbsoluteValue K ℝ) :
    IsFinitePlace v ↔ ∃ w : FinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ w.isFinitePlace⟩

/-- The norm of the image after the embedding associated to `v` is equal to the `v`-adic absolute
value. -/
theorem FinitePlace.norm_def (x : K) :
    ‖embedding v x‖ = adicAbv v x := by
  simp +instances [NormedField.toNorm, instNormedFieldValuedAdicCompletion, Valued.toNormedField,
    Valued.norm, Valuation.RankOne.hom, embedding_apply, adicAbv_def]

/-- The norm of the image after the embedding associated to `v` is equal to the norm of `v` raised
to the power of the `v`-adic valuation. -/
theorem FinitePlace.norm_def' (x : K) :
    ‖embedding v x‖ = toNNReal (absNorm_ne_zero v) (v.valuation K x) := by
  rw [norm_def, adicAbv_def]

/-- The norm of the image after the embedding associated to `v` is equal to the norm of `v` raised
to the power of the `v`-adic valuation for integers. -/
theorem FinitePlace.norm_def_int (x : 𝓞 K) :
    ‖embedding v x‖ = toNNReal (absNorm_ne_zero v) (v.intValuation x) := by
  simp [norm_def, adicAbv_def, valuation_of_algebraMap]

/-- The `v`-adic absolute value satisfies the ultrametric inequality. -/
theorem RingOfIntegers.HeightOneSpectrum.adicAbv_add_le_max (x y : K) :
    adicAbv v (x + y) ≤ (adicAbv v x) ⊔ (adicAbv v y) := isNonarchimedean_adicAbv v x y

/-- The `v`-adic absolute value of a natural number is `≤ 1`. -/
theorem RingOfIntegers.HeightOneSpectrum.adicAbv_natCast_le_one (n : ℕ) : adicAbv v n ≤ 1 :=
  (isNonarchimedean_adicAbv v).apply_natCast_le_one_of_isNonarchimedean

/-- The `v`-adic absolute value of an integer is `≤ 1`. -/
theorem RingOfIntegers.HeightOneSpectrum.adicAbv_intCast_le_one (n : ℤ) : adicAbv v n ≤ 1 :=
  (isNonarchimedean_adicAbv v).apply_intCast_le_one_of_isNonarchimedean

open FinitePlace

/-- The `v`-adic norm of an integer is at most 1. -/
theorem FinitePlace.norm_le_one (x : 𝓞 K) : ‖embedding v x‖ ≤ 1 := by
  rw [norm_def]
  exact v.adicAbv_coe_le_one (one_lt_absNorm_nnreal v) x

/-- The `v`-adic norm of an integer is 1 if and only if it is not in the ideal. -/
theorem FinitePlace.norm_eq_one_iff_notMem (x : 𝓞 K) :
    ‖embedding v x‖ = 1 ↔ x ∉ v.asIdeal := by
  rw [norm_def]
  exact v.adicAbv_coe_eq_one_iff (one_lt_absNorm_nnreal v) x

/-- The `v`-adic norm of an integer is less than 1 if and only if it is in the ideal. -/
theorem FinitePlace.norm_lt_one_iff_mem (x : 𝓞 K) :
    ‖embedding v x‖ < 1 ↔ x ∈ v.asIdeal := by
  rw [norm_def]
  exact v.adicAbv_coe_lt_one_iff (one_lt_absNorm_nnreal v) x

end FinitePlace

namespace FinitePlace
variable {K : Type*} [Field K] [NumberField K]

instance : FunLike (FinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective' _ _ h := Subtype.ext (AbsoluteValue.ext <| congr_fun h)

instance : MonoidWithZeroHomClass (FinitePlace K) K ℝ where
  map_mul w := w.1.map_mul
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

instance : NonnegHomClass (FinitePlace K) K ℝ where
  apply_nonneg w := w.1.nonneg

@[simp]
theorem mk_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) : mk v x = ‖embedding v x‖ := rfl

lemma coe_apply (v : FinitePlace K) (x : K) : v x = v.val x := rfl

/-- For a finite place `w`, return a maximal ideal `v` such that `w = finite_place v` . -/
noncomputable def maximalIdeal (w : FinitePlace K) : HeightOneSpectrum (𝓞 K) := w.2.choose

@[simp]
theorem mk_maximalIdeal (w : FinitePlace K) : mk (maximalIdeal w) = w := Subtype.ext w.2.choose_spec

@[simp]
theorem norm_embedding_eq (w : FinitePlace K) (x : K) :
    ‖embedding (maximalIdeal w) x‖ = w x := by
  conv_rhs => rw [← mk_maximalIdeal w, mk_apply]

theorem pos_iff {w : FinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := w.1.pos_iff

@[simp]
theorem mk_eq_iff {v₁ v₂ : HeightOneSpectrum (𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂ := by
  refine ⟨?_, fun a ↦ by rw [a]⟩
  contrapose!
  intro h
  rw [DFunLike.ne_iff]
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h <| HeightOneSpectrum.ext_iff.mpr <| IsMaximal.eq_of_le (isMaximal v₁) IsPrime.ne_top' H
  use x
  simp only [mk_apply]
  rw [← norm_lt_one_iff_mem] at hx1
  rw [← norm_eq_one_iff_notMem] at hx2
  linarith

theorem maximalIdeal_mk (v : HeightOneSpectrum (𝓞 K)) : maximalIdeal (mk v) = v := by
  rw [← mk_eq_iff, mk_maximalIdeal]

/-- The equivalence between finite places and maximal ideals. -/
noncomputable def equivHeightOneSpectrum :
    FinitePlace K ≃ HeightOneSpectrum (𝓞 K) where
  toFun := maximalIdeal
  invFun := mk
  left_inv := mk_maximalIdeal
  right_inv := maximalIdeal_mk

lemma maximalIdeal_injective : (fun w : FinitePlace K ↦ maximalIdeal w).Injective :=
  equivHeightOneSpectrum.injective

lemma maximalIdeal_inj (w₁ w₂ : FinitePlace K) : maximalIdeal w₁ = maximalIdeal w₂ ↔ w₁ = w₂ :=
  equivHeightOneSpectrum.injective.eq_iff

@[fun_prop]
theorem hasFiniteMulSupport_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (fun w : FinitePlace K ↦ w x).HasFiniteMulSupport := by
  have (w : FinitePlace K) : w x ≠ 1 ↔ w x < 1 :=
    ne_iff_lt_iff_le.mpr <| norm_embedding_eq w x ▸ norm_le_one w.maximalIdeal x
  simp_rw [Function.HasFiniteMulSupport, Function.mulSupport, this, ← norm_embedding_eq,
    norm_lt_one_iff_mem, ← Ideal.dvd_span_singleton]
  have h : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  have h_inj : Set.InjOn FinitePlace.maximalIdeal {w | w.maximalIdeal.asIdeal ∣ span {x}} :=
    Function.Injective.injOn maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_span_singleton, Set.image_subset_iff, Set.preimage_setOf_eq, subset_refl]

@[deprecated (since := "2026-03-03")] alias mulSupport_finite_int := hasFiniteMulSupport_int

@[fun_prop]
theorem hasFiniteMulSupport {x : K} (h_x_nezero : x ≠ 0) :
    (fun w : FinitePlace K ↦ w x).HasFiniteMulSupport := by
  rcases IsFractionRing.div_surjective (A := 𝓞 K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀]
  obtain ⟨ha, hb⟩ := h_x_nezero
  simp_rw [← RingOfIntegers.coe_eq_algebraMap]
  fun_prop (disch := assumption)

@[deprecated (since := "2026-03-03")] alias mulSupport_finite := hasFiniteMulSupport

protected
lemma add_le (v : FinitePlace K) (x y : K) :
    v (x + y) ≤ max (v x) (v y) := by
  obtain ⟨w, hw⟩ := v.prop
  have H x : v x = RingOfIntegers.HeightOneSpectrum.adicAbv w x := by
    rw [show v x = v.val x from rfl]
    grind only [place_apply, norm_def]
  simpa only [H] using RingOfIntegers.HeightOneSpectrum.adicAbv_add_le_max w x y

instance : NonarchimedeanHomClass (FinitePlace K) K ℝ where
  map_add_le_max v a b := FinitePlace.add_le v a b

end FinitePlace

end NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

open NumberField.FinitePlace NumberField.RingOfIntegers
  NumberField.RingOfIntegers.HeightOneSpectrum
open scoped NumberField

lemma equivHeightOneSpectrum_symm_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (equivHeightOneSpectrum.symm v) x = ‖embedding v x‖ := rfl

set_option backward.isDefEq.respectTransparency false in
open Ideal in
lemma embedding_mul_absNorm (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K}
    (h_x_nezero : x ≠ 0) : ‖embedding v x‖ * absNorm (v.maxPowDividing (span {x})) = 1 := by
  rw [maxPowDividing, map_pow, Nat.cast_pow, norm_def, adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _
      ((v.valuation K).ne_zero_iff.mpr (coe_ne_zero_iff.mpr h_x_nezero))]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_absNorm_nnreal v)).ne']
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_absNorm_nnreal v).ne')]
  simp [valuation_of_algebraMap, intValuation_if_neg, h_x_nezero]

end IsDedekindDomain.HeightOneSpectrum
