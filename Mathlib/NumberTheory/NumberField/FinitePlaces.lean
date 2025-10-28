/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.Algebra.Order.Archimedean.Submonoid
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Data.Int.WithZero
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Algebra.Ring.Subring.IntPolynomial
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

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
* `NumberField.FinitePlace.mulSupport_finite`: the `v`-adic absolute value of a non-zero element of
  `K` is different from 1 for at most finitely many `v`.
*  The valuation subrings of the field at the `v`-valuation and it's adic completion are
   discrete valuation rings.

## Tags
number field, places, finite places
-/

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
    simp [Valuation.mem_integer_iff, ← exp_zero, Subtype.ext_iff, - exp_neg,
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
    use π
    simp [hπ, ← exp_zero, - exp_neg,
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
  cutsat

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
noncomputable def FinitePlace.embedding : WithVal (v.valuation K) →+* adicCompletion K v :=
  UniformSpace.Completion.coeRingHom

theorem FinitePlace.embedding_apply (x : K) : embedding v x = ↑x := rfl

noncomputable
instance : (v.valuation K).RankOne where
  hom := {
    toFun := toNNReal (absNorm_ne_zero v)
    map_zero' := rfl
    map_one' := rfl
    map_mul' := MonoidWithZeroHom.map_mul (toNNReal (absNorm_ne_zero v))
  }
  strictMono' := toNNReal_strictMono (one_lt_absNorm_nnreal v)
  exists_val_nontrivial := by
    rcases Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot with ⟨x, hx1, hx2⟩
    use x
    rw [valuation_of_algebraMap] --intValuation_lt_one_iff_mem]
    rw [← intValuation_lt_one_iff_mem] at hx1
    refine ⟨v.intValuation_ne_zero _ hx2, hx1.ne⟩

noncomputable instance instRankOneValuedAdicCompletion :
    Valuation.RankOne (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) where
  hom := {
    toFun := toNNReal (absNorm_ne_zero v)
    map_zero' := rfl
    map_one' := rfl
    map_mul' := MonoidWithZeroHom.map_mul (toNNReal (absNorm_ne_zero v))
  }
  strictMono' := toNNReal_strictMono (one_lt_absNorm_nnreal v)
  exists_val_nontrivial := by
    rcases Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot with ⟨x, hx1, hx2⟩
    use x
    dsimp [adicCompletion]
    rw [valuedAdicCompletion_eq_valuation' v (x : K)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rwa [valuation_of_algebraMap, intValuation_lt_one_iff_mem]

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
    toNNReal (absNorm_ne_zero v) (Valued.v x) = adicAbv v x := rfl

@[deprecated (since := "2025-03-01")]
  alias toNNReal_Valued_eq_vadicAbv := toNNReal_valued_eq_adicAbv

/-- The norm of the image after the embedding associated to `v` is equal to the `v`-adic absolute
value. -/
theorem FinitePlace.norm_def (x : WithVal (v.valuation K)) : ‖embedding v x‖ = adicAbv v x := by
  simp [NormedField.toNorm, instNormedFieldValuedAdicCompletion, Valued.toNormedField, Valued.norm,
    Valuation.RankOne.hom, embedding_apply, ← toNNReal_valued_eq_adicAbv]

/-- The norm of the image after the embedding associated to `v` is equal to the norm of `v` raised
to the power of the `v`-adic valuation. -/
theorem FinitePlace.norm_def' (x : WithVal (v.valuation K)) :
    ‖embedding v x‖ = toNNReal (absNorm_ne_zero v) (v.valuation K x) := by
  rw [norm_def, adicAbv_def]

/-- The norm of the image after the embedding associated to `v` is equal to the norm of `v` raised
to the power of the `v`-adic valuation for integers. -/
theorem FinitePlace.norm_def_int (x : 𝓞 (WithVal (v.valuation K))) :
    ‖embedding v x‖ = toNNReal (absNorm_ne_zero v) (v.intValuation x) := by
  rw [norm_def, adicAbv_def, valuation_of_algebraMap]

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
theorem FinitePlace.norm_le_one (x : 𝓞 (WithVal (v.valuation K))) : ‖embedding v x‖ ≤ 1 := by
  rw [norm_def]
  exact v.adicAbv_coe_le_one (one_lt_absNorm_nnreal v) x

/-- The `v`-adic norm of an integer is 1 if and only if it is not in the ideal. -/
theorem FinitePlace.norm_eq_one_iff_notMem (x : 𝓞 (WithVal (v.valuation K))) :
    ‖embedding v x‖ = 1 ↔ x ∉ v.asIdeal := by
  rw [norm_def]
  exact v.adicAbv_coe_eq_one_iff (one_lt_absNorm_nnreal v) x

@[deprecated (since := "2025-05-23")]
alias FinitePlace.norm_eq_one_iff_not_mem := FinitePlace.norm_eq_one_iff_notMem

/-- The `v`-adic norm of an integer is less than 1 if and only if it is in the ideal. -/
theorem FinitePlace.norm_lt_one_iff_mem (x : 𝓞 (WithVal (v.valuation K))) :
    ‖embedding v x‖ < 1 ↔ x ∈ v.asIdeal := by
  rw [norm_def]
  exact v.adicAbv_coe_lt_one_iff (one_lt_absNorm_nnreal v) x

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
theorem mk_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) : mk v x = ‖embedding v x‖ := rfl

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

theorem mulSupport_finite_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K ↦ w x).Finite := by
  have (w : FinitePlace K) : w x ≠ 1 ↔ w x < 1 :=
    ne_iff_lt_iff_le.mpr <| norm_embedding_eq w x ▸ norm_le_one w.maximalIdeal x
  simp_rw [Function.mulSupport, this, ← norm_embedding_eq, norm_lt_one_iff_mem,
    ← Ideal.dvd_span_singleton]
  have h : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  have h_inj : Set.InjOn FinitePlace.maximalIdeal {w | w.maximalIdeal.asIdeal ∣ span {x}} :=
    Function.Injective.injOn maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_span_singleton, Set.image_subset_iff, Set.preimage_setOf_eq, subset_refl]

theorem mulSupport_finite {x : K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K ↦ w x).Finite := by
  rcases IsFractionRing.div_surjective (A := 𝓞 K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀]
  obtain ⟨ha, hb⟩ := h_x_nezero
  simp_rw [← RingOfIntegers.coe_eq_algebraMap]
  apply ((mulSupport_finite_int ha).union (mulSupport_finite_int hb)).subset
  intro w
  simp only [Function.mem_mulSupport, ne_eq, Set.mem_union]
  contrapose!
  simp +contextual only [ne_eq, one_ne_zero, not_false_eq_true, div_self, implies_true]

end FinitePlace

end NumberField

namespace IsDedekindDomain.HeightOneSpectrum

section LiesOver

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Algebra A B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A] [Algebra A L]
    [Algebra K L] [IsDedekindDomain B] [IsScalarTower A B L] [IsScalarTower A K L]
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)

lemma mk_count_factors_map
    (hAB : Function.Injective (algebraMap A B))
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (I : Ideal A)
    [DecidableEq (Ideal B)]
    [DecidableEq (Associates (Ideal A))] [DecidableEq (Associates (Ideal B))]
    [∀ p : Associates (Ideal A), Decidable (Irreducible p)]
    [∀ p : Associates (Ideal B), Decidable (Irreducible p)]
    [w.asIdeal.LiesOver v.asIdeal] :
    (Associates.mk w.asIdeal).count (Associates.mk (I.map (algebraMap A B))).factors =
    Ideal.ramificationIdx (algebraMap A B) v.asIdeal w.asIdeal *
      (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Associates.mk_zero, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot,
      Associates.mk_zero]
    simp [Associates.count, Associates.factors_zero, w.associates_irreducible,
      associates_irreducible v, Associates.bcount]
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp only [Ideal.map_top]
    simp only [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    rw [Associates.count_zero (associates_irreducible _),
      Associates.count_zero (associates_irreducible _), mul_zero]
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul, ← Associates.mk_mul_mk]
    have hp_bot : p ≠ ⊥ := hp.ne_zero
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp_bot
    have hI_bot := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hI
    rw [Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot) (Associates.mk_ne_zero.mpr hI)
      (associates_irreducible _), Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot')
      (Associates.mk_ne_zero.mpr hI_bot) (associates_irreducible _)]
    simp only [IH, mul_add]
    congr 1
    by_cases hw : v.asIdeal = p
    · have : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
      rw [hw, Associates.factors_self this, Associates.count_some this]
      simp only [Multiset.nodup_singleton, Multiset.mem_singleton, Multiset.count_eq_one_of_mem,
        mul_one]
      rw [count_associates_factors_eq hp_bot' w.2 w.3,
        Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp_bot' w.2 w.3]
    · have : (Associates.mk v.asIdeal).count (Associates.mk p).factors = 0 :=
        Associates.count_eq_zero_of_ne (associates_irreducible _)
          (Associates.irreducible_mk.mpr hp.irreducible)
          (by rwa [ne_eq, Associates.mk_eq_mk_iff_associated, associated_iff_eq])
      rw [this, mul_zero, eq_comm]
      by_contra H
      rw [eq_comm, ← ne_eq, Associates.count_ne_zero_iff_dvd hp_bot' (irreducible w),
        Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← under_def,
        ← Ideal.over_def w.asIdeal v.asIdeal] at H
      apply hw (((Ideal.isPrime_of_prime hp).isMaximal hp_bot).eq_of_le v.2.ne_top H).symm

lemma intValuation_comap [NoZeroSMulDivisors A B] (hAB : Function.Injective (algebraMap A B))
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (x : A)
    [w.asIdeal.LiesOver v.asIdeal] :
    v.intValuation x ^ (Ideal.ramificationIdx (algebraMap A B) v.asIdeal w.asIdeal) =
      w.intValuation (algebraMap A B x) := by
  classical
  by_cases hx : x = 0
  · simp [hx, ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  change (ite _ _ _) ^ _ = ite _ _ _
  rw [map_eq_zero_iff _ hAB, if_neg hx, if_neg hx, ← Set.image_singleton, ← Ideal.map_span,
    mk_count_factors_map _ _ hAB v w, mul_comm]
  simp [← WithZero.coe_pow, ← ofAdd_nsmul, mul_comm]

open scoped algebraMap in
lemma valuation_liesOver [IsFractionRing B L] [NoZeroSMulDivisors A B]
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : WithVal (v.valuation K)) :
    let e := Ideal.ramificationIdx (algebraMap A B) v.asIdeal w.asIdeal
    v.valuation K x ^ e = w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp
  erw [valuation_of_algebraMap, valuation_of_algebraMap]
  erw [div_pow, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L]
  rw [valuation_of_algebraMap]
  rw [← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L) v w]
  erw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L]
  rw [valuation_of_algebraMap]
  rw [← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L) v w]

variable {A K B L v w} in
theorem uniformContinuous_algebraMap [IsFractionRing B L] [NoZeroSMulDivisors A B]
    [w.asIdeal.LiesOver v.asIdeal] :
    UniformContinuous (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp only [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  let e := Ideal.ramificationIdx (algebraMap A B) v.asIdeal w.asIdeal
  use WithZero.expEquiv ((WithZero.log γ) / e)
  simp
  intro x hx
  change (w.valuation L (algebraMap K L x)) < γ
  rw [← valuation_liesOver A K L B]
  rcases eq_or_ne x 0 with (rfl | hx₀);
  · simp [ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  · rw [← WithZero.log_lt_log (by simp_all) (by simp)] at hx
    rw [← WithZero.log_lt_log (by simp_all) (by simp)]
    simp at hx ⊢
    have := Int.mul_lt_of_lt_ediv (by
      simpa using Nat.pos_of_ne_zero (ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx
    rw [mul_comm]
    exact this

noncomputable
instance [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal] :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  UniformSpace.Completion.mapRingHom _ uniformContinuous_algebraMap.continuous |>.toAlgebra

theorem algebraMap_coe [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal]
    (x : WithVal (v.valuation K)) :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) x =
      algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)) x := by
  simp [RingHom.algebraMap_toAlgebra, UniformSpace.Completion.mapRingHom_apply]
  rw [UniformSpace.Completion.map_coe uniformContinuous_algebraMap]

open WithZeroTopology in
theorem valued_liesOver [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    letI e := Ideal.ramificationIdx (algebraMap A B) v.asIdeal w.asIdeal
    Valued.v x ^ e = Valued.v (algebraMap _ (w.adicCompletion L) x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    apply isClosed_eq
    · apply Continuous.pow Valued.continuous_valuation
    · apply Continuous.comp Valued.continuous_valuation
      apply UniformSpace.Completion.continuous_map
  | ih a =>
    rw [valuedAdicCompletion_eq_valuation', algebraMap_coe, valuedAdicCompletion_eq_valuation']
    rw [valuation_liesOver A K L]
    rfl

theorem exists_liesOver [Algebra.IsIntegral A B] :
    ∃ v : HeightOneSpectrum A, w.asIdeal.LiesOver v.asIdeal := by
  let v : HeightOneSpectrum A := {
    asIdeal := under A w.asIdeal
    isPrime := IsPrime.under A w.asIdeal
    ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot
  }
  use v
  exact ⟨rfl⟩

lemma absNorm_eq_pow_inertiaDeg' [Module.Free ℤ B] [Module.Free ℤ A] [Module.Finite A B]
    (P : Ideal B) (p : Ideal A) [P.LiesOver p] (hp : p.IsPrime) (hp_ne_bot : p ≠ ⊥) :
    absNorm P = absNorm p ^ (p.inertiaDeg P) := by
  have : p.IsMaximal := hp.isMaximal hp_ne_bot
  let _ : Field (A ⧸ p) := Quotient.field p
  simp [inertiaDeg_algebraMap, absNorm_apply, Submodule.cardQuot_apply]
  rw [Module.natCard_eq_pow_finrank (K := A ⧸ p)]

instance [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal] :
  (Valued.v : Valuation (v.adicCompletion K) _).HasExtension
    (Valued.v : Valuation (w.adicCompletion L) _) where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_eq_one]
    simp
    simp_rw [← valued_liesOver]
    intro x
    apply Iff.intro
    · intro a
      simp_all only [one_pow]
    · intro a
      rwa [pow_eq_one_iff (ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot)] at a

-- Only doesn't cause diamonds because I.LiesOver I doesn't exist yet ...
noncomputable
instance instAlgebraLiesOver [IsFractionRing B L] [NoZeroSMulDivisors A B]
    [w.asIdeal.LiesOver v.asIdeal] :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  inferInstanceAs (Algebra Valued.v.valuationSubring Valued.v.valuationSubring)

instance [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal] :
   IsLocalHom (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) :=
  inferInstanceAs (IsLocalHom (algebraMap Valued.v.valuationSubring Valued.v.valuationSubring))

-- Only doesn't cause diamonds because I.LiesOver I doesn't exist yet ...
noncomputable
instance [IsFractionRing B L] [NoZeroSMulDivisors A B]
    [w.asIdeal.LiesOver v.asIdeal] :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletion L) :=
  Algebra.compHom _ (algebraMap _ (w.adicCompletionIntegers L))

attribute [local instance 1001] Algebra.toSMul in
noncomputable
instance [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) (w.adicCompletion L) :=
  Valuation.HasExtension.instIsScalarTower_valuationSubring' _ _

attribute [local instance 1001] Algebra.toSMul in
noncomputable
instance [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L) :=
  Valuation.HasExtension.instIsScalarTower_valuationSubring _

noncomputable instance {v : HeightOneSpectrum A}
    [(Valued.v : Valuation (v.adicCompletion K) _).RankOne] :
    NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField

end LiesOver

open NumberField.FinitePlace NumberField.RingOfIntegers
  NumberField.RingOfIntegers.HeightOneSpectrum
open scoped NumberField Valued

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))

lemma equivHeightOneSpectrum_symm_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (equivHeightOneSpectrum.symm v) x = ‖embedding v x‖ := rfl

open Ideal in
lemma embedding_mul_absNorm (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 (WithVal (v.valuation K))}
    (h_x_nezero : x ≠ 0) : ‖embedding v x‖ * absNorm (v.maxPowDividing (span {x})) = 1 := by
  rw [maxPowDividing, map_pow, Nat.cast_pow, norm_def, adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _
      ((v.valuation K).ne_zero_iff.mpr (coe_ne_zero_iff.mpr h_x_nezero))]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_absNorm_nnreal v)).ne']
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_absNorm_nnreal v).ne')]
  simp [valuation_of_algebraMap, intValuation_if_neg, h_x_nezero]

open NumberField

open scoped TensorProduct in
instance [w.asIdeal.LiesOver v.asIdeal] :
    Module.Finite (v.adicCompletion K) (w.adicCompletion L) := by
  let Lw := w.adicCompletion L
  let Kᵥ := v.adicCompletion K
  let Φ : Kᵥ ⊗[ℚ] L →ₗ[Kᵥ] Lw := by
    apply Algebra.TensorProduct.lift (Algebra.algHom Kᵥ Kᵥ Lw) (Algebra.algHom ℚ L Lw) ?_
      |>.toLinearMap
    intro x y
    simp [Commute, SemiconjBy, mul_comm]
  have : Module.Finite Kᵥ (LinearMap.range Φ) := by
    exact LinearMap.finiteDimensional_range Φ
  have : ContinuousSMul Kᵥ Lw := by
    apply ContinuousSMul.mk
    apply Continuous.mul
    · simp_rw [UniformSpace.Completion.mapRingHom_apply]
      apply Continuous.comp
      · exact UniformSpace.Completion.continuous_map
      · fun_prop
    · fun_prop
  have hclosed : IsClosed (LinearMap.range Φ : Set Lw) :=
    Submodule.closed_of_finiteDimensional (LinearMap.range Φ)
  have hss : Set.range (algebraMap L Lw) ⊆ LinearMap.range Φ := by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    use 1 ⊗ₜ[ℚ] x
    simp [Φ]
    rfl
  have h_dense : Dense (Set.range (algebraMap L Lw)) := by
    exact UniformSpace.Completion.denseRange_coe (α := WithVal (w.valuation L))
  have h_dense := h_dense.mono hss
  have := DenseRange.closure_range h_dense
  erw [hclosed.closure_eq] at this
  have hsurj : Function.Surjective Φ := by
    rw [← Set.range_eq_univ]
    exact this
  exact Module.Finite.of_surjective _ hsurj

instance : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K _)

instance [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) :=
  inferInstance

theorem _root_.NNReal.zpow_pow_comm {x : ℝ≥0} {z : ℤ} {n : ℕ} : (x ^ z) ^ n = (x ^ n) ^ z := by
  simpa [← zpow_natCast] using zpow_comm _ _ _

private lemma inertiaDeg_mul_ramificationIdx_ne_zero [w.asIdeal.LiesOver v.asIdeal] :
    (v.asIdeal.inertiaDeg w.asIdeal *
      v.asIdeal.ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal) ≠ 0 := by
  simpa [-inertiaDeg_algebraMap] using
    ⟨Ideal.inertiaDeg_ne_zero _ _, ramificationIdx_ne_zero_of_liesOver _ v.ne_bot⟩

noncomputable
def algebraNorm_of_liesOver [w.asIdeal.LiesOver v.asIdeal] :
    AlgebraNorm (v.adicCompletion K) (w.adicCompletion L) where
  toFun x :=
    let e := v.asIdeal.ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal *
      v.asIdeal.inertiaDeg w.asIdeal
    ‖x‖ ^ (e : ℝ)⁻¹
  map_zero' := by
    simp [-inertiaDeg_algebraMap]
    rw [← mul_inv]
    rw [Real.rpow_inv_eq le_rfl le_rfl
      (by rw [← Nat.cast_mul, Nat.cast_ne_zero]; exact inertiaDeg_mul_ramificationIdx_ne_zero v w)]
    rw [← Nat.cast_mul]
    rw [Real.rpow_natCast]
    rw [zero_pow]
    exact inertiaDeg_mul_ramificationIdx_ne_zero v w
  add_le' r s := by
    apply (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le r s)
      (by simp only [inv_nonneg, Nat.cast_nonneg])).trans
    apply NNReal.rpow_add_le_add_rpow _ _ (by simp only [inv_nonneg, Nat.cast_nonneg])
    rw [inv_le_one₀]
    · simp only [Nat.one_le_cast]
      linarith [Nat.pos_of_ne_zero <| inertiaDeg_mul_ramificationIdx_ne_zero v w]
    · simp only [Nat.cast_pos, mul_comm]
      exact Nat.pos_of_ne_zero <| inertiaDeg_mul_ramificationIdx_ne_zero v w
  neg' := by simp [norm_neg]
  mul_le' := by simp [Real.mul_rpow]
  eq_zero_of_map_eq_zero' := fun _ h => by
    rwa [Real.rpow_eq_zero (norm_nonneg _), norm_eq_zero] at h
    simpa using inertiaDeg_mul_ramificationIdx_ne_zero v w
  smul' a x := by
    simp [RingHom.smul_toAlgebra, Real.mul_rpow, -inertiaDeg_algebraMap]
    left
    rw [← mul_inv]
    rw [Real.rpow_inv_eq (norm_nonneg _) (norm_nonneg _)
      (by rw [← Nat.cast_mul, Nat.cast_ne_zero]; exact inertiaDeg_mul_ramificationIdx_ne_zero v w)]
    simp [instNormedFieldValuedAdicCompletion, -inertiaDeg_algebraMap]
    change _ = (toNNReal (absNorm_ne_zero v) (Valued.v a) : ℝ) ^ _
    change (toNNReal (absNorm_ne_zero w) (Valued.v (algebraMap _ (w.adicCompletion L) a)) : ℝ) = _
    rw [← Nat.cast_mul]
    rw [Real.rpow_natCast]
    rw [← NNReal.coe_pow, NNReal.coe_inj]
    rw [mul_comm]
    rw [pow_mul]
    rw [← map_pow]
    rw [← valued_liesOver]
    simp [toNNReal, -inertiaDeg_algebraMap]
    rw [absNorm_eq_pow_inertiaDeg' (𝓞 K) (𝓞 L) w.asIdeal v.asIdeal v.isPrime v.ne_bot]
    rw [zero_pow <| Ideal.inertiaDeg_ne_zero _ _]
    split_ifs
    · rfl
    · simp [NNReal.zpow_pow_comm]

instance instIsIntegral [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsIntegral (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) where
  isIntegral x := by
    simp [IsIntegral, RingHom.IsIntegralElem]
    let q := minpoly (v.adicCompletion K) x.1
    have hq : ∀ n : ℕ, ‖q.coeff n‖ ≤ 1 := by
      rw [← spectralValue_le_one_iff
        (minpoly.monic <| IsAlgebraic.isIntegral <| Algebra.IsAlgebraic.isAlgebraic _)]
      have := x.2
      rw [mem_adicCompletionIntegers] at this
      let e := v.asIdeal.ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal *
        v.asIdeal.inertiaDeg w.asIdeal
      have hnorm : ‖x‖ ^ (e : ℝ)⁻¹ = spectralValue q := by
        let f : AlgebraNorm (v.adicCompletion K) (w.adicCompletion L) :=
          algebraNorm_of_liesOver v w
        have hf : IsPowMul f := by
          simp [IsPowMul, f]
          intro a n hn
          change ‖a ^ n‖ ^ (_ : ℝ)⁻¹ = (‖a‖ ^ (_ : ℝ)⁻¹) ^ n
          simp [Real.rpow_pow_comm]
        have := spectralNorm_unique hf
        rw [AlgebraNorm.ext_iff] at this
        simp [f] at this
        specialize this x
        simpa using this
      rw [← hnorm]
      simp
      apply Real.rpow_le_one (by simp) (Valued.toNormedField.norm_le_one_iff.mpr this)
        (by simp)
    set p : Polynomial (v.adicCompletionIntegers K) :=
      q.int (v.adicCompletionIntegers K).toSubring (by simpa using hq)
    use p
    rw [Polynomial.int_monic_iff]
    constructor
    · apply minpoly.monic
      apply IsAlgebraic.isIntegral
      apply Algebra.IsAlgebraic.isAlgebraic
    · simp only [p]
      have := Polynomial.int_eval₂_eq (v.adicCompletionIntegers K).toSubring q
        (by simpa using hq) x.1
      rw [minpoly.aeval] at this
      apply_fun (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) using
        IsFractionRing.injective _ _
      simp_rw [ValuationSubring.algebraMap_apply]
      simp only [ZeroMemClass.coe_zero]
      rw [← this]
      rw [← ValuationSubring.subtype_apply]
      simp only [Polynomial.eval₂_def]
      simp only [Polynomial.sum_def, map_sum]
      apply Finset.sum_congr rfl
      intro e _
      simp
      rw [← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      left
      rfl

instance instIsIntegralClosure [w.asIdeal.LiesOver v.asIdeal] :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) :=
  -- takes too long to synthesize on its own
  let _ : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
    instIsIntegral _ _
  IsIntegralClosure.of_isIntegrallyClosed (w.adicCompletionIntegers L)
    (v.adicCompletionIntegers K) (w.adicCompletion L)

instance instFiniteIntegers [w.asIdeal.LiesOver v.asIdeal] :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  let _ := instIsIntegralClosure v w
  IsIntegralClosure.finite _ (v.adicCompletion K) (w.adicCompletion L) _

instance : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))

open Valued integer in
theorem compact_adicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) := by
  apply CompactSpace.mk
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_, ?_⟩
  · rw [Valued.integer.totallyBounded_iff_finite_residueField]
    obtain ⟨𝔭, _⟩ := exists_liesOver (𝓞 ℚ) _ v
    have : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers ℚ)) := by
      have : CompactSpace (𝔭.adicCompletionIntegers ℚ) :=
        𝔭.adicCompletionIntegersEquivPadicInt.toHomeomorph.symm.compactSpace
      erw [compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
        at this
      exact this.2.2
    let _ := instFiniteIntegers 𝔭 v
    exact IsLocalRing.ResidueField.finite_of_finite this (S := v.adicCompletionIntegers K)
  · rw [← completeSpace_iff_isComplete_univ]
    exact Valued.isClosed_valuationSubring _ |>.completeSpace_coe

end IsDedekindDomain.HeightOneSpectrum
