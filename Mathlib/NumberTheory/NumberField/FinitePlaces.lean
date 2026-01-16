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
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Algebra.Ring.Subring.IntPolynomial
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

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
    use π
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
noncomputable def FinitePlace.embedding : WithVal (v.valuation K) →+* adicCompletion K v :=
  UniformSpace.Completion.coeRingHom

theorem FinitePlace.embedding_apply (x : K) : embedding v x = ↑x := rfl

noncomputable instance : (v.valuation K).RankOne where
  hom := {
    toFun := toNNReal (absNorm_ne_zero v)
    map_zero' := rfl
    map_one' := rfl
    map_mul' := map_mul (toNNReal (absNorm_ne_zero v))
  }
  strictMono' := toNNReal_strictMono (one_lt_absNorm_nnreal v)
  exists_val_nontrivial := by
    rcases Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot with ⟨x, hx1, hx2⟩
    use x
    rw [valuation_of_algebraMap]
    exact ⟨v.intValuation_ne_zero _ hx2, ((intValuation_lt_one_iff_mem _ _).2 hx1).ne⟩

@[deprecated Valuation.instRankOneCompletion (since := "2026-01-05")]
noncomputable instance instRankOneValuedAdicCompletion :
    Valuation.RankOne (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := inferInstance

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

open UniqueFactorizationMonoid in
theorem Ideal.IsDedekindDomain.emultiplicity_eq_zero_of_ne {R : Type*} [CommRing R]
    [IsDedekindDomain R] {a b : Ideal R} (ha : Irreducible a) (hb : Irreducible b) (h : a ≠ b)
    (h_bot : b ≠ ⊥) : emultiplicity a b = 0 := by
  classical
  rw [emultiplicity_eq_count_normalizedFactors ha hb.ne_zero, normalize_eq, Nat.cast_eq_zero,
    Multiset.count_eq_zero, Ideal.mem_normalizedFactors_iff h_bot, not_and]
  intro _ h_le
  exact h ((((Ideal.prime_iff_isPrime hb.ne_zero).1 hb.prime).isMaximal hb.ne_zero).eq_of_le
    IsPrime.ne_top' h_le).symm

namespace IsDedekindDomain

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Algebra A B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A] [Algebra A L]
    [Algebra K L] [IsDedekindDomain B] [IsScalarTower A B L] [IsScalarTower A K L]
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)

variable {A B} in
open UniqueFactorizationMonoid Ideal.IsDedekindDomain in
theorem emultiplicity_map_right_eq
    (hAB : Function.Injective (algebraMap A B))
    {v : Ideal A} {w : Ideal B} {I : Ideal A} (h : I ≠ ⊥)
    (hv : Irreducible v) (hw : Irreducible w) (hw_ne_bot : w ≠ ⊥)
    [w.LiesOver v] :
    emultiplicity w (I.map (algebraMap A B)) =
      v.ramificationIdx (algebraMap A B) w * emultiplicity v I := by
  classical
  induction I using induction_on_prime with
  | h₁ => aesop
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp_rw [Ideal.map_top, emultiplicity_eq_count_normalizedFactors hw top_ne_bot,
      emultiplicity_eq_count_normalizedFactors hv h, ← Ideal.one_eq_top, normalizedFactors_one]
    simp
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul]
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp.ne_zero
    rw [emultiplicity_mul hw.prime, emultiplicity_mul hv.prime, IH hI, mul_add]
    congr
    by_cases hvp : v = p
    · simp [hvp, (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self, mul_one,
        ramificationIdx_eq_normalizedFactors_count hp_bot' ((Ideal.prime_iff_isPrime hw_ne_bot).1
          hw.prime) hw_ne_bot, emultiplicity_eq_count_normalizedFactors hw hp_bot']
    · have h₀ := emultiplicity_eq_zero_of_ne hv hp.irreducible hvp hp.ne_zero
      rw [h₀, mul_zero, emultiplicity_eq_count_normalizedFactors hw hp_bot', normalize_eq,
        Nat.cast_eq_zero, Multiset.count_eq_zero, Ideal.mem_normalizedFactors_iff hp_bot', not_and]
      intro _ H
      rw [Ideal.map_le_iff_le_comap, ← under_def, ← Ideal.over_def w v] at H
      exact hvp ((((Ideal.prime_iff_isPrime hp.ne_zero).1 hp).isMaximal hp.ne_zero).eq_of_le
        (fun h ↦ by simp [h, emultiplicity] at h₀) H).symm

namespace HeightOneSpectrum

lemma intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [intValuation_if_neg _ hnz, count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

lemma intValuation_comap [NoZeroSMulDivisors A B] (hAB : Function.Injective (algebraMap A B))
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (x : A) [w.asIdeal.LiesOver v.asIdeal] :
    v.intValuation x ^ (v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal) =
      w.intValuation (algebraMap A B x) := by
  rcases eq_or_ne x 0 with rfl | hx; · simp [ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  rw [intValuation_eq_coe_neg_multiplicity v hx, intValuation_eq_coe_neg_multiplicity w (by simpa),
    ← Set.image_singleton, ← Ideal.map_span, exp_neg, exp_neg, inv_pow, ← exp_nsmul,
    Int.nsmul_eq_mul, inv_inj, exp_inj, ← Nat.cast_mul, Nat.cast_inj]
  refine multiplicity_eq_of_emultiplicity_eq_some ?_ |>.symm
  rw [emultiplicity_map_right_eq hAB (by simp [hx]) v.irreducible w.irreducible w.ne_bot,
    Nat.cast_mul]
  congr
  exact (FiniteMultiplicity.of_prime_left v.prime (by simp [hx])).emultiplicity_eq_multiplicity

theorem _root_.WithVal.algebraMap_apply {K Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Field K] {A : Type*} [CommSemiring A] [Algebra A K] (v : Valuation K Γ₀) (x : A) :
    algebraMap A (WithVal v) x = algebraMap A K x := rfl

theorem _root_.WithVal.algebraMap_apply' {K Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Field K] {A : Type*} [Field A] [Algebra K A] (v : Valuation K Γ₀) (x : K) :
    algebraMap (WithVal v) A x = algebraMap K A x := rfl

variable {A K B} in
open scoped algebraMap in
lemma valuation_liesOver [IsFractionRing B L] [NoZeroSMulDivisors A B]
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : WithVal (v.valuation K)) :
    v.valuation K x ^ v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal =
      w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [WithVal.algebraMap_apply, valuation_of_algebraMap, div_pow,
    ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L) v w]

variable {A K B L v w} in
theorem uniformContinuous_algebraMap [IsFractionRing B L] [NoZeroSMulDivisors A B]
    [w.asIdeal.LiesOver v.asIdeal] :
    UniformContinuous (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  use WithZero.expEquiv ((WithZero.log γ) / v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal)
  simp only [adicValued_apply', coe_expEquiv_apply, Set.mem_setOf_eq, true_and]
  intro x hx
  change (w.valuation L (algebraMap K L x)) < γ
  rw [← valuation_liesOver L]
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp [ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  · rw [← WithZero.log_lt_log (by simp_all) (by simp)] at hx ⊢
    simp_rw [log_exp, log_pow, Int.nsmul_eq_mul] at hx ⊢
    rw [mul_comm]
    exact Int.mul_lt_of_lt_ediv
      (mod_cast Nat.pos_of_ne_zero (ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx

-- noncomputable
-- instance [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal] :
--     Algebra (v.adicCompletion K) (w.adicCompletion L) :=
--   UniformSpace.Completion.mapRingHom _ uniformContinuous_algebraMap.continuous |>.toAlgebra

-- instance [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal] :
--     ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
--   continuous_smul := (UniformSpace.Completion.continuous_map.comp (by fun_prop)).mul (by fun_prop)

open WithZeroTopology UniformSpace.Completion in
theorem valued_liesOver [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal]
    [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower (WithVal (v.valuation K)) (v.adicCompletion K) (w.adicCompletion L)]
    (x : v.adicCompletion K) :
    Valued.v x ^ v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal =
      Valued.v (algebraMap _ (w.adicCompletion L) x) := by
  induction x using induction_on with
  | hp =>
    exact isClosed_eq (Valued.continuous_valuation.pow _)
      (Valued.continuous_valuation.comp <| continuous_algebraMap _ _)
  | ih a =>
    have := IsScalarTower.algebraMap_apply _ (v.adicCompletion K) (w.adicCompletion L) a
    rw [algebraMap_def] at this
    rw [algebraMap_def] at this
    rw [valuedAdicCompletion_eq_valuation']
    simp at this
    rw [← this]
    rw [valuedAdicCompletion_eq_valuation']
    rw [valuation_liesOver L]
    rw [WithVal.algebraMap_apply, WithVal.algebraMap_apply']

variable {B} in
def under [Algebra.IsIntegral A B] : HeightOneSpectrum A where
  asIdeal := w.asIdeal.under A
  isPrime := .under A w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

instance [Algebra.IsIntegral A B] : w.asIdeal.LiesOver (w.under A).asIdeal := ⟨rfl⟩

variable [IsFractionRing B L] [NoZeroSMulDivisors A B]
    [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower (WithVal (v.valuation K)) (v.adicCompletion K) (w.adicCompletion L)]

instance [w.asIdeal.LiesOver v.asIdeal] :
    (Valued.v : Valuation (v.adicCompletion K) _).HasExtension
      (Valued.v : Valuation (w.adicCompletion L) _) where
  val_isEquiv_comap := by
    simp only [Valuation.isEquiv_iff_val_eq_one, Valuation.comap_apply, ← valued_liesOver]
    intro x
    exact ⟨by simp_all, fun h ↦ by
      grind [pow_eq_one_iff, ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot]⟩

noncomputable
instance instAlgebraLiesOver [IsFractionRing B L] [NoZeroSMulDivisors A B]
    [w.asIdeal.LiesOver v.asIdeal] :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  Valuation.HasExtension.instAlgebra_valuationSubring _ _

instance [IsFractionRing B L] [NoZeroSMulDivisors A B] [w.asIdeal.LiesOver v.asIdeal] :
   IsLocalHom (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) :=
  Valuation.HasExtension.instIsLocalHomValuationSubring _ _

-- noncomputable
-- instance [IsFractionRing B L] [NoZeroSMulDivisors A B]
--     [w.asIdeal.LiesOver v.asIdeal] :
--     Algebra (v.adicCompletionIntegers K) (w.adicCompletion L) :=
--   Algebra.compHom _ (algebraMap _ (w.adicCompletionIntegers L))

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

open NumberField.FinitePlace NumberField.RingOfIntegers
  NumberField.RingOfIntegers.HeightOneSpectrum
open scoped NumberField Valued

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower (WithVal (v.valuation K)) (v.adicCompletion K) (w.adicCompletion L)]
-- lemma equivHeightOneSpectrum_symm_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
--     (equivHeightOneSpectrum.symm v) x = ‖embedding v x‖ := rfl

-- open Ideal in
-- lemma embedding_mul_absNorm (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 (WithVal (v.valuation K))}
--     (h_x_nezero : x ≠ 0) : ‖embedding v x‖ * absNorm (v.maxPowDividing (span {x})) = 1 := by
--   rw [maxPowDividing, map_pow, Nat.cast_pow, norm_def, adicAbv_def,
--     WithZeroMulInt.toNNReal_neg_apply _
--       ((v.valuation K).ne_zero_iff.mpr (coe_ne_zero_iff.mpr h_x_nezero))]
--   push_cast
--   rw [← zpow_natCast, ← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_absNorm_nnreal v)).ne']
--   norm_cast
--   rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_absNorm_nnreal v).ne')]
--   simp [valuation_of_algebraMap, intValuation_if_neg, h_x_nezero]

open NumberField

open scoped TensorProduct in
instance [w.asIdeal.LiesOver v.asIdeal] :
    Module.Finite (v.adicCompletion K) (w.adicCompletion L) := by
  let Lw := w.adicCompletion L
  let Kᵥ := v.adicCompletion K
  let Φ : Kᵥ ⊗[ℚ] L →ₗ[Kᵥ] Lw :=
    Algebra.TensorProduct.lift (Algebra.algHom Kᵥ Kᵥ Lw) (Algebra.algHom ℚ L Lw)
      (fun x y ↦ mul_comm ..) |>.toLinearMap
  -- Φ has closed image
  have hclosed : IsClosed (Φ.range : Set Lw) :=
    (LinearMap.range Φ).closed_of_finiteDimensional
  -- Φ has dense range
  have h_dense : DenseRange Φ := by
    have hss : Set.range (algebraMap L Lw) ⊆ LinearMap.range Φ := by
      rintro z ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ[ℚ] x, by simp [Φ, Algebra.algHom]⟩
    apply UniformSpace.Completion.denseRange_coe.mono hss
  -- thus the linear map Φ is surjective since its range is closed and dense
  have hsurj : Function.Surjective Φ := by
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← hclosed.closure_eq]
    exact h_dense.closure_range
  exact Module.Finite.of_surjective _ hsurj

instance : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K _)

-- instance [w.asIdeal.LiesOver v.asIdeal] :
--     Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) :=
--   inferInstance

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
    simp only [norm_zero, Nat.cast_mul, mul_inv_rev]
    rw [← mul_inv, Real.rpow_inv_eq le_rfl le_rfl
      (by rw [← Nat.cast_mul, Nat.cast_ne_zero]; exact inertiaDeg_mul_ramificationIdx_ne_zero v w),
      ← Nat.cast_mul, Real.rpow_natCast, zero_pow]
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
    rw [Algebra.smul_def]
    simp only [norm_mul,
      Nat.cast_mul, mul_inv_rev, norm_nonneg, Real.mul_rpow, mul_eq_mul_right_iff]
    left
    rw [← mul_inv, Real.rpow_inv_eq (norm_nonneg _) (norm_nonneg _)
      (by rw [← Nat.cast_mul, Nat.cast_ne_zero]; exact inertiaDeg_mul_ramificationIdx_ne_zero v w)]
    simp only [instNormedFieldValuedAdicCompletion]
    change _ = (toNNReal (absNorm_ne_zero v) (Valued.v a) : ℝ) ^ _
    change (toNNReal (absNorm_ne_zero w) (Valued.v (algebraMap _ (w.adicCompletion L) a)) : ℝ) = _
    rw [← Nat.cast_mul, Real.rpow_natCast, ← NNReal.coe_pow, NNReal.coe_inj, mul_comm, pow_mul,
      ← map_pow, ← valued_liesOver]
    simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, pow_eq_zero_iff', map_eq_zero,
      ne_eq, dite_pow]
    rw [absNorm_eq_pow_inertiaDeg_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot,
      zero_pow <| Ideal.inertiaDeg_ne_zero _ _]
    split_ifs
    · rfl
    · simp [NNReal.zpow_pow_comm]

instance instIsIntegral [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsIntegral (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) where
  isIntegral x := by
    simp only [IsIntegral, RingHom.IsIntegralElem]
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
          simp only [IsPowMul, f]
          intro a n hn
          change ‖a ^ n‖ ^ (_ : ℝ)⁻¹ = (‖a‖ ^ (_ : ℝ)⁻¹) ^ n
          simp [Real.rpow_pow_comm]
        simpa [f] using f.ext_iff.1 (spectralNorm_unique hf) x
      rw [← hnorm]
      simp only [AddSubgroupClass.coe_norm, ge_iff_le]
      apply Real.rpow_le_one (by simp) (Valued.toNormedField.norm_le_one_iff.mpr this)
        (by simp)
    set p : Polynomial (v.adicCompletionIntegers K) :=
      q.int (v.adicCompletionIntegers K).toSubring (by simpa using hq)
    use p
    rw [Polynomial.int_monic_iff]
    refine ⟨minpoly.monic (Algebra.IsAlgebraic.isAlgebraic _).isIntegral, ?_⟩
    simp only [p]
    have := Polynomial.int_eval₂_eq (v.adicCompletionIntegers K).toSubring q
      (by simpa using hq) x.1
    rw [minpoly.aeval] at this
    apply_fun (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) using
      IsFractionRing.injective _ _
    simp only [ValuationSubring.algebraMap_apply, ZeroMemClass.coe_zero]
    simp only [← this, ← ValuationSubring.subtype_apply, Polynomial.eval₂_def, Polynomial.sum_def,
      map_sum]
    apply Finset.sum_congr rfl fun e _ ↦ ?_
    simp only [ValuationSubring.subtype_apply, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      mul_eq_mul_right_iff, pow_eq_zero_iff', ZeroMemClass.coe_eq_zero, ne_eq]
    --rw [← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    left
    congr

instance [w.asIdeal.LiesOver v.asIdeal] :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) :=
  -- takes too long to synthesize on its own
  let _ : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
    instIsIntegral _ _
  IsIntegralClosure.of_isIntegrallyClosed (w.adicCompletionIntegers L)
    (v.adicCompletionIntegers K) (w.adicCompletion L)

instance instFiniteIntegers [w.asIdeal.LiesOver v.asIdeal] :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  IsIntegralClosure.finite _ (v.adicCompletion K) (w.adicCompletion L) _

instance : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))

namespace LiesOver

open UniformSpace.Completion

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Algebra A B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A] [Algebra A L]
    [Algebra K L] [IsDedekindDomain B] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing B L] [NoZeroSMulDivisors A B]
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

noncomputable scoped instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  UniformSpace.Completion.mapRingHom _ uniformContinuous_algebraMap.continuous |>.toAlgebra

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := (UniformSpace.Completion.continuous_map.comp (by fun_prop)).mul (by fun_prop)

scoped instance :
    IsScalarTower (WithVal (v.valuation K)) (v.adicCompletion K) (w.adicCompletion L) := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [RingHom.algebraMap_toAlgebra]
  rw [algebraMap_def, algebraMap_def]
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

end LiesOver

open scoped LiesOver in
open Valued integer Rat.HeightOneSpectrum IsLocalRing in
instance compact_adicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) where
  isCompact_univ := by
    rw [isCompact_iff_totallyBounded_isComplete]
    refine ⟨?_, completeSpace_iff_isComplete_univ.1 (isClosed_valuationSubring _).completeSpace_coe⟩
    rw [totallyBounded_iff_finite_residueField]
    let 𝔭 := v.under (𝓞 ℚ)
    have h : Finite (ResidueField (𝔭.adicCompletionIntegers ℚ)) :=
      (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.1
        (adicCompletionIntegers.padicIntEquiv 𝔭).toHomeomorph.symm.compactSpace).2.2
    let _ := instFiniteIntegers 𝔭 v
    exact ResidueField.finite_of_finite h (S := v.adicCompletionIntegers K)

end IsDedekindDomain.HeightOneSpectrum
