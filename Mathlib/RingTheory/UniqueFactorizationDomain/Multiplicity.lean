/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Unique factorization and multiplicity

## Main results

* `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`: The multiplicity of an
  irreducible factor of a nonzero element is exactly the number of times the normalized factor
  occurs in the `normalizedFactors`.
-/

public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

theorem WfDvdMonoid.max_power_factor' [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ ≠ 0) (hx : ¬IsUnit x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a := by
  obtain ⟨a, ⟨n, rfl⟩, hm⟩ := wellFounded_dvdNotUnit.has_min
    {a | ∃ n, x ^ n * a = a₀} ⟨a₀, 0, by rw [pow_zero, one_mul]⟩
  refine ⟨n, a, ?_, rfl⟩; rintro ⟨d, rfl⟩
  exact hm d ⟨n + 1, by rw [pow_succ, mul_assoc]⟩
    ⟨(right_ne_zero_of_mul <| right_ne_zero_of_mul h), x, hx, mul_comm _ _⟩

theorem WfDvdMonoid.max_power_factor [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ ≠ 0) (hx : Irreducible x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a :=
  max_power_factor' h hx.not_isUnit

theorem FiniteMultiplicity.of_not_isUnit [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a b : α} (ha : ¬IsUnit a) (hb : b ≠ 0) : FiniteMultiplicity a b := by
  obtain ⟨n, c, ndvd, rfl⟩ := WfDvdMonoid.max_power_factor' hb ha
  exact ⟨n, by rwa [pow_succ, mul_dvd_mul_iff_left (left_ne_zero_of_mul hb)]⟩

theorem FiniteMultiplicity.of_prime_left [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a b : α} (ha : Prime a) (hb : b ≠ 0) : FiniteMultiplicity a b :=
  .of_not_isUnit ha.not_unit hb

theorem Prime.emultiplicity_self [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a : α} (ha : Prime a) : emultiplicity a a = 1 :=
  (FiniteMultiplicity.of_prime_left ha ha.ne_zero).emultiplicity_self

/-- The `emultiplicity` of a prime `p` at another prime `q` is `1` if `p` and `q` are
associated, and `0` otherwise. -/
theorem Prime.emultiplicity_prime [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    [DecidableRel ((· ∣ ·) : α → α → Prop)] {p q : α} (hp : Prime p) (hq : Prime q) :
    emultiplicity p q = if Associated p q then 1 else 0 := by
  split_ifs with h
  · obtain ⟨u, rfl⟩ := h
    rw [emultiplicity_mul hp, hp.emultiplicity_self,
      emultiplicity_of_unit_right hp.not_unit, add_zero]
  · rwa [emultiplicity_eq_zero, hp.dvd_prime_iff_associated hq]

/-- An element of a `WfDvdMonoid` is zero iff every power of a fixed prime divides it. -/
theorem WfDvdMonoid.eq_zero_iff_forall_prime_pow_dvd [CommMonoidWithZero α] [IsCancelMulZero α]
    [WfDvdMonoid α] {a p : α} (hp : Prime p) : a = 0 ↔ ∀ n, p ^ n ∣ a := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  by_contra!
  have := FiniteMultiplicity.of_prime_left hp this
  grind

/-- A nonzero element of a `WfDvdMonoid` has finite multiplicity at every prime. -/
theorem WfDvdMonoid.ne_zero_iff_finiteMultiplicity [CommMonoidWithZero α] [IsCancelMulZero α]
    [WfDvdMonoid α] {a p : α} (hp : Prime p) : a ≠ 0 ↔ FiniteMultiplicity p a := by
  convert (WfDvdMonoid.eq_zero_iff_forall_prime_pow_dvd hp).not
  rw [FiniteMultiplicity, not_forall]
  constructor
  · grind
  · intro ⟨n, hn⟩
    have hn' : 1 ≤ n := by
      contrapose! hn
      simp [Nat.lt_one_iff.mp hn, pow_zero]
    refine ⟨n - 1, by rwa [Nat.sub_add_cancel hn']⟩

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

section multiplicity

variable [NormalizationMonoid R]

open Multiset

theorem le_emultiplicity_iff_replicate_le_normalizedFactors {a b : R} {n : ℕ} (ha : Irreducible a)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n (normalize a) ≤ normalizedFactors b := by
  rw [← pow_dvd_iff_le_emultiplicity]
  revert b
  induction n with
  | zero => simp
  | succ n ih => ?_
  intro b hb
  constructor
  · rintro ⟨c, rfl⟩
    rw [Ne, pow_succ', mul_assoc, mul_eq_zero, not_or] at hb
    rw [pow_succ', mul_assoc, normalizedFactors_mul hb.1 hb.2, replicate_succ,
      normalizedFactors_irreducible ha, singleton_add, cons_le_cons_iff, ← ih hb.2]
    apply Dvd.intro _ rfl
  · rw [Multiset.le_iff_exists_add]
    rintro ⟨u, hu⟩
    rw [← (prod_normalizedFactors hb).dvd_iff_dvd_right, hu, prod_add, prod_replicate]
    exact (Associated.pow_pow <| associated_normalize a).dvd.trans (Dvd.intro u.prod rfl)

variable [DecidableEq R]

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalizedFactors`.

For a version using `multiplicity`, see `multiplicity_eq_count_normalizedFactors`.

See also `count_normalizedFactors_eq` which expands the definition of `multiplicity`
to produce a specification for `count (normalizedFactors _) _`..
-/
theorem emultiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b ≠ 0) :
    emultiplicity a b = (normalizedFactors b).count (normalize a) := by
  apply le_antisymm
  · apply Order.le_of_lt_add_one
    rw [← Nat.cast_one, ← Nat.cast_add, lt_iff_not_ge,
      le_emultiplicity_iff_replicate_le_normalizedFactors ha hb, ← le_count_iff_replicate_le]
    simp
  rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb, ← le_count_iff_replicate_le]

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalizedFactors`.

For a version using `emultiplicity`, see `emultiplicity_eq_count_normalizedFactors`. -/
theorem multiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b ≠ 0) :
    multiplicity a b = (normalizedFactors b).count (normalize a) := by
  have := emultiplicity_eq_count_normalizedFactors ha hb
  rwa [(finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity,
    ENat.coe_inj] at this

/-- The number of times an irreducible factor `p` appears in `normalizedFactors x` is defined by
the number of times it divides `x`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplicity p x`.
-/
theorem count_normalizedFactors_eq {p x : R} (hp : Irreducible p) (hnorm : normalize p = p) {n : ℕ}
    (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  by_cases hx0 : x = 0
  · simp [hx0] at hlt
  apply Nat.cast_injective (R := ℕ∞)
  convert! (emultiplicity_eq_count_normalizedFactors hp hx0).symm
  · exact hnorm.symm
  exact (emultiplicity_eq_coe.mpr ⟨hle, hlt⟩).symm

/-- The number of times an irreducible factor `p` appears in `normalizedFactors x` is defined by
the number of times it divides `x`. This is a slightly more general version of
`UniqueFactorizationMonoid.count_normalizedFactors_eq` that allows `p = 0`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplicity p x`.
-/
theorem count_normalizedFactors_eq' {p x : R} (hp : p = 0 ∨ Irreducible p) (hnorm : normalize p = p)
    {n : ℕ} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_notMem_normalizedFactors _)
    · rw [zero_pow (Nat.succ_ne_zero _)] at hle hlt
      exact absurd hle hlt
  · exact count_normalizedFactors_eq hp hnorm hle hlt

lemma associated_finprod_pow_count {x : R} (hx : x ≠ 0) :
    Associated (∏ᶠ p : R, p ^ (normalizedFactors x).count p) x := by
  rw [← Multiset.prod_map_eq_finprod, Multiset.map_id']
  exact prod_normalizedFactors hx

lemma finprod_pow_count_eq_of_subsingleton_units [Subsingleton Rˣ] {x : R} (hx : x ≠ 0) :
    ∏ᶠ p : R, p ^ (normalizedFactors x).count p = x :=
  associated_iff_eq.mp <| associated_finprod_pow_count hx

end multiplicity

lemma dvd_iff_emultiplicity_le {a b : R} (ha : a ≠ 0) :
    a ∣ b ↔ ∀ p : R, Prime p → emultiplicity p a ≤ emultiplicity p b := by
  classical
  refine ⟨fun h _ _ ↦ emultiplicity_le_emultiplicity_of_dvd_right h, fun h ↦ ?_⟩
  by_cases hb : b = 0
  · simp_all
  letI : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha hb, Multiset.le_iff_count]
  intro q
  by_cases hq : q ∈ normalizedFactors a
  · have hqprime : Prime q := prime_of_normalized_factor q hq
    have h1 := emultiplicity_eq_count_normalizedFactors hqprime.irreducible ha
    have h2 := emultiplicity_eq_count_normalizedFactors hqprime.irreducible hb
    rw [normalize_normalized_factor q hq] at h1 h2
    simpa [h1, h2] using h q hqprime
  · simp [Multiset.count_eq_zero_of_notMem hq]

/-- Two nonzero elements of a `UniqueFactorizationMonoid` are associated iff they have the
same `emultiplicity` at every prime. -/
lemma associated_iff_emultiplicity_eq {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    Associated a b ↔ ∀ p : R, Prime p → emultiplicity p a = emultiplicity p b := by
  rw [← dvd_dvd_iff_associated, dvd_iff_emultiplicity_le ha, dvd_iff_emultiplicity_le hb,
    ← forall₂_and]
  simp_rw [le_antisymm_iff]

/-- Version of `associated_iff_emultiplicity_eq` without the nonzero hypotheses, at the cost of
fixing a prime `p` (used to detect whether `a` or `b` vanishes). -/
lemma associated_iff_emultiplicity_eq' (a b : R) {p : R} (hp : Prime p) :
    Associated a b ↔ ∀ p : R, Prime p → emultiplicity p a = emultiplicity p b := by
  by_cases ha : a = 0
  · rw [ha, Associated.comm, associated_zero_iff_eq_zero]
    refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
    rw [WfDvdMonoid.eq_zero_iff_forall_prime_pow_dvd hp]
    have h := h p hp
    simp only [emultiplicity_zero] at h
    exact fun n ↦ by rw [pow_dvd_iff_le_emultiplicity, ← h]; exact le_top
  by_cases hb : b = 0
  · rw [hb, associated_zero_iff_eq_zero]
    refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
    rw [WfDvdMonoid.eq_zero_iff_forall_prime_pow_dvd hp]
    have h := h p hp
    simp only [emultiplicity_zero] at h
    exact fun n ↦ by rw [pow_dvd_iff_le_emultiplicity, h]; exact le_top
  exact associated_iff_emultiplicity_eq ha hb

/-- In a `UniqueFactorizationMonoid` with a unique unit and infinitely many elements (e.g. the
ring of integers of a number field), two elements are equal iff they have the same
`emultiplicity` at every prime. -/
lemma eq_iff_emultiplicity_eq [Subsingleton Rˣ] [Infinite R] {a b : R} :
    a = b ↔ ∀ p : R, Prime p → emultiplicity p a = emultiplicity p b := by
  obtain ⟨p, hp⟩ : ∃ p : R, Prime p := by
    rw [exists_prime_iff]
    obtain ⟨p, h⟩ := Set.Finite.exists_notMem (Set.toFinite ({0, 1} : Set R))
    refine ⟨p, by grind, ?_⟩
    by_contra! hp
    lift p to Rˣ using hp
    simp [Subsingleton.elim p 1] at h
  rw [← associated_iff_eq, associated_iff_emultiplicity_eq' _ _ hp]

lemma pow_dvd_pow_iff_dvd {a b : R} {n : ℕ} (hn : n ≠ 0) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  by_cases ha : a = 0
  · simp [ha, hn]
  refine ⟨?_, fun h ↦ pow_dvd_pow_of_dvd h n⟩
  rw [dvd_iff_emultiplicity_le (pow_ne_zero n ha), dvd_iff_emultiplicity_le ha]
  intro H p hp
  have := H p hp
  rwa [emultiplicity_pow hp, emultiplicity_pow hp,
    ENat.mul_le_mul_left_iff (by exact_mod_cast hn) (ENat.coe_ne_top _)] at this

@[fun_prop]
lemma hasFiniteMulSupport_fun_pow_multiplicity {α M : Type*} [CommMonoid M] [Subsingleton Rˣ]
    (f : α → M) {g : α → R} (hgi : g.Injective) (hg : ∀ s, Irreducible (g s)) {r : R} (hr : r ≠ 0) :
    (fun s : α ↦ f s ^ multiplicity (g s) r).HasFiniteMulSupport := by
  classical
  simp only [multiplicity_eq_count_normalizedFactors (hg _) hr, normalize_eq]
  fun_prop

end UniqueFactorizationMonoid
