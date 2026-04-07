/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Unique factorization and multiplicity

## Main results

* `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`: The multiplicity of an
  irreducible factor of a nonzero element is exactly the number of times the normalized factor
  occurs in the `normalizedFactors`.
-/

public section

assert_not_exists Field

local infixl:50 " ~ᵤ " => Associated

section

variable {α : Type*} [CommMonoidWithZero α] [WfDvdMonoid α]

theorem WfDvdMonoid.max_power_factor' {a₀ x : α} (h : a₀ ≠ 0) (hx : ¬IsUnit x) :
    ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a := by
  obtain ⟨a, ⟨n, rfl⟩, hm⟩ := wellFounded_dvdNotUnit.has_min
    {a | ∃ n, x ^ n * a = a₀} ⟨a₀, 0, by rw [pow_zero, one_mul]⟩
  refine ⟨n, a, ?_, rfl⟩; rintro ⟨d, rfl⟩
  exact hm d ⟨n + 1, by rw [pow_succ, mul_assoc]⟩
    ⟨(right_ne_zero_of_mul <| right_ne_zero_of_mul h), x, hx, mul_comm _ _⟩

theorem WfDvdMonoid.max_power_factor {a₀ x : α} (h : a₀ ≠ 0) (hx : Irreducible x) :
    ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a :=
  max_power_factor' h hx.not_isUnit

variable [IsCancelMulZero α]

theorem FiniteMultiplicity.of_not_isUnit {a b : α} (ha : ¬IsUnit a) (hb : b ≠ 0) :
    FiniteMultiplicity a b := by
  obtain ⟨n, c, ndvd, rfl⟩ := WfDvdMonoid.max_power_factor' hb ha
  exact ⟨n, by rwa [pow_succ, mul_dvd_mul_iff_left (left_ne_zero_of_mul hb)]⟩

theorem FiniteMultiplicity.of_prime_left {a b : α} (ha : Prime a) (hb : b ≠ 0) :
    FiniteMultiplicity a b :=
  .of_not_isUnit ha.not_unit hb

theorem WfDvdMonoid.max_power_factor_of_finset (b : α) (hbI : Irreducible b)
    {ι : Type*} (s : Finset ι) (hsNe : s.Nonempty) (f : ι → α) (hNe0 : ∀ x ∈ s, f x ≠ 0) :
    ∃ (n : ℕ), (∀ i ∈ s, b ^ n ∣ f i) ∧ ∃ j ∈ s, ¬ (b ^ (n + 1) ∣ f j) := by
  let σ : Finset ℕ := s.image (fun x ↦ multiplicity b (f x))
  have hσ : σ.Nonempty := by simp [σ, Finset.image_nonempty, hsNe]
  use (σ.min' hσ)
  constructor
  · intro i hi
    apply (pow_dvd_pow _ _).trans (_ : b ^ (multiplicity b (f i)) ∣ f i) <;>
      aesop (add safe Finset.min'_le) -- can unfold this aesop to make it fast
  obtain ⟨j, hmem, hj⟩ := by simpa [σ] using Finset.min'_mem σ hσ
  use j, hmem; simp only [← hj, σ]; clear hj
  aesop (add safe [FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt,
    FiniteMultiplicity.of_not_isUnit, Irreducible.not_isUnit]) (erase Aesop.BuiltinRules.not_intro)

/--
Given a finitely supported function `f : ι →₀ α` we can factor the biggest
power of some irreducible `b : α` out of `f`. -/
theorem WfDvdMonoid.max_power_factor_of_finsupp (b : α) (hbI : Irreducible b)
    {ι : Type*} (f : ι →₀ α) (h0 : f ≠ 0) :
    ∃ (n : ℕ), (∀ i , b ^ n ∣ f i) ∧ ∃ j ∈ f.support, ¬ (b ^ (n + 1) ∣ f j) := by
  have ⟨n, h1, h2⟩ := max_power_factor_of_finset b hbI f.support (by simp [*]) f (by simp)
  refine ⟨n, fun i ↦ ?_, h2⟩
  by_cases hi : i ∈ f.support <;> aesop

/--
Given a finitely supported function `f : ι →₀ α` we can factor the biggest
power of some irreducible `b : α` out of `f`.

This is a variant of `WfDvdMonoid.max_power_factor_of_finsupp` where the function obtained by
dividing by `b ^ n` is explicit. -/
theorem WfDvdMonoid.max_power_factor_of_finsupp'
    {ι : Type*} (b : α) (hbI : Irreducible b) (f : ι →₀ α) (h0 : f ≠ 0) :
    ∃ (n : ℕ) (f' : ι →₀ α), f' ≠ 0 ∧ f'.support = f.support
      ∧ (∀ i, f i = b ^ n * f' i) ∧ ∃ j ∈ f'.support, ¬ (b ∣ f' j) := by
  obtain ⟨n, h1, ⟨j, hmem, hj⟩⟩ := max_power_factor_of_finsupp b hbI f h0
  choose! f' hf using h1
  let F : ι →₀ α := ⟨f.support, f', by aesop⟩
  use n, F
  refine ⟨?_, ?_, ?_⟩
  · aesop (add norm Finsupp.ext_iff)
  · aesop
  · simp only [Finsupp.coe_mk, Finsupp.mem_support_iff, ne_eq, F]
    use hf, j
    refine ⟨by aesop, ?_⟩
    replace hf := hf j
    contrapose! hj
    obtain ⟨w, h⟩ := hj
    simp_all [← mul_assoc, pow_succ]

end

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
  convert (emultiplicity_eq_count_normalizedFactors hp hx0).symm
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

end UniqueFactorizationMonoid
