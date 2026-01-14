/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Multiplicative maps on unique factorization domains

## Main results
* `UniqueFactorizationMonoid.induction_on_coprime`: if `P` holds for `0`, units and powers of
  primes, and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`, then `P` holds on all `a : α`.
* `UniqueFactorizationMonoid.multiplicative_of_coprime`: if `f` maps `p ^ i` to `(f p) ^ i` for
  primes `p`, and `f` is multiplicative on coprime elements, then `f` is multiplicative everywhere.
-/

assert_not_exists Field

variable {α : Type*}

namespace UniqueFactorizationMonoid

variable {R : Type*} [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

section Multiplicative

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]
variable {β : Type*} [CancelCommMonoidWithZero β]

theorem prime_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s : Finset α} (i : α → ℕ) (p : α)
    (hps : p ∉ s) (is_prime : ∀ q ∈ insert p s, Prime q)
    (is_coprime : ∀ᵉ (q ∈ insert p s) (q' ∈ insert p s), q ∣ q' → q = q') :
    IsRelPrime (p ^ i p) (∏ p' ∈ s, p' ^ i p') := by
  have hp := is_prime _ (Finset.mem_insert_self _ _)
  refine (isRelPrime_iff_no_prime_factors <| pow_ne_zero _ hp.ne_zero).mpr ?_
  intro d hdp hdprod hd
  apply hps
  replace hdp := hd.dvd_of_dvd_pow hdp
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod
  obtain ⟨q, q_mem, rfl⟩ := Multiset.mem_map.mp q_mem'
  replace hdq := hd.dvd_of_dvd_pow hdq
  have : p ∣ q := dvd_trans (hd.irreducible.dvd_symm hp.irreducible hdp) hdq
  convert q_mem using 0
  rw [Finset.mem_val,
    is_coprime _ (Finset.mem_insert_self p s) _ (Finset.mem_insert_of_mem q_mem) this]

/-- If `P` holds for units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on a product of powers of distinct primes. -/
@[elab_as_elim]
theorem induction_on_prime_power {P : α → Prop} (s : Finset α) (i : α → ℕ)
    (is_prime : ∀ p ∈ s, Prime p) (is_coprime : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q)
    (h1 : ∀ {x}, IsUnit x → P x) (hpr : ∀ {p} (i : ℕ), Prime p → P (p ^ i))
    (hcp : ∀ {x y}, IsRelPrime x y → P x → P y → P (x * y)) :
    P (∏ p ∈ s, p ^ i p) := by
  letI := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p f' hpf' ih =>
    rw [Finset.prod_insert hpf']
    exact
      hcp (prime_pow_coprime_prod_of_coprime_insert i p hpf' is_prime is_coprime)
        (hpr (i p) (is_prime _ (Finset.mem_insert_self _ _)))
        (ih (fun q hq => is_prime _ (Finset.mem_insert_of_mem hq)) fun q hq q' hq' =>
          is_coprime _ (Finset.mem_insert_of_mem hq) _ (Finset.mem_insert_of_mem hq'))

/-- If `P` holds for `0`, units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on all `a : α`. -/
@[elab_as_elim]
theorem induction_on_coprime {P : α → Prop} (a : α) (h0 : P 0) (h1 : ∀ {x}, IsUnit x → P x)
    (hpr : ∀ {p} (i : ℕ), Prime p → P (p ^ i))
    (hcp : ∀ {x y}, IsRelPrime x y → P x → P y → P (x * y)) : P a := by
  letI := Classical.decEq α
  have P_of_associated : ∀ {x y}, Associated x y → P x → P y := by
    rintro x y ⟨u, rfl⟩ hx
    exact hcp (fun p _ hpx => isUnit_of_dvd_unit hpx u.isUnit) hx (h1 u.isUnit)
  by_cases ha0 : a = 0
  · rwa [ha0]
  haveI : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  letI : NormalizationMonoid α := UniqueFactorizationMonoid.normalizationMonoid
  refine P_of_associated (prod_normalizedFactors ha0) ?_
  rw [← (normalizedFactors a).map_id, Finset.prod_multiset_map_count]
  refine induction_on_prime_power _ _ ?_ ?_ @h1 @hpr @hcp <;> simp only [Multiset.mem_toFinset]
  · apply prime_of_normalized_factor
  · apply normalizedFactors_eq_of_dvd

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative on all products of primes. -/
theorem multiplicative_prime_power {f : α → β} (s : Finset α) (i j : α → ℕ)
    (is_prime : ∀ p ∈ s, Prime p) (is_coprime : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q)
    (h1 : ∀ {x y}, IsUnit y → f (x * y) = f x * f y)
    (hpr : ∀ {p} (i : ℕ), Prime p → f (p ^ i) = f p ^ i)
    (hcp : ∀ {x y}, IsRelPrime x y → f (x * y) = f x * f y) :
    f (∏ p ∈ s, p ^ (i p + j p)) = f (∏ p ∈ s, p ^ i p) * f (∏ p ∈ s, p ^ j p) := by
  letI := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p s hps ih =>
    have hpr_p := is_prime _ (Finset.mem_insert_self _ _)
    have hpr_s : ∀ p ∈ s, Prime p := fun p hp => is_prime _ (Finset.mem_insert_of_mem hp)
    have hcp_p := fun i => prime_pow_coprime_prod_of_coprime_insert i p hps is_prime is_coprime
    have hcp_s : ∀ᵉ (p ∈ s) (q ∈ s), p ∣ q → p = q := fun p hp q hq =>
      is_coprime p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps, Finset.prod_insert hps, Finset.prod_insert hps, hcp (hcp_p _),
      hpr _ hpr_p, hcp (hcp_p _), hpr _ hpr_p, hcp (hcp_p (fun p => i p + j p)), hpr _ hpr_p,
      ih hpr_s hcp_s, pow_add, mul_assoc, mul_left_comm (f p ^ j p), mul_assoc]

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative everywhere. -/
theorem multiplicative_of_coprime (f : α → β) (a b : α) (h0 : f 0 = 0)
    (h1 : ∀ {x y}, IsUnit y → f (x * y) = f x * f y)
    (hpr : ∀ {p} (i : ℕ), Prime p → f (p ^ i) = f p ^ i)
    (hcp : ∀ {x y}, IsRelPrime x y → f (x * y) = f x * f y) :
    f (a * b) = f a * f b := by
  letI := Classical.decEq α
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul, h0, zero_mul]
  by_cases hb0 : b = 0
  · rw [hb0, mul_zero, h0, mul_zero]
  by_cases hf1 : f 1 = 0
  · calc
      f (a * b) = f (a * b * 1) := by rw [mul_one]
      _ = 0 := by simp only [h1 isUnit_one, hf1, mul_zero]
      _ = f a * f (b * 1) := by simp only [h1 isUnit_one, hf1, mul_zero]
      _ = f a * f b := by rw [mul_one]
  haveI : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  letI : NormalizationMonoid α := UniqueFactorizationMonoid.normalizationMonoid
  suffices
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ ((normalizedFactors a).count p + (normalizedFactors b).count p)) =
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ (normalizedFactors a).count p) *
      f (∏ p ∈ (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset,
        p ^ (normalizedFactors b).count p) by
    obtain ⟨ua, a_eq⟩ := prod_normalizedFactors ha0
    obtain ⟨ub, b_eq⟩ := prod_normalizedFactors hb0
    rw [← a_eq, ← b_eq, mul_right_comm (Multiset.prod (normalizedFactors a)) ua
        (Multiset.prod (normalizedFactors b) * ub), h1 ua.isUnit, h1 ub.isUnit, h1 ua.isUnit, ←
      mul_assoc, h1 ub.isUnit, mul_right_comm _ (f ua), ← mul_assoc]
    congr
    rw [← (normalizedFactors a).map_id, ← (normalizedFactors b).map_id,
      Finset.prod_multiset_map_count, Finset.prod_multiset_map_count,
      Finset.prod_subset (Finset.subset_union_left (s₂ := (normalizedFactors b).toFinset)),
      Finset.prod_subset (Finset.subset_union_right (s₂ := (normalizedFactors b).toFinset)), ←
      Finset.prod_mul_distrib]
    · simp_rw [id, ← pow_add, this]
    all_goals simp only [Multiset.mem_toFinset]
    · intro p _ hpb
      simp [hpb]
    · intro p _ hpa
      simp [hpa]
  refine multiplicative_prime_power _ _ _ ?_ ?_ @h1 @hpr @hcp
  all_goals simp only [Multiset.mem_toFinset, Finset.mem_union]
  · rintro p (hpa | hpb) <;> apply prime_of_normalized_factor <;> assumption
  · rintro p (hp | hp) q (hq | hq) hdvd <;>
      rw [← normalize_normalized_factor _ hp, ← normalize_normalized_factor _ hq] <;>
      exact
        normalize_eq_normalize hdvd
          ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
            (prime_of_normalized_factor _ hq).irreducible hdvd)

end Multiplicative

end UniqueFactorizationMonoid
