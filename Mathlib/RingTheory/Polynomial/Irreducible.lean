/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Norm

/-!
# Criteria for `X ^ n - C a` to be irreducible

## Main result

- `X_pow_sub_C_irreducible_iff_of_prime`:
  For `n = p` a prime, `X ^ n - C a` is irreducible iff `a` is not a `p`-power.

- `X_pow_sub_C_irreducible_iff_of_prime_pow`:
  For `n = p ^ k` an odd prime power, `X ^ n - C a` is irreducible iff `a` is not a `p`-power.

- `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`:
  For `n` odd, `X ^ n - C a` is irreducible iff `a` is not a `p`-power for all prime `p ∣ n`.

- `X_pow_sub_C_irreducible_iff_of_odd`:
  For `n` odd, `X ^ n - C a` is irreducible iff `a` is not a `d`-power for `d ∣ n` and `d ≠ 1`.

TODO: criteria for even `n`. See [serge_lang_algebra] VI,§9.

-/

universe u

variable {R K : Type u} [CommRing R] [Field K]

open Polynomial IntermediateField

section Irreducible

theorem pow_ne_of_irreducible_X_pow_sub_C {n : ℕ} {a : K}
    (H : Irreducible (X ^ n - C a)) {m : ℕ} (hm : m ∣ n) (hm' : m ≠ 1) (b : K) : b ^ m ≠ a := by
  have hn : n ≠ 0 := fun e ↦ not_irreducible_C
    (1 - a) (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using H)
  obtain ⟨k, rfl⟩ := hm
  rintro rfl
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X ^ k) (C b) m
  rw [mul_comm, pow_mul, map_pow, hq] at H
  have : degree q = 0
  · simpa [isUnit_iff_degree_eq_zero, degree_X_pow_sub_C,
      Nat.pos_iff_ne_zero, (mul_ne_zero_iff.mp hn).2] using H.2 _ q rfl
  apply_fun degree at hq
  simp only [this, ← pow_mul, mul_comm k m, degree_X_pow_sub_C, Nat.pos_iff_ne_zero.mpr hn,
    Nat.pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).2, degree_mul, ← map_pow, add_zero,
    Nat.cast_injective.eq_iff] at hq
  exact hm' ((mul_eq_right₀ (mul_ne_zero_iff.mp hn).2).mp hq)

theorem X_pow_sub_C_irreducible_of_prime {p : ℕ} (hp : p.Prime) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ p - C a) := by
  -- First of all, We may find an irreducible factor `g` of `X ^ p - C a`.
  have : ¬ IsUnit (X ^ p - C a)
  · rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hp.pos, Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor this (X_pow_sub_C_ne_zero hp.pos a)
  -- It suffices to show that `deg g = p`.
  suffices natDegree g = p from (associated_of_dvd_of_natDegree_le hg'
    (X_pow_sub_C_ne_zero hp.pos a) (this.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg
  -- Suppose `deg g ≠ p`.
  by_contra h
  have : Fact (Irreducible g) := ⟨hg⟩
  -- Let `r` be a root of `g`, then `N_K(r) ^ p = N_K(r ^ p) = N_K(a) = a ^ (deg g)`.
  have key : (Algebra.norm K (AdjoinRoot.root g)) ^ p = a ^ g.natDegree
  · have := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hg' (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at this
    rw [← map_pow, this, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap,
      ← finrank_top', ← IntermediateField.adjoin_root_eq_top g,
      IntermediateField.adjoin.finrank,
      AdjoinRoot.minpoly_root hg.ne_zero, natDegree_mul_C]
    · simpa using hg.ne_zero
    · exact AdjoinRoot.isIntegral_root hg.ne_zero
  -- Since `a ^ (deg g)` is a `p`-power, and `p` is coprime to `deg g`, we conclude that `a` is
  -- also a `p`-power, contradicting the hypothesis
  have : p.Coprime (natDegree g) := hp.coprime_iff_not_dvd.mpr (fun e ↦ h (((natDegree_le_of_dvd hg'
    (X_pow_sub_C_ne_zero hp.pos a)).trans_eq natDegree_X_pow_sub_C).antisymm (Nat.le_of_dvd
      (natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_irreducible hg) e)))
  exact ha _ ((pow_mem_range_pow_of_coprime this.symm a).mp ⟨_, key⟩).choose_spec

theorem X_pow_sub_C_irreducible_iff_of_prime {p : ℕ} (hp : p.Prime) {a : K} :
    Irreducible (X ^ p - C a) ↔ ∀ b, b ^ p ≠ a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · dvd_rfl hp.ne_one), X_pow_sub_C_irreducible_of_prime hp⟩

theorem X_pow_mul_sub_C_irreducible
    {n m : ℕ} {a : K} (hm : Irreducible (X ^ m - C a))
    (hn : ∀ (E : Type u) [Field E] [Algebra K E] (x : E) (hx : minpoly K x = X ^ m - C a),
      Irreducible (X ^ n - C (AdjoinSimple.gen K x))) :
    Irreducible (X ^ (n * m) - C a) := by
  have hm' : m ≠ 0
  · rintro rfl
    rw [pow_zero, ← C.map_one, ← map_sub] at hm
    exact not_irreducible_C _ hm
  simpa [pow_mul] using irreducible_comp (monic_X_pow_sub_C a hm') (monic_X_pow n) hm
    (by simpa only [Polynomial.map_pow, map_X] using hn)

-- TODO: generalize to even `n`
theorem X_pow_sub_C_irreducible_of_odd
    {n : ℕ} (hn : Odd n) {a : K} (ha : ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ n - C a) := by
  induction n using induction_on_primes generalizing K a with
  | h₀ => simp at hn
  | h₁ => simpa using irreducible_X_sub_C a
  | h p n hp IH =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mul_right _ _)))
    intro E _ _ x hx
    have : IsIntegral K x := not_not.mp fun h ↦ by
      simpa only [degree_zero, degree_X_pow_sub_C hp.pos,
        WithBot.nat_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
    apply IH (Nat.odd_mul.mp hn).2
    intros q hq hqn b hb
    apply ha q hq (dvd_mul_of_dvd_right hqn p) (Algebra.norm _ b)
    rw [← map_pow, hb, ← adjoin.powerBasis_gen this,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simp [minpoly_gen, hx, hp.ne_zero.symm, (Nat.odd_mul.mp hn).1.neg_pow]

theorem X_pow_sub_C_irreducible_iff_forall_prime_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :=
  ⟨fun e _ hp hpn ↦ pow_ne_of_irreducible_X_pow_sub_C e hpn hp.ne_one,
    X_pow_sub_C_irreducible_of_odd hn⟩

theorem X_pow_sub_C_irreducible_iff_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (∀ d, d ∣ n → d ≠ 1 → ∀ b : K, b ^ d ≠ a) :=
  ⟨fun e _ ↦ pow_ne_of_irreducible_X_pow_sub_C e,
    fun H ↦ X_pow_sub_C_irreducible_of_odd hn fun p hp hpn ↦ (H p hpn hp.ne_one)⟩

-- TODO: generalize to `p = 2`
theorem X_pow_sub_C_irreducible_of_prime_pow
    {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2) (n : ℕ) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ (p ^ n) - C a) := by
  apply X_pow_sub_C_irreducible_of_odd (hp.odd_of_ne_two hp').pow
  intros q hq hq'
  simpa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hq')] using ha

theorem X_pow_sub_C_irreducible_iff_of_prime_pow
    {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2) {n} (hn : n ≠ 0) {a : K} :
    Irreducible (X ^ p ^ n - C a) ↔ ∀ b, b ^ p ≠ a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · (dvd_pow dvd_rfl hn) hp.ne_one),
    X_pow_sub_C_irreducible_of_prime_pow hp hp' n⟩

end Irreducible
