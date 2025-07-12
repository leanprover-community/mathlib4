/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Prime ideals in ℕ and ℤ

## Main results

* `Ideal.isPrime_nat_iff`: the prime ideals in ℕ are ⟨0⟩, ⟨p⟩ (for prime `p`), and ⟨2, 3⟩ = {1}ᶜ.
  The proof follows https://math.stackexchange.com/a/4224486.

* `Ideal.isPrime_int_iff` : the prime ideals in ℤ are ⟨0⟩ and ⟨p⟩ (for prime `p`).
-/

/-- The natural numbers form a local semiring. -/
instance : IsLocalRing ℕ where
  isUnit_or_isUnit_of_add_one {a b} hab := by
    have h : a = 1 ∨ b = 1 := by omega
    apply h.imp <;> simp +contextual

open IsLocalRing Ideal

theorem Nat.mem_maximalIdeal_iff {n : ℕ} : n ∈ maximalIdeal ℕ ↔ n ≠ 1 := by simp

theorem Nat.coe_maximalIdeal : (maximalIdeal ℕ : Set ℕ) = {1}ᶜ := by ext; simp

theorem Nat.maximalIdeal_eq_span_two_three : maximalIdeal ℕ = .span {2, 3} := by
  refine le_antisymm (fun n h ↦ ?_) (span_le.mpr <| Set.pair_subset (by simp) (by simp))
  obtain lt | lt := (mem_maximalIdeal_iff.mp h).lt_or_gt
  · obtain rfl := lt_one_iff.mp lt; exact zero_mem _
  exact mem_span_pair.mpr <|
    exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le 2 3 n (by simp) (show 2 ≤ n by omega)

theorem Ideal.isPrime_nat_iff {P : Ideal ℕ} :
    P.IsPrime ↔ P = ⊥ ∨ P = maximalIdeal ℕ ∨ ∃ p : ℕ, p.Prime ∧ P = span {p} := by
  refine .symm ⟨?_, fun h ↦ or_iff_not_imp_left.mpr fun h0 ↦ or_iff_not_imp_right.mpr fun hsp ↦
    (le_maximalIdeal h.ne_top).antisymm fun n hn ↦ ?_⟩
  · rintro (rfl | rfl | ⟨p, hp, rfl⟩)
    · exact bot_prime
    · exact (maximalIdeal.isMaximal ℕ).isPrime
    · rwa [span_singleton_prime (by simp [hp.ne_zero]), ← Nat.prime_iff]
  rw [← le_bot_iff, SetLike.not_le_iff_exists] at h0
  classical
  let p := Nat.find h0
  have ⟨(hp : p ∈ P), (hp0 : p ≠ 0)⟩ := Nat.find_spec h0
  have : p ≠ 1 := ne_of_mem_of_not_mem hp P.one_notMem
  have prime : p.Prime := Nat.prime_iff_not_exists_mul_eq.mpr <| .intro (by omega)
    fun ⟨m, n, hm, hn, eq⟩ ↦ have := mul_ne_zero_iff.mp (eq ▸ hp0)
    (h.mem_or_mem (eq ▸ hp)).elim (Nat.find_min h0 hm ⟨·, this.1⟩) (Nat.find_min h0 hn ⟨·, this.2⟩)
  push_neg at hsp
  have ⟨q, hq, hqp⟩ := SetLike.exists_of_lt
    ((P.span_singleton_le_iff_mem.mpr hp).lt_of_ne (hsp p prime).symm)
  obtain rfl | hn1 := eq_or_ne n 0
  · exact Ideal.zero_mem _
  have : n ≠ 1 := Nat.mem_maximalIdeal_iff.mp hn
  have ⟨a, b, eq⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le p q _
    (by simp [prime.coprime_iff_not_dvd.mpr (Ideal.mem_span_singleton.not.mp hqp)])
    (Nat.lt_pow_self (show 1 < n by omega)).le
  exact h.mem_of_pow_mem _ (eq ▸ add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hq))

theorem Ideal.map_comap_natCastRingHom_int {I : Ideal ℤ} :
    (I.comap (Nat.castRingHom ℤ)).map (Nat.castRingHom ℤ) = I :=
  map_comap_le.antisymm fun n hn ↦ n.sign_mul_natAbs ▸ mul_mem_left _ _ <| mem_map_of_mem _
    (mem_comap.mpr <| show (n.natAbs : ℤ) ∈ I from n.sign_mul_self ▸ mul_mem_left _ _ hn)

theorem Ideal.isPrime_int_iff {P : Ideal ℤ} :
    P.IsPrime ↔ P = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ P = span {(p : ℤ)} := by
  refine .symm ⟨?_, fun h ↦ ?_⟩
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · exact bot_prime
    rwa [span_singleton_prime (by simp [hp.ne_zero]), ← Nat.prime_iff_prime_int]
  rw [← P.map_comap_natCastRingHom_int]
  obtain hP | hP := isPrime_nat_iff.mp (h.comap (Nat.castRingHom ℤ))
  · exact .inl (by rw [hP, map_bot])
  have ⟨p, hp, hP⟩ := hP.resolve_left fun hP ↦ by
    rw [← P.map_comap_natCastRingHom_int, hP, Nat.maximalIdeal_eq_span_two_three, map_span] at h
    exact h.one_notMem (Set.image_pair .. ▸ mem_span_pair.mpr ⟨-1, 1, rfl⟩)
  exact .inr ⟨p, hp, by rw [hP, map_span, Set.image_singleton, Nat.coe_castRingHom]⟩
