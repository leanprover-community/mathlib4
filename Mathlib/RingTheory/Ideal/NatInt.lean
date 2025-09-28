/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

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

theorem Nat.maximalIdeal_eq_span_two_three : maximalIdeal ℕ = span {2, 3} := by
  refine le_antisymm (fun n h ↦ ?_) (span_le.mpr <| Set.pair_subset (by simp) (by simp))
  obtain lt | lt := (mem_maximalIdeal_iff.mp h).lt_or_gt
  · obtain rfl := lt_one_iff.mp lt; exact zero_mem _
  exact mem_span_pair.mpr <|
    exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le 2 3 n (by simp) (show 2 ≤ n by cutsat)

theorem Nat.one_mem_span_iff {s : Set ℕ} : 1 ∈ span s ↔ 1 ∈ s := by
  rw [← SetLike.mem_coe, ← not_iff_not]
  simp_rw [← Set.mem_compl_iff, ← Set.singleton_subset_iff, Set.subset_compl_comm,
    ← coe_maximalIdeal, SetLike.coe_subset_coe, span_le]

theorem Nat.one_mem_closure_iff {s : Set ℕ} : 1 ∈ AddSubmonoid.closure s ↔ 1 ∈ s := by
  rw [← Submodule.span_nat_eq_addSubmonoidClosure]
  exact one_mem_span_iff

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
  have prime : p.Prime := Nat.prime_iff_not_exists_mul_eq.mpr <| .intro (by cutsat)
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
    (Nat.lt_pow_self (show 1 < n by cutsat)).le
  exact h.mem_of_pow_mem _ (eq ▸ add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hq))

theorem Ideal.map_comap_natCastRingHom_int {I : Ideal ℤ} :
    (I.comap (Nat.castRingHom ℤ)).map (Nat.castRingHom ℤ) = I :=
  map_comap_le.antisymm fun n hn ↦ n.sign_mul_natAbs ▸ mul_mem_left _ _ <| mem_map_of_mem _
    (mem_comap.mpr <| show (n.natAbs : ℤ) ∈ I from n.sign_mul_self ▸ mul_mem_left _ _ hn)

theorem Ideal.isPrime_int_iff {P : Ideal ℤ} :
    P.IsPrime ↔ P = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ P = span {(p : ℤ)} :=
  isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors.trans <| or_congr_right
  ⟨fun ⟨p, hp, eq⟩ ↦ ⟨_, Int.prime_iff_natAbs_prime.mp hp, eq.trans
    p.span_natAbs.symm⟩, fun ⟨_p, hp, eq⟩ ↦ ⟨_, Nat.prime_iff_prime_int.mp hp, eq⟩⟩

theorem ringKrullDim_nat : ringKrullDim ℕ = 2 := by
  refine le_antisymm (iSup_le fun s ↦ le_of_not_gt fun hs ↦ ?_) ?_
  · replace hs : 2 < s.length := ENat.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hs)
    let s := s.take ⟨3, by cutsat⟩
    have : NeZero s.length := ⟨three_ne_zero⟩
    have h1 : ⊥ < (s 1).asIdeal := bot_le.trans_lt (s.step 0)
    obtain hmax | ⟨p, hp, hsp⟩ := (Ideal.isPrime_nat_iff.mp (s 1).2).resolve_left h1.ne'
    · exact (le_maximalIdeal_of_isPrime (s 2).asIdeal).not_gt (hmax.symm.trans_lt (s.step 1))
    obtain hmax | ⟨q, hq, hsq⟩ :=
      (Ideal.isPrime_nat_iff.mp (s 2).2).resolve_left (h1.trans (s.step 1)).ne'
    · exact (le_maximalIdeal_of_isPrime (s 3).asIdeal).not_gt (hmax.symm.trans_lt (s.step 2))
    · exact hq.not_isUnit <| (Ideal.span_singleton_lt_span_singleton.mp
        ((hsp.symm.trans_lt (s.step 1)).trans_eq hsq)).isUnit_of_irreducible_right hp
  · refine le_iSup_of_le ⟨2, ![⊥, ⟨_, (span_singleton_prime two_ne_zero).mpr <| Nat.prime_iff.mp
      Nat.prime_two⟩, ⟨_, (maximalIdeal.isMaximal ℕ).isPrime⟩], fun i ↦ ?_⟩ le_rfl
    fin_cases i
    · exact bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr two_ne_zero)
    · simp_rw [Nat.maximalIdeal_eq_span_two_three]
      exact SetLike.lt_iff_le_and_exists.mpr ⟨Ideal.span_mono (by simp),
        3, Ideal.subset_span (by simp), Ideal.mem_span_singleton.not.mpr <| by simp⟩
