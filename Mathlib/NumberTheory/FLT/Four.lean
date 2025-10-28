/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Fermat's Last Theorem for the case n = 4
There are no non-zero integers `a`, `b` and `c` such that `a ^ 4 + b ^ 4 = c ^ 4`.
-/

assert_not_exists TwoSidedIdeal

noncomputable section

/-- Shorthand for three non-zero integers `a`, `b`, and `c` satisfying `a ^ 4 + b ^ 4 = c ^ 2`.
We will show that no integers satisfy this equation. Clearly Fermat's Last theorem for n = 4
follows. -/
def Fermat42 (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2

namespace Fermat42

theorem comm {a b c : ℤ} : Fermat42 a b c ↔ Fermat42 b a c := by
  delta Fermat42
  rw [add_comm]
  tauto

theorem mul {a b c k : ℤ} (hk0 : k ≠ 0) :
    Fermat42 a b c ↔ Fermat42 (k * a) (k * b) (k ^ 2 * c) := by
  delta Fermat42
  constructor
  · intro f42
    constructor
    · exact mul_ne_zero hk0 f42.1
    constructor
    · exact mul_ne_zero hk0 f42.2.1
    · have H : a ^ 4 + b ^ 4 = c ^ 2 := f42.2.2
      linear_combination k ^ 4 * H
  · intro f42
    constructor
    · exact right_ne_zero_of_mul f42.1
    constructor
    · exact right_ne_zero_of_mul f42.2.1
    apply (mul_right_inj' (pow_ne_zero 4 hk0)).mp
    linear_combination f42.2.2

theorem ne_zero {a b c : ℤ} (h : Fermat42 a b c) : c ≠ 0 := by
  apply ne_zero_pow two_ne_zero _; apply ne_of_gt
  rw [← h.2.2, (by ring : a ^ 4 + b ^ 4 = (a ^ 2) ^ 2 + (b ^ 2) ^ 2)]
  exact
    add_pos (sq_pos_of_ne_zero (pow_ne_zero 2 h.1)) (sq_pos_of_ne_zero (pow_ne_zero 2 h.2.1))

/-- We say a solution to `a ^ 4 + b ^ 4 = c ^ 2` is minimal if there is no other solution with
a smaller `c` (in absolute value). -/
def Minimal (a b c : ℤ) : Prop :=
  Fermat42 a b c ∧ ∀ a1 b1 c1 : ℤ, Fermat42 a1 b1 c1 → Int.natAbs c ≤ Int.natAbs c1

/-- if we have a solution to `a ^ 4 + b ^ 4 = c ^ 2` then there must be a minimal one. -/
theorem exists_minimal {a b c : ℤ} (h : Fermat42 a b c) : ∃ a0 b0 c0, Minimal a0 b0 c0 := by
  classical
  let S : Set ℕ := { n | ∃ s : ℤ × ℤ × ℤ, Fermat42 s.1 s.2.1 s.2.2 ∧ n = Int.natAbs s.2.2 }
  have S_nonempty : S.Nonempty := by
    use Int.natAbs c
    rw [Set.mem_setOf_eq]
    use ⟨a, ⟨b, c⟩⟩
  let m : ℕ := Nat.find S_nonempty
  have m_mem : m ∈ S := Nat.find_spec S_nonempty
  rcases m_mem with ⟨s0, hs0, hs1⟩
  use s0.1, s0.2.1, s0.2.2, hs0
  intro a1 b1 c1 h1
  rw [← hs1]
  apply Nat.find_min'
  use ⟨a1, ⟨b1, c1⟩⟩

/-- a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` must have `a` and `b` coprime. -/
theorem coprime_of_minimal {a b c : ℤ} (h : Minimal a b c) : IsCoprime a b := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a1, rfl⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b1, rfl⟩ := Int.natCast_dvd.mpr hpb
  have hpc : (p : ℤ) ^ 2 ∣ c := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2]
    apply Dvd.intro (a1 ^ 4 + b1 ^ 4)
    ring
  obtain ⟨c1, rfl⟩ := hpc
  have hf : Fermat42 a1 b1 c1 :=
    (Fermat42.mul (Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero hp))).mpr h.1
  apply Nat.le_lt_asymm (h.2 _ _ _ hf)
  rw [Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_pow, Int.natAbs_natCast]
  · exact Nat.one_lt_pow two_ne_zero (Nat.Prime.one_lt hp)
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (ne_zero hf))

/-- We can swap `a` and `b` in a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2`. -/
theorem minimal_comm {a b c : ℤ} : Minimal a b c → Minimal b a c := fun ⟨h1, h2⟩ =>
  ⟨Fermat42.comm.mp h1, h2⟩

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has positive `c`. -/
theorem neg_of_minimal {a b c : ℤ} : Minimal a b c → Minimal a b (-c) := by
  rintro ⟨⟨ha, hb, heq⟩, h2⟩
  constructor
  · apply And.intro ha (And.intro hb _)
    rw [heq]
    exact (neg_sq c).symm
  rwa [Int.natAbs_neg c]

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has `a` odd. -/
theorem exists_odd_minimal {a b c : ℤ} (h : Fermat42 a b c) :
    ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ a0 % 2 = 1 := by
  obtain ⟨a0, b0, c0, hf⟩ := exists_minimal h
  rcases Int.emod_two_eq_zero_or_one a0 with hap | hap
  · rcases Int.emod_two_eq_zero_or_one b0 with hbp | hbp
    · exfalso
      have h1 : 2 ∣ (Int.gcd a0 b0 : ℤ) :=
        Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hap) (Int.dvd_of_emod_eq_zero hbp)
      rw [Int.isCoprime_iff_gcd_eq_one.mp (coprime_of_minimal hf)] at h1
      revert h1
      decide
    · exact ⟨b0, ⟨a0, ⟨c0, minimal_comm hf, hbp⟩⟩⟩
  exact ⟨a0, ⟨b0, ⟨c0, hf, hap⟩⟩⟩

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has
`a` odd and `c` positive. -/
theorem exists_pos_odd_minimal {a b c : ℤ} (h : Fermat42 a b c) :
    ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ a0 % 2 = 1 ∧ 0 < c0 := by
  obtain ⟨a0, b0, c0, hf, hc⟩ := exists_odd_minimal h
  rcases lt_trichotomy 0 c0 with (h1 | h1 | h1)
  · use a0, b0, c0
  · exfalso
    exact ne_zero hf.1 h1.symm
  · use a0, b0, -c0, neg_of_minimal hf, hc
    exact neg_pos.mpr h1

end Fermat42

theorem Int.isCoprime_of_sq_sum {r s : ℤ} (h2 : IsCoprime s r) : IsCoprime (r ^ 2 + s ^ 2) r := by
  rw [sq, sq]
  exact (IsCoprime.mul_left h2 h2).mul_add_left_left r

@[deprecated (since := "2025-01-23")] alias Int.coprime_of_sq_sum := Int.isCoprime_of_sq_sum

theorem Int.isCoprime_of_sq_sum' {r s : ℤ} (h : IsCoprime r s) :
    IsCoprime (r ^ 2 + s ^ 2) (r * s) := by
  apply IsCoprime.mul_right (Int.isCoprime_of_sq_sum (isCoprime_comm.mp h))
  rw [add_comm]; apply Int.isCoprime_of_sq_sum h

@[deprecated (since := "2025-01-23")] alias Int.coprime_of_sq_sum' := Int.isCoprime_of_sq_sum'

namespace Fermat42

-- If we have a solution to a ^ 4 + b ^ 4 = c ^ 2, we can construct a smaller one. This
-- implies there can't be a smallest solution.
theorem not_minimal {a b c : ℤ} (h : Minimal a b c) (ha2 : a % 2 = 1) (hc : 0 < c) : False := by
  -- Use the fact that a ^ 2, b ^ 2, c form a pythagorean triple to obtain m and n such that
  -- a ^ 2 = m ^ 2 - n ^ 2, b ^ 2 = 2 * m * n and c = m ^ 2 + n ^ 2
  -- first the formula:
  have ht : PythagoreanTriple (a ^ 2) (b ^ 2) c := by
    delta PythagoreanTriple
    linear_combination h.1.2.2
  -- coprime requirement:
  have h2 : Int.gcd (a ^ 2) (b ^ 2) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (coprime_of_minimal h).pow
  -- in order to reduce the possibilities we get from the classification of pythagorean triples
  -- it helps if we know the parity of a ^ 2 (and the sign of c):
  have ha22 : a ^ 2 % 2 = 1 := by
    rw [sq, Int.mul_emod, ha2]
    decide
  obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ := ht.coprime_classification' h2 ha22 hc
  -- Now a, n, m form a pythagorean triple and so we can obtain r and s such that
  -- a = r ^ 2 - s ^ 2, n = 2 * r * s and m = r ^ 2 + s ^ 2
  -- formula:
  have htt : PythagoreanTriple a n m := by
    delta PythagoreanTriple
    linear_combination ht1
  -- a and n are coprime, because a ^ 2 = m ^ 2 - n ^ 2 and m and n are coprime.
  have h3 : Int.gcd a n = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    apply @IsCoprime.of_mul_left_left _ _ _ a
    rw [← sq, ht1, (by ring : m ^ 2 - n ^ 2 = m ^ 2 + -n * n)]
    exact (Int.isCoprime_iff_gcd_eq_one.mpr ht4).pow_left.add_mul_right_left (-n)
  -- m is positive because b is non-zero and b ^ 2 = 2 * m * n and we already have 0 ≤ m.
  have hb20 : b ^ 2 ≠ 0 := mt pow_eq_zero h.1.2.1
  have h4 : 0 < m := by
    apply lt_of_le_of_ne ht6
    rintro rfl
    revert hb20
    rw [ht2]
    simp
  obtain ⟨r, s, _, htt2, htt3, htt4, htt5, htt6⟩ := htt.coprime_classification' h3 ha2 h4
  -- Now use the fact that (b / 2) ^ 2 = m * r * s, and m, r and s are pairwise coprime to obtain
  -- i, j and k such that m = i ^ 2, r = j ^ 2 and s = k ^ 2.
  -- m and r * s are coprime because m = r ^ 2 + s ^ 2 and r and s are coprime.
  have hcp : Int.gcd m (r * s) = 1 := by
    rw [htt3]
    exact Int.isCoprime_iff_gcd_eq_one.mp
      (Int.isCoprime_of_sq_sum' (Int.isCoprime_iff_gcd_eq_one.mpr htt4))
  -- b is even because b ^ 2 = 2 * m * n.
  have hb2 : 2 ∣ b := by
    apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
    rw [ht2, mul_assoc]
    exact dvd_mul_right 2 (m * n)
  obtain ⟨b', hb2'⟩ := hb2
  have hs : b' ^ 2 = m * (r * s) := by
    apply (mul_right_inj' (by norm_num : (4 : ℤ) ≠ 0)).mp
    linear_combination (-b - 2 * b') * hb2' + ht2 + 2 * m * htt2
  have hrsz : r * s ≠ 0 := by
    -- because b ^ 2 is not zero and (b / 2) ^ 2 = m * (r * s)
    by_contra hrsz
    revert hb20
    rw [ht2, htt2, mul_assoc, @mul_assoc _ _ _ r s, hrsz]
    simp
  have h2b0 : b' ≠ 0 := by
    apply ne_zero_pow two_ne_zero
    rw [hs]
    apply mul_ne_zero
    · exact ne_of_gt h4
    · exact hrsz
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one hcp hs.symm
  -- use m is positive to exclude m = - i ^ 2
  have hi' : ¬m = -i ^ 2 := by
    by_contra h1
    have hit : -i ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg i)
    rw [← h1] at hit
    apply absurd h4 (not_lt.mpr hit)
  replace hi : m = i ^ 2 := Or.resolve_right hi hi'
  rw [mul_comm] at hs
  rw [Int.gcd_comm] at hcp
  -- obtain d such that r * s = d ^ 2
  obtain ⟨d, hd⟩ := Int.sq_of_gcd_eq_one hcp hs.symm
  -- (b / 2) ^ 2 and m are positive so r * s is positive
  have hd' : ¬r * s = -d ^ 2 := by
    by_contra h1
    rw [h1] at hs
    have h2 : b' ^ 2 ≤ 0 := by
      rw [hs, (by ring : -d ^ 2 * m = -(d ^ 2 * m))]
      exact neg_nonpos.mpr ((mul_nonneg_iff_of_pos_right h4).mpr (sq_nonneg d))
    have h2' : 0 ≤ b' ^ 2 := by apply sq_nonneg b'
    exact absurd (lt_of_le_of_ne h2' (Ne.symm (pow_ne_zero _ h2b0))) (not_lt.mpr h2)
  replace hd : r * s = d ^ 2 := Or.resolve_right hd hd'
  -- r = +/- j ^ 2
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one htt4 hd
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero, neg_zero, or_self_iff] at hj
    apply left_ne_zero_of_mul hrsz hj
  rw [mul_comm] at hd
  rw [Int.gcd_comm] at htt4
  -- s = +/- k ^ 2
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one htt4 hd
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero, neg_zero, or_self_iff] at hk
    apply right_ne_zero_of_mul hrsz hk
  have hj2 : r ^ 2 = j ^ 4 := by
    rcases hj with hjp | hjp <;>
      · rw [hjp]
        ring
  have hk2 : s ^ 2 = k ^ 4 := by
    rcases hk with hkp | hkp <;>
      · rw [hkp]
        ring
  -- from m = r ^ 2 + s ^ 2 we now get a new solution to a ^ 4 + b ^ 4 = c ^ 2:
  have hh : i ^ 2 = j ^ 4 + k ^ 4 := by rw [← hi, htt3, hj2, hk2]
  have hn : n ≠ 0 := by
    rw [ht2] at hb20
    apply right_ne_zero_of_mul hb20
  -- and it has a smaller c: from c = m ^ 2 + n ^ 2 we see that m is smaller than c, and i ^ 2 = m.
  have hic : Int.natAbs i < Int.natAbs c := by
    apply Int.ofNat_lt.mp
    rw [← Int.eq_natAbs_of_nonneg (le_of_lt hc)]
    apply lt_of_le_of_lt (Int.natAbs_le_self_sq i)
    rw [← hi, ht3]
    apply lt_of_le_of_lt (Int.le_self_sq m)
    exact lt_add_of_pos_right (m ^ 2) (sq_pos_of_ne_zero hn)
  have hic' : Int.natAbs c ≤ Int.natAbs i := by
    apply h.2 j k i
    exact ⟨hj0, hk0, hh.symm⟩
  apply absurd (not_le_of_gt hic) (not_not.mpr hic')

end Fermat42

theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a ^ 4 + b ^ 4 ≠ c ^ 2 := by
  intro h
  obtain ⟨a0, b0, c0, ⟨hf, h2, hp⟩⟩ :=
    Fermat42.exists_pos_odd_minimal (And.intro ha (And.intro hb h))
  apply Fermat42.not_minimal hf h2 hp

/--
Fermat's Last Theorem for $n=4$: if `a b c : ℕ` are all non-zero
then `a ^ 4 + b ^ 4 ≠ c ^ 4`.
-/
theorem fermatLastTheoremFour : FermatLastTheoremFor 4 := by
  rw [fermatLastTheoremFor_iff_int]
  intro a b c ha hb _ heq
  apply @not_fermat_42 _ _ (c ^ 2) ha hb
  rw [heq]; ring

/--
To prove Fermat's Last Theorem, it suffices to prove it for odd prime exponents.
-/
theorem FermatLastTheorem.of_odd_primes
    (hprimes : ∀ p : ℕ, Nat.Prime p → Odd p → FermatLastTheoremFor p) : FermatLastTheorem := by
  intro n h
  obtain hdvd|⟨p, hpprime, hdvd, hpodd⟩ := Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt h <;>
    apply FermatLastTheoremWith.mono hdvd
  · exact fermatLastTheoremFour
  · exact hprimes p hpprime hpodd
