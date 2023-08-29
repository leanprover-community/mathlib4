/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

#align_import number_theory.fermat4 from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# Fermat's Last Theorem for the case n = 4
There are no non-zero integers `a`, `b` and `c` such that `a ^ 4 + b ^ 4 = c ^ 4`.
-/


noncomputable section

open Classical

/-- Shorthand for three non-zero integers `a`, `b`, and `c` satisfying `a ^ 4 + b ^ 4 = c ^ 2`.
We will show that no integers satisfy this equation. Clearly Fermat's Last theorem for n = 4
follows. -/
def Fermat42 (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2
#align fermat_42 Fermat42

namespace Fermat42

theorem comm {a b c : ℤ} : Fermat42 a b c ↔ Fermat42 b a c := by
  delta Fermat42
  -- ⊢ a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2 ↔ b ≠ 0 ∧ a ≠ 0 ∧ b ^ 4 + a ^ 4 = c ^ 2
  rw [add_comm]
  -- ⊢ a ≠ 0 ∧ b ≠ 0 ∧ b ^ 4 + a ^ 4 = c ^ 2 ↔ b ≠ 0 ∧ a ≠ 0 ∧ b ^ 4 + a ^ 4 = c ^ 2
  tauto
  -- 🎉 no goals
#align fermat_42.comm Fermat42.comm

theorem mul {a b c k : ℤ} (hk0 : k ≠ 0) :
    Fermat42 a b c ↔ Fermat42 (k * a) (k * b) (k ^ 2 * c) := by
  delta Fermat42
  -- ⊢ a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2 ↔ k * a ≠ 0 ∧ k * b ≠ 0 ∧ (k * a) ^ 4  …
  constructor
  -- ⊢ a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2 → k * a ≠ 0 ∧ k * b ≠ 0 ∧ (k * a) ^ 4  …
  · intro f42
    -- ⊢ k * a ≠ 0 ∧ k * b ≠ 0 ∧ (k * a) ^ 4 + (k * b) ^ 4 = (k ^ 2 * c) ^ 2
    constructor
    -- ⊢ k * a ≠ 0
    · exact mul_ne_zero hk0 f42.1
      -- 🎉 no goals
    constructor
    -- ⊢ k * b ≠ 0
    · exact mul_ne_zero hk0 f42.2.1
      -- 🎉 no goals
    · have H : a ^ 4 + b ^ 4 = c ^ 2 := f42.2.2
      -- ⊢ (k * a) ^ 4 + (k * b) ^ 4 = (k ^ 2 * c) ^ 2
      linear_combination k ^ 4 * H
      -- 🎉 no goals
  · intro f42
    -- ⊢ a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2
    constructor
    -- ⊢ a ≠ 0
    · exact right_ne_zero_of_mul f42.1
      -- 🎉 no goals
    constructor
    -- ⊢ b ≠ 0
    · exact right_ne_zero_of_mul f42.2.1
      -- 🎉 no goals
    apply (mul_right_inj' (pow_ne_zero 4 hk0)).mp
    -- ⊢ k ^ 4 * (a ^ 4 + b ^ 4) = k ^ 4 * c ^ 2
    linear_combination f42.2.2
    -- 🎉 no goals
#align fermat_42.mul Fermat42.mul

theorem ne_zero {a b c : ℤ} (h : Fermat42 a b c) : c ≠ 0 := by
  apply ne_zero_pow two_ne_zero _; apply ne_of_gt
  -- ⊢ c ^ 2 ≠ 0
                                   -- ⊢ 0 < c ^ 2
  rw [← h.2.2, (by ring : a ^ 4 + b ^ 4 = (a ^ 2) ^ 2 + (b ^ 2) ^ 2)]
  -- ⊢ 0 < (a ^ 2) ^ 2 + (b ^ 2) ^ 2
  exact
    add_pos (sq_pos_of_ne_zero _ (pow_ne_zero 2 h.1)) (sq_pos_of_ne_zero _ (pow_ne_zero 2 h.2.1))
#align fermat_42.ne_zero Fermat42.ne_zero

/-- We say a solution to `a ^ 4 + b ^ 4 = c ^ 2` is minimal if there is no other solution with
a smaller `c` (in absolute value). -/
def Minimal (a b c : ℤ) : Prop :=
  Fermat42 a b c ∧ ∀ a1 b1 c1 : ℤ, Fermat42 a1 b1 c1 → Int.natAbs c ≤ Int.natAbs c1
#align fermat_42.minimal Fermat42.Minimal

/-- if we have a solution to `a ^ 4 + b ^ 4 = c ^ 2` then there must be a minimal one. -/
theorem exists_minimal {a b c : ℤ} (h : Fermat42 a b c) : ∃ a0 b0 c0, Minimal a0 b0 c0 := by
  let S : Set ℕ := { n | ∃ s : ℤ × ℤ × ℤ, Fermat42 s.1 s.2.1 s.2.2 ∧ n = Int.natAbs s.2.2 }
  -- ⊢ ∃ a0 b0 c0, Minimal a0 b0 c0
  have S_nonempty : S.Nonempty := by
    use Int.natAbs c
    rw [Set.mem_setOf_eq]
    use ⟨a, ⟨b, c⟩⟩
  let m : ℕ := Nat.find S_nonempty
  -- ⊢ ∃ a0 b0 c0, Minimal a0 b0 c0
  have m_mem : m ∈ S := Nat.find_spec S_nonempty
  -- ⊢ ∃ a0 b0 c0, Minimal a0 b0 c0
  rcases m_mem with ⟨s0, hs0, hs1⟩
  -- ⊢ ∃ a0 b0 c0, Minimal a0 b0 c0
  use s0.1, s0.2.1, s0.2.2, hs0
  -- ⊢ ∀ (a1 b1 c1 : ℤ), Fermat42 a1 b1 c1 → Int.natAbs s0.snd.snd ≤ Int.natAbs c1
  intro a1 b1 c1 h1
  -- ⊢ Int.natAbs s0.snd.snd ≤ Int.natAbs c1
  rw [← hs1]
  -- ⊢ m ≤ Int.natAbs c1
  apply Nat.find_min'
  -- ⊢ Int.natAbs c1 ∈ S
  use ⟨a1, ⟨b1, c1⟩⟩
  -- 🎉 no goals
#align fermat_42.exists_minimal Fermat42.exists_minimal

/-- a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` must have `a` and `b` coprime. -/
theorem coprime_of_minimal {a b c : ℤ} (h : Minimal a b c) : IsCoprime a b := by
  apply Int.gcd_eq_one_iff_coprime.mp
  -- ⊢ Int.gcd a b = 1
  by_contra hab
  -- ⊢ False
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  -- ⊢ False
  obtain ⟨a1, rfl⟩ := Int.coe_nat_dvd_left.mpr hpa
  -- ⊢ False
  obtain ⟨b1, rfl⟩ := Int.coe_nat_dvd_left.mpr hpb
  -- ⊢ False
  have hpc : (p : ℤ) ^ 2 ∣ c := by
    rw [← Int.pow_dvd_pow_iff zero_lt_two, ← h.1.2.2]
    apply Dvd.intro (a1 ^ 4 + b1 ^ 4)
    ring
  obtain ⟨c1, rfl⟩ := hpc
  -- ⊢ False
  have hf : Fermat42 a1 b1 c1 :=
    (Fermat42.mul (Int.coe_nat_ne_zero.mpr (Nat.Prime.ne_zero hp))).mpr h.1
  apply Nat.le_lt_antisymm (h.2 _ _ _ hf)
  -- ⊢ Int.natAbs c1 < Int.natAbs (↑p ^ 2 * c1)
  rw [Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_pow, Int.natAbs_ofNat]
  -- ⊢ 1 < p ^ 2
  · exact Nat.one_lt_pow _ _ zero_lt_two (Nat.Prime.one_lt hp)
    -- 🎉 no goals
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (ne_zero hf))
    -- 🎉 no goals
#align fermat_42.coprime_of_minimal Fermat42.coprime_of_minimal

/-- We can swap `a` and `b` in a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2`. -/
theorem minimal_comm {a b c : ℤ} : Minimal a b c → Minimal b a c := fun ⟨h1, h2⟩ =>
  ⟨Fermat42.comm.mp h1, h2⟩
#align fermat_42.minimal_comm Fermat42.minimal_comm

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has positive `c`. -/
theorem neg_of_minimal {a b c : ℤ} : Minimal a b c → Minimal a b (-c) := by
  rintro ⟨⟨ha, hb, heq⟩, h2⟩
  -- ⊢ Minimal a b (-c)
  constructor
  -- ⊢ Fermat42 a b (-c)
  · apply And.intro ha (And.intro hb _)
    -- ⊢ a ^ 4 + b ^ 4 = (-c) ^ 2
    rw [heq]
    -- ⊢ c ^ 2 = (-c) ^ 2
    exact (neg_sq c).symm
    -- 🎉 no goals
  rwa [Int.natAbs_neg c]
  -- 🎉 no goals
#align fermat_42.neg_of_minimal Fermat42.neg_of_minimal

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has `a` odd. -/
theorem exists_odd_minimal {a b c : ℤ} (h : Fermat42 a b c) :
    ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ a0 % 2 = 1 := by
  obtain ⟨a0, b0, c0, hf⟩ := exists_minimal h
  -- ⊢ ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ a0 % 2 = 1
  cases' Int.emod_two_eq_zero_or_one a0 with hap hap
  -- ⊢ ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ a0 % 2 = 1
  · cases' Int.emod_two_eq_zero_or_one b0 with hbp hbp
    -- ⊢ ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ a0 % 2 = 1
    · exfalso
      -- ⊢ False
      have h1 : 2 ∣ (Int.gcd a0 b0 : ℤ) :=
        Int.dvd_gcd (Int.dvd_of_emod_eq_zero hap) (Int.dvd_of_emod_eq_zero hbp)
      rw [Int.gcd_eq_one_iff_coprime.mpr (coprime_of_minimal hf)] at h1
      -- ⊢ False
      revert h1
      -- ⊢ 2 ∣ ↑1 → False
      norm_num
      -- 🎉 no goals
    · exact ⟨b0, ⟨a0, ⟨c0, minimal_comm hf, hbp⟩⟩⟩
      -- 🎉 no goals
  exact ⟨a0, ⟨b0, ⟨c0, hf, hap⟩⟩⟩
  -- 🎉 no goals
#align fermat_42.exists_odd_minimal Fermat42.exists_odd_minimal

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has
`a` odd and `c` positive. -/
theorem exists_pos_odd_minimal {a b c : ℤ} (h : Fermat42 a b c) :
    ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ a0 % 2 = 1 ∧ 0 < c0 := by
  obtain ⟨a0, b0, c0, hf, hc⟩ := exists_odd_minimal h
  -- ⊢ ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ a0 % 2 = 1 ∧ 0 < c0
  rcases lt_trichotomy 0 c0 with (h1 | h1 | h1)
  · use a0, b0, c0
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    exact ne_zero hf.1 h1.symm
    -- 🎉 no goals
  · use a0, b0, -c0, neg_of_minimal hf, hc
    -- ⊢ 0 < -c0
    exact neg_pos.mpr h1
    -- 🎉 no goals
#align fermat_42.exists_pos_odd_minimal Fermat42.exists_pos_odd_minimal

end Fermat42

theorem Int.coprime_of_sq_sum {r s : ℤ} (h2 : IsCoprime s r) : IsCoprime (r ^ 2 + s ^ 2) r := by
  rw [sq, sq]
  -- ⊢ IsCoprime (r * r + s * s) r
  exact (IsCoprime.mul_left h2 h2).mul_add_left_left r
  -- 🎉 no goals
#align int.coprime_of_sq_sum Int.coprime_of_sq_sum

theorem Int.coprime_of_sq_sum' {r s : ℤ} (h : IsCoprime r s) :
    IsCoprime (r ^ 2 + s ^ 2) (r * s) := by
  apply IsCoprime.mul_right (Int.coprime_of_sq_sum (isCoprime_comm.mp h))
  -- ⊢ IsCoprime (r ^ 2 + s ^ 2) s
  rw [add_comm]; apply Int.coprime_of_sq_sum h
  -- ⊢ IsCoprime (s ^ 2 + r ^ 2) s
                 -- 🎉 no goals
#align int.coprime_of_sq_sum' Int.coprime_of_sq_sum'

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
  have h2 : Int.gcd (a ^ 2) (b ^ 2) = 1 := Int.gcd_eq_one_iff_coprime.mpr (coprime_of_minimal h).pow
  -- ⊢ False
  -- in order to reduce the possibilities we get from the classification of pythagorean triples
  -- it helps if we know the parity of a ^ 2 (and the sign of c):
  have ha22 : a ^ 2 % 2 = 1 := by
    rw [sq, Int.mul_emod, ha2]
    norm_num
  obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ := ht.coprime_classification' h2 ha22 hc
  -- ⊢ False
  -- Now a, n, m form a pythagorean triple and so we can obtain r and s such that
  -- a = r ^ 2 - s ^ 2, n = 2 * r * s and m = r ^ 2 + s ^ 2
  -- formula:
  have htt : PythagoreanTriple a n m := by
    delta PythagoreanTriple
    linear_combination ht1
  -- a and n are coprime, because a ^ 2 = m ^ 2 - n ^ 2 and m and n are coprime.
  have h3 : Int.gcd a n = 1 := by
    apply Int.gcd_eq_one_iff_coprime.mpr
    apply @IsCoprime.of_mul_left_left _ _ _ a
    rw [← sq, ht1, (by ring : m ^ 2 - n ^ 2 = m ^ 2 + -n * n)]
    exact (Int.gcd_eq_one_iff_coprime.mp ht4).pow_left.add_mul_right_left (-n)
  -- m is positive because b is non-zero and b ^ 2 = 2 * m * n and we already have 0 ≤ m.
  have hb20 : b ^ 2 ≠ 0 := mt pow_eq_zero h.1.2.1
  -- ⊢ False
  have h4 : 0 < m := by
    apply lt_of_le_of_ne ht6
    rintro rfl
    revert hb20
    rw [ht2]
    simp
  obtain ⟨r, s, _, htt2, htt3, htt4, htt5, htt6⟩ := htt.coprime_classification' h3 ha2 h4
  -- ⊢ False
  -- Now use the fact that (b / 2) ^ 2 = m * r * s, and m, r and s are pairwise coprime to obtain
  -- i, j and k such that m = i ^ 2, r = j ^ 2 and s = k ^ 2.
  -- m and r * s are coprime because m = r ^ 2 + s ^ 2 and r and s are coprime.
  have hcp : Int.gcd m (r * s) = 1 := by
    rw [htt3]
    exact
      Int.gcd_eq_one_iff_coprime.mpr (Int.coprime_of_sq_sum' (Int.gcd_eq_one_iff_coprime.mp htt4))
  -- b is even because b ^ 2 = 2 * m * n.
  have hb2 : 2 ∣ b := by
    apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
    rw [ht2, mul_assoc]
    exact dvd_mul_right 2 (m * n)
  cases' hb2 with b' hb2'
  -- ⊢ False
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
  -- ⊢ False
  -- use m is positive to exclude m = - i ^ 2
  have hi' : ¬m = -i ^ 2 := by
    by_contra h1
    have hit : -i ^ 2 ≤ 0
    apply neg_nonpos.mpr (sq_nonneg i)
    rw [← h1] at hit
    apply absurd h4 (not_lt.mpr hit)
  replace hi : m = i ^ 2
  -- ⊢ m = i ^ 2
  · apply Or.resolve_right hi hi'
    -- 🎉 no goals
  rw [mul_comm] at hs
  -- ⊢ False
  rw [Int.gcd_comm] at hcp
  -- ⊢ False
  -- obtain d such that r * s = d ^ 2
  obtain ⟨d, hd⟩ := Int.sq_of_gcd_eq_one hcp hs.symm
  -- ⊢ False
  -- (b / 2) ^ 2 and m are positive so r * s is positive
  have hd' : ¬r * s = -d ^ 2 := by
    by_contra h1
    rw [h1] at hs
    have h2 : b' ^ 2 ≤ 0 := by
      rw [hs, (by ring : -d ^ 2 * m = -(d ^ 2 * m))]
      exact neg_nonpos.mpr ((zero_le_mul_right h4).mpr (sq_nonneg d))
    have h2' : 0 ≤ b' ^ 2 := by apply sq_nonneg b'
    exact absurd (lt_of_le_of_ne h2' (Ne.symm (pow_ne_zero _ h2b0))) (not_lt.mpr h2)
  replace hd : r * s = d ^ 2
  -- ⊢ r * s = d ^ 2
  · apply Or.resolve_right hd hd'
    -- 🎉 no goals
  -- r = +/- j ^ 2
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one htt4 hd
  -- ⊢ False
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, zero_pow zero_lt_two, neg_zero, or_self_iff] at hj
    apply left_ne_zero_of_mul hrsz hj
  rw [mul_comm] at hd
  -- ⊢ False
  rw [Int.gcd_comm] at htt4
  -- ⊢ False
  -- s = +/- k ^ 2
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one htt4 hd
  -- ⊢ False
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_pow zero_lt_two, neg_zero, or_self_iff] at hk
    apply right_ne_zero_of_mul hrsz hk
  have hj2 : r ^ 2 = j ^ 4 := by
    cases' hj with hjp hjp <;>
      · rw [hjp]
        ring
  have hk2 : s ^ 2 = k ^ 4 := by
    cases' hk with hkp hkp <;>
      · rw [hkp]
        ring
  -- from m = r ^ 2 + s ^ 2 we now get a new solution to a ^ 4 + b ^ 4 = c ^ 2:
  have hh : i ^ 2 = j ^ 4 + k ^ 4 := by rw [← hi, htt3, hj2, hk2]
  -- ⊢ False
  have hn : n ≠ 0 := by
    rw [ht2] at hb20
    apply right_ne_zero_of_mul hb20
  -- and it has a smaller c: from c = m ^ 2 + n ^ 2 we see that m is smaller than c, and i ^ 2 = m.
  have hic : Int.natAbs i < Int.natAbs c := by
    apply Int.ofNat_lt.mp
    rw [← Int.eq_natAbs_of_zero_le (le_of_lt hc)]
    apply gt_of_gt_of_ge _ (Int.natAbs_le_self_sq i)
    rw [← hi, ht3]
    apply gt_of_gt_of_ge _ (Int.le_self_sq m)
    exact lt_add_of_pos_right (m ^ 2) (sq_pos_of_ne_zero n hn)
  have hic' : Int.natAbs c ≤ Int.natAbs i := by
    apply h.2 j k i
    exact ⟨hj0, hk0, hh.symm⟩
  apply absurd (not_le_of_lt hic) (not_not.mpr hic')
  -- 🎉 no goals
#align fermat_42.not_minimal Fermat42.not_minimal

end Fermat42

theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a ^ 4 + b ^ 4 ≠ c ^ 2 := by
  intro h
  -- ⊢ False
  obtain ⟨a0, b0, c0, ⟨hf, h2, hp⟩⟩ :=
    Fermat42.exists_pos_odd_minimal (And.intro ha (And.intro hb h))
  apply Fermat42.not_minimal hf h2 hp
  -- 🎉 no goals
#align not_fermat_42 not_fermat_42

theorem not_fermat_4 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a ^ 4 + b ^ 4 ≠ c ^ 4 := by
  intro heq
  -- ⊢ False
  apply @not_fermat_42 _ _ (c ^ 2) ha hb
  -- ⊢ a ^ 4 + b ^ 4 = (c ^ 2) ^ 2
  rw [heq]; ring
  -- ⊢ c ^ 4 = (c ^ 2) ^ 2
            -- 🎉 no goals
#align not_fermat_4 not_fermat_4
