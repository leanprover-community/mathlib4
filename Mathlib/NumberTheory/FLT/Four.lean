/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
module

public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.PythagoreanTriples

import Mathlib.Tactic.LinearCombination

/-!
# Fermat's Last Theorem for the case n = 4

There are no non-zero integers `a`, `b` and `c` such that `a ^ 4 + b ^ 4 = c ^ 4`.
-/

@[expose] public section

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
  · grind [mul_eq_zero]
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
    rw [Set.mem_ofPred_eq]
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

theorem Int.isCoprime_of_sq_sum' {r s : ℤ} (h : IsCoprime r s) :
    IsCoprime (r ^ 2 + s ^ 2) (r * s) := by
  apply IsCoprime.mul_right (Int.isCoprime_of_sq_sum (isCoprime_comm.mp h))
  rw [add_comm]; apply Int.isCoprime_of_sq_sum h

namespace Fermat42

-- If we have a solution to a ^ 4 + b ^ 4 = c ^ 2, we can construct a smaller one. This
-- implies there can't be a smallest solution.
theorem not_minimal {a b c : ℤ} (h : Minimal a b c) (ha2 : a % 2 = 1) (hc : 0 < c) : False := by
  -- Step 1: Parametrize the primitive Pythagorean triple (a², b², c).
  have ht : PythagoreanTriple (a ^ 2) (b ^ 2) c := by
    rw [PythagoreanTriple, ← pow_add, ← pow_add, ← sq]; exact h.1.2.2
  obtain ⟨m, n, ht1, ht2, ht3, ht4, _, ht6⟩ := ht.coprime_classification'
    (Int.isCoprime_iff_gcd_eq_one.mp (coprime_of_minimal h).pow)
    (by rw [sq, Int.mul_emod, ha2]; rfl) hc
  -- Step 2: Parametrize the second primitive Pythagorean triple (a, n, m).
  have htt : PythagoreanTriple a n m := by
    rw [PythagoreanTriple, ← sq, ← sq, ← sq, ht1, sub_add_cancel]
  have hmn : IsCoprime (a * a + n * n) n :=
    let h := Int.isCoprime_iff_gcd_eq_one.mpr ht4; htt.eq ▸ h.mul_left h
  have hmn0 : 2 * m * n ≠ 0 := ht2 ▸ pow_ne_zero 2 h.1.2.1
  have h4 : 0 < m := ht6.lt_of_ne' (right_ne_zero_of_mul (left_ne_zero_of_mul hmn0))
  obtain ⟨r, s, _, htt2, htt3, htt4, _, _⟩ := htt.coprime_classification'
    (Int.isCoprime_iff_gcd_eq_one.mp hmn.of_add_mul_left_left.of_mul_left_left) ha2 h4
  -- Step 3: Extract square factors from m * r * s = (b / 2)² via pairwise coprimality.
  have hrs : IsCoprime r s := Int.isCoprime_iff_gcd_eq_one.mpr htt4
  have hcp : IsCoprime m (r * s) := htt3 ▸ Int.isCoprime_of_sq_sum' hrs
  obtain ⟨b', hb'⟩ : 2 ∣ b := Int.Prime.dvd_pow' Nat.prime_two ⟨m * n, ht2.trans (mul_assoc ..)⟩
  have hs : m * (r * s) = b' ^ 2 := mul_left_cancel₀ (pow_ne_zero 2 two_ne_zero) <| by
    rw [← mul_pow, ← hb', ht2, htt2, sq, mul_mul_mul_comm, ← mul_assoc 2 r]
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hcp) hs
  have hi := hi.resolve_right fun h1 => (h1 ▸ h4).not_ge (neg_nonpos.mpr (sq_nonneg i))
  have sq_pow4 {x y : ℤ} (hg : IsCoprime x y) (he : x * y = b' ^ 2) (hx : x ≠ 0) :
      ∃ w, w ≠ 0 ∧ x ^ 2 = w ^ 4 := by
    obtain ⟨w, rfl | rfl⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hg) he
    · exact ⟨w, ne_zero_pow two_ne_zero hx, (pow_mul ..).symm⟩
    · exact ⟨w, ne_zero_pow two_ne_zero (neg_ne_zero.mp hx), (neg_sq _).trans (pow_mul ..).symm⟩
  have h2rs : 2 * r * s ≠ 0 := htt2 ▸ right_ne_zero_of_mul hmn0
  obtain ⟨j, hj0, hj⟩ := sq_pow4 (hcp.of_mul_right_left.symm.mul_right hrs)
    (mul_left_comm r m s ▸ hs) (right_ne_zero_of_mul (left_ne_zero_of_mul h2rs))
  obtain ⟨k, hk0, hk⟩ := sq_pow4 (hcp.of_mul_right_right.symm.mul_right hrs.symm)
    (by rw [mul_comm s, mul_assoc, hs]) (right_ne_zero_of_mul h2rs)
  -- Step 4: Construct a smaller solution (j, k, i), contradicting minimality.
  exact (h.2 j k i ⟨hj0, hk0, by rw [← hj, ← hk, ← htt3, hi]⟩).not_gt <| Int.ofNat_lt.mp <|
    calc (i.natAbs : ℤ) ≤ i ^ 2 := Int.natAbs_le_self_sq i
      _ ≤ m ^ 2 := hi ▸ Int.le_self_sq m
      _ < m ^ 2 + n ^ 2 := lt_add_of_pos_right _ (sq_pos_of_ne_zero (right_ne_zero_of_mul hmn0))
      _ = c.natAbs := by rw [← ht3, Int.natAbs_of_nonneg hc.le]

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
  obtain hdvd | ⟨p, hpprime, hdvd, hpodd⟩ := Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt h
    <;> apply FermatLastTheoremWith.mono hdvd
  · exact fermatLastTheoremFour
  · exact hprimes p hpprime hpodd
