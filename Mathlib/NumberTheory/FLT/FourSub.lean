/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Fermat's Last Theorem for n = 4, difference form: `a ^ 4 - b ^ 4 ≠ c ^ 2`

There are no non-zero integers `a`, `b`, `c` such that `a ^ 4 - b ^ 4 = c ^ 2`.
This is the "difference form" companion to `Mathlib.NumberTheory.FLT.Four.not_fermat_42`
(sum form `a ^ 4 + b ^ 4 = c ^ 2`).  Together the two theorems close both
diophantine shapes of Fermat's n = 4 case.

## Strategy

Mirrors mathlib's `Fermat42` structure for the sum form, adapted to the
difference form:

* `Fermat42Sub (a b c : ℤ) : Prop` — the predicate `a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
  a ^ 4 - b ^ 4 = c ^ 2`.
* `Fermat42Sub.Minimal` — minimal counterexample.
* `Fermat42Sub.exists_minimal` + `coprime_of_minimal` — reduce to coprime.
* `(b ^ 2) ^ 2 + c ^ 2 = (a ^ 2) ^ 2` — primitive Pythagorean triple.
* Case split on parity of `b`:
  * `b` odd (Case A): `b ^ 2 = m ^ 2 - n ^ 2`, `c = 2 m n`, `a ^ 2 = m ^ 2 + n ^ 2`.
    Reduces to the auxiliary equation `2 a ^ 2 = s ^ 4 + t ^ 4` which is also
    impossible (`fermat42Double_impossible`, a classical Fermat descent in
    its own right).
  * `b` even (Case B): `c = m ^ 2 - n ^ 2`, `b ^ 2 = 2 m n`, `a ^ 2 = m ^ 2 + n ^ 2`.
    Direct infinite descent via a strictly smaller `Fermat42Sub`.

The auxiliary `fermat42Double_impossible` (`2 a ^ 2 = s ^ 4 + t ^ 4` has no
non-trivial coprime solutions with `s ^ 2 ≠ t ^ 2`) is proved by infinite
descent on `a.natAbs`, using a Pythagorean classification on `u ^ 2 + v ^ 2 =
a ^ 2` (`u = (s ^ 2 + t ^ 2) / 2`, `v = (t ^ 2 - s ^ 2) / 2`), two parallel
coprime factorizations yielding a quadruple `(a', b, c, d)` with
`k = a' * b * c * d` and the key relation `4 * a' * b * c * d =
(c ^ 2 - b ^ 2) * (2 * a' ^ 2 - d ^ 2)`.  Completing the square gives
`(2 (c ^ 2 - b ^ 2) d + 4 a' b c) ^ 2 = 8 a' ^ 2 * (b ^ 4 + c ^ 4)`, which
forces `2 e ^ 2 = b ^ 4 + c ^ 4` with `|e| ≤ k ^ 2 < a`.

## Main results

* `Fermat42Sub` — the difference-form predicate.
* `not_fermat_42_sub` — no non-zero integer solutions.
-/

noncomputable section

/-! ## Section: Fermat42SubFoundations_2026_11_13 -/

/-- Three non-zero integers `a`, `b`, `c` with `a^4 - b^4 = c^2`.

Mirrors mathlib's `Fermat42` (sum form). We explicitly require
`c ≠ 0` to exclude the degenerate family `a = ±b, c = 0`. -/
def Fermat42Sub (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2

namespace Fermat42Sub

/-- Scaling: `Fermat42Sub a b c ↔ Fermat42Sub (k·a) (k·b) (k²·c)` for `k ≠ 0`. -/
theorem mul {a b c k : ℤ} (hk0 : k ≠ 0) :
    Fermat42Sub a b c ↔ Fermat42Sub (k * a) (k * b) (k ^ 2 * c) := by
  delta Fermat42Sub
  constructor
  · intro ⟨ha, hb, hc, hH⟩
    refine ⟨mul_ne_zero hk0 ha, mul_ne_zero hk0 hb,
            mul_ne_zero (pow_ne_zero 2 hk0) hc, ?_⟩
    linear_combination k ^ 4 * hH
  · intro ⟨ha, hb, hc, hH⟩
    refine ⟨right_ne_zero_of_mul ha, right_ne_zero_of_mul hb,
            right_ne_zero_of_mul hc, ?_⟩
    apply (mul_right_inj' (pow_ne_zero 4 hk0)).mp
    linear_combination hH

/-- `a^4 > b^4` for any `Fermat42Sub a b c` with `c ≠ 0`.

Follows from `a^4 - b^4 = c^2 > 0`. -/
theorem lt_pow_of_fermat42Sub {a b c : ℤ} (h : Fermat42Sub a b c) :
    b ^ 4 < a ^ 4 := by
  have hc : c ≠ 0 := h.2.2.1
  have hH : a ^ 4 - b ^ 4 = c ^ 2 := h.2.2.2
  have hc_pos : 0 < c ^ 2 := by positivity
  linarith

/-- A minimal counterexample: no other `Fermat42Sub` has strictly smaller `|c|`. -/
def Minimal (a b c : ℤ) : Prop :=
  Fermat42Sub a b c ∧ ∀ a1 b1 c1 : ℤ, Fermat42Sub a1 b1 c1 →
    Int.natAbs c ≤ Int.natAbs c1

/-- Any `Fermat42Sub` solution yields a minimal one (via well-ordering of ℕ). -/
theorem exists_minimal {a b c : ℤ} (h : Fermat42Sub a b c) :
    ∃ a0 b0 c0, Minimal a0 b0 c0 := by
  classical
  let S : Set ℕ := { n | ∃ s : ℤ × ℤ × ℤ, Fermat42Sub s.1 s.2.1 s.2.2 ∧
    n = Int.natAbs s.2.2 }
  have S_nonempty : S.Nonempty := by
    refine ⟨Int.natAbs c, ?_⟩
    rw [Set.mem_setOf_eq]
    exact ⟨⟨a, ⟨b, c⟩⟩, h, rfl⟩
  let m : ℕ := Nat.find S_nonempty
  have m_mem : m ∈ S := Nat.find_spec S_nonempty
  rcases m_mem with ⟨s0, hs0, hs1⟩
  refine ⟨s0.1, s0.2.1, s0.2.2, hs0, ?_⟩
  intro a1 b1 c1 h1
  rw [← hs1]
  apply Nat.find_min'
  exact ⟨⟨a1, ⟨b1, c1⟩⟩, h1, rfl⟩

/-- A minimal `Fermat42Sub` solution has `a, b` coprime.

Proof: if prime `p ∣ gcd(a, b)`, then `p^2 ∣ c` (via `a^4 - b^4 = c^2`),
and dividing through gives a smaller solution — contradicting minimality. -/
theorem coprime_of_minimal {a b c : ℤ} (h : Minimal a b c) : IsCoprime a b := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a1, rfl⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b1, rfl⟩ := Int.natCast_dvd.mpr hpb
  have hpc : (p : ℤ) ^ 2 ∣ c := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2.2]
    refine Dvd.intro (a1 ^ 4 - b1 ^ 4) ?_
    ring
  obtain ⟨c1, rfl⟩ := hpc
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero hp)
  have hf : Fermat42Sub a1 b1 c1 :=
    (Fermat42Sub.mul hp_ne).mpr h.1
  apply Nat.le_lt_asymm (h.2 _ _ _ hf)
  rw [Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_pow, Int.natAbs_natCast]
  · exact Nat.one_lt_pow two_ne_zero (Nat.Prime.one_lt hp)
  · -- c1 ≠ 0 is in hf (now that we require c ≠ 0 in Fermat42Sub).
    exact Int.natAbs_pos.mpr hf.2.2.1

end Fermat42Sub

/-! ## Section: Fermat42SubCaseAReduction_2026_11_13 -/

namespace Fermat42Sub
/-- **Auxiliary Diophantine equation**: `2a² = s⁴ + t⁴` has no
nontrivial coprime solutions.

Classical Fermat result (same era as `not_fermat_42`, separate descent).
Proof structure: Pythagorean decomposition of the derived equation
`u² + v² = a²` with `u = (s²+t²)/2, v = (t²-s²)/2`, followed by
infinite descent.

Stated as a named Prop.  Discharging requires ~50-80 Lean lines. -/
def Fermat42Double_impossible : Prop :=
  ∀ s t a : ℤ, s ≠ 0 → t ≠ 0 → a ≠ 0 → IsCoprime s t → s ^ 2 ≠ t ^ 2 →
    2 * a ^ 2 ≠ s ^ 4 + t ^ 4

/-- **Sub-gap 3**: `b² = (m − 2k)(m + 2k)` with coprime factors
(both odd), so each factor is a perfect square.

Standard coprime-square-product lemma.  Named for the descent.
Requires `0 ≤ m - 2*k` (the square itself). -/
def Fermat42SubCaseA_squareSplit : Prop :=
  ∀ m k b : ℤ, 0 ≤ m - 2 * k → 0 ≤ m + 2 * k →
    IsCoprime (m - 2 * k) (m + 2 * k) →
    b ^ 2 = (m - 2 * k) * (m + 2 * k) →
    ∃ s t : ℤ, m - 2 * k = s ^ 2 ∧ m + 2 * k = t ^ 2 ∧
      s * t = b ∧ IsCoprime s t

/-- **Case A reduction**: under the Case A hypothesis, we derive
an auxiliary `2a² = s⁴ + t⁴` instance that must be contradicted. -/
theorem fermat42Sub_caseA_reduces
    (hSplit3 : Fermat42SubCaseA_squareSplit)
    (hDouble : Fermat42Double_impossible)
    (a b c m n : ℤ)
    (_h_min : Minimal a b c)
    (_ha_pos : 0 < a) (_hc_pos : 0 < c)
    (_h_m_nn : 0 ≤ m) (_h_n_pos : 0 < n)
    (hmn_coprime : IsCoprime m n)
    (hm_odd : m % 2 = 1) (hn_even : n % 2 = 0)
    (hb_sq : b ^ 2 = m ^ 2 - n ^ 2)
    (ha_sq : a ^ 2 = m ^ 2 + n ^ 2) : False := by
  -- Write n = 2k where k = n / 2.
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hn_even
  -- hk : n = 2 * k.
  subst hk
  -- b² = m² - (2k)² = (m - 2k)(m + 2k).
  have hb_fact : b ^ 2 = (m - 2 * k) * (m + 2 * k) := by
    rw [hb_sq]; ring
  -- Apply sub-gap 3: square split.
  -- m - 2k ≥ 0 and m + 2k ≥ 0 (from b² = (m - 2k)(m + 2k) ≥ 0, m ≥ 0, k > 0).
  have hk_pos : 0 < k := by linarith
  have hm_plus_nn : 0 ≤ m + 2 * k := by linarith [_h_m_nn]
  have hm_minus_nn : 0 ≤ m - 2 * k := by
    have hbsq_nn : 0 ≤ b ^ 2 := sq_nonneg b
    rw [hb_fact] at hbsq_nn
    by_contra h_lt
    push_neg at h_lt
    have h_neg : m - 2 * k < 0 := h_lt
    have h_sum_pos : 0 < m + 2 * k ∨ m + 2 * k = 0 := by
      rcases lt_or_eq_of_le hm_plus_nn with h | h
      · left; exact h
      · right; exact h.symm
    rcases h_sum_pos with h_sum_pos | h_sum_zero
    · have : (m - 2 * k) * (m + 2 * k) < 0 :=
        mul_neg_of_neg_of_pos h_neg h_sum_pos
      linarith
    · rw [h_sum_zero] at hb_fact; simp at hb_fact
      have : b = 0 := by nlinarith [sq_nonneg b, hb_fact]
      -- b = 0 contradicts _h_min.1.2.1.
      exact _h_min.1.2.1 this
  -- Coprimality of (m - 2k) and (m + 2k):
  -- From `IsCoprime m (2k)`: derive `IsCoprime (m - 2k) (2k)` via add_mul.
  -- Then derive `IsCoprime (m - 2k) (m + 2k) = IsCoprime (m - 2k) ((m - 2k) + 4k)`.
  have hcop1 : IsCoprime (m - 2 * k) (2 * k) := by
    -- m - 2k = m + (-1) * (2k).  IsCoprime m (2k) ⟹ IsCoprime (m + (-1)*(2k)) (2k).
    have := hmn_coprime.add_mul_right_left (-1)
    simpa using this
  -- Derive IsCoprime (m - 2k) 2 from m - 2k odd.
  have hm_minus_odd : (m - 2 * k) % 2 = 1 := by
    rw [Int.sub_emod, hm_odd]; simp [Int.mul_emod]
  have hcop_two : IsCoprime (m - 2 * k) (2 : ℤ) := by
    refine (Int.isCoprime_iff_gcd_eq_one).mpr ?_
    rw [Int.gcd]
    have h2 : Int.natAbs 2 = 2 := rfl
    rw [h2]
    have hodd : Odd (m - 2 * k) := by
      rw [Int.odd_iff]; exact hm_minus_odd
    have h_natabs_odd : Odd (Int.natAbs (m - 2 * k)) :=
      Int.natAbs_odd.mpr hodd
    exact (Nat.Coprime.symm (Nat.coprime_two_left.mpr h_natabs_odd))
  -- IsCoprime (m - 2k) (4k) from IsCoprime (m-2k) 2 and IsCoprime (m-2k) (2k).
  -- 4k = 2 * (2k).
  have hcop_4k : IsCoprime (m - 2 * k) (4 * k) := by
    have h_4k : (4 * k : ℤ) = 2 * (2 * k) := by ring
    rw [h_4k]
    exact hcop_two.mul_right hcop1
  -- IsCoprime (m - 2k) (m + 2k) = IsCoprime (m - 2k) ((m - 2k) + 4k).
  -- Use `add_mul_right_right` after rewriting (m + 2k) = (m - 2k) + 4k = (m - 2k) + 1 * (4k).
  -- Actually: IsCoprime x (y + z * x) ← IsCoprime x y, where we want the reverse direction.
  -- We have IsCoprime (m-2k) (4k) and want IsCoprime (m-2k) ((m-2k) + 4k).
  -- Use `IsCoprime.of_add_mul_left_right` reversed?  Or use the explicit `add_mul` iff.
  have hpair_coprime : IsCoprime (m - 2 * k) (m + 2 * k) := by
    have hrw : m + 2 * k = 4 * k + 1 * (m - 2 * k) := by ring
    rw [hrw]
    exact hcop_4k.add_mul_right_right 1
  obtain ⟨s, t, hs_eq, ht_eq, hst_eq, hst_coprime⟩ :=
    hSplit3 m k b hm_minus_nn hm_plus_nn hpair_coprime hb_fact
  -- From m - 2k = s² and m + 2k = t²: 2m = s² + t², 2(2k) = t² - s².
  -- Then a² = m² + (2k)² = ((s²+t²)/2)² + ((t²-s²)/2)² = (s⁴+t⁴)/2.
  have ha_dbl : 2 * a ^ 2 = s ^ 4 + t ^ 4 := by
    have h1 : 2 * m = s ^ 2 + t ^ 2 := by linear_combination hs_eq + ht_eq
    have h2 : 4 * k = t ^ 2 - s ^ 2 := by linear_combination ht_eq - hs_eq
    -- 4a² = 4(m² + (2k)²) = (2m)² + (4k)² = (s²+t²)² + (t²-s²)² = 2(s⁴+t⁴).
    have h3 : (2 * a) ^ 2 = (s ^ 2 + t ^ 2) ^ 2 + (t ^ 2 - s ^ 2) ^ 2 := by
      have : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
      rw [this, ha_sq]
      have hfour_k : (4 * k) ^ 2 = 16 * k ^ 2 := by ring
      -- 4(m² + 4k²) = (2m)² + (4k)²
      calc 4 * (m ^ 2 + (2 * k) ^ 2)
          = (2 * m) ^ 2 + (4 * k) ^ 2 := by ring
        _ = (s ^ 2 + t ^ 2) ^ 2 + (t ^ 2 - s ^ 2) ^ 2 := by rw [h1, h2]
    -- (s²+t²)² + (t²-s²)² = 2(s⁴+t⁴).
    have h4 : (s ^ 2 + t ^ 2) ^ 2 + (t ^ 2 - s ^ 2) ^ 2 = 2 * (s ^ 4 + t ^ 4) := by
      ring
    have h5 : (2 * a) ^ 2 = 2 * (s ^ 4 + t ^ 4) := by rw [h3, h4]
    have h6 : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
    linarith [h5, h6]
  -- s, t, a nonzero.
  have hb_ne : b ≠ 0 := _h_min.1.2.1
  have hst_ne : s * t ≠ 0 := by rw [hst_eq]; exact hb_ne
  have hs_ne : s ≠ 0 := left_ne_zero_of_mul hst_ne
  have ht_ne : t ≠ 0 := right_ne_zero_of_mul hst_ne
  have ha_ne : a ≠ 0 := ne_of_gt _ha_pos
  -- s² ≠ t² from k > 0 (i.e., n = 2k > 0) and `t² - s² = 4k > 0`.
  have hst_sq_ne : s ^ 2 ≠ t ^ 2 := by
    intro h_eq
    have h_ts : t ^ 2 - s ^ 2 = 4 * k := by linarith [ht_eq, hs_eq]
    rw [h_eq] at h_ts
    linarith [hk_pos]
  -- Apply sub-gap: 2a² = s⁴ + t⁴ is impossible.
  exact hDouble s t a hs_ne ht_ne ha_ne hst_coprime hst_sq_ne ha_dbl

end Fermat42Sub

/-! ## Section: Fermat42SubCaseBClosure_2026_11_13 -/

namespace Fermat42Sub
/-- **Sub-gap 1**: `b² = 2mn` with `gcd(m, n) = 1`, `m` odd, `n` even
implies `m` and `n/2` are each perfect squares.

Standard coprime-square-product lemma.  Stated as a named sub-gap. -/
def Fermat42SubCaseB_squareSplit : Prop :=
  ∀ m n b : ℤ, 0 ≤ m → 0 < n → IsCoprime m n →
    m % 2 = 1 → n % 2 = 0 → b ^ 2 = 2 * m * n →
    ∃ i j : ℤ, m = i ^ 2 ∧ n = 2 * j ^ 2 ∧ b = 2 * i * j

/-- **Sub-gap 2**: given `a² - i⁴ = 4j⁴`, `a > 0`, `i` odd, `j ≠ 0`,
with `gcd(a, i·j) = 1`, there exist `p, q` coprime with `pq = i` and
`a - 2j² = p⁴`, `a + 2j² = q⁴`.

Follows from coprimality of `(a - 2j²)` and `(a + 2j²)` plus the
coprime-product-is-4th-power argument.  Stated as a named sub-gap. -/
def Fermat42SubCaseB_fourthPowerSplit : Prop :=
  ∀ a i j : ℤ, 0 < a → i % 2 = 1 → j ≠ 0 → IsCoprime a (i * j) →
    a ^ 2 - i ^ 4 = 4 * j ^ 4 →
    ∃ p q : ℤ, p * q = i ∧ a - 2 * j ^ 2 = p ^ 4 ∧ a + 2 * j ^ 2 = q ^ 4

/-- **Case B closure**: conditional on the two square-split sub-gaps. -/
theorem fermat42Sub_caseB_descends
    (hSplit1 : Fermat42SubCaseB_squareSplit)
    (hSplit2 : Fermat42SubCaseB_fourthPowerSplit)
    (a b c m n : ℤ)
    (h_min : Minimal a b c)
    (ha_pos : 0 < a) (hc_pos : 0 < c)
    (h_m_nn : 0 ≤ m) (h_n_pos : 0 < n)
    (hmn_coprime : IsCoprime m n)
    (hm_odd : m % 2 = 1) (hn_even : n % 2 = 0)
    (hc_eq : c = m ^ 2 - n ^ 2)
    (hb_sq : b ^ 2 = 2 * m * n)
    (ha_sq : a ^ 2 = m ^ 2 + n ^ 2) : False := by
  -- Step 1: square split.
  obtain ⟨i, j, hm_eq, hn_eq, hb_eq⟩ := hSplit1 m n b h_m_nn h_n_pos
    hmn_coprime hm_odd hn_even hb_sq
  -- Step 2: `a² - i⁴ = 4j⁴` follows from `a² = m² + n²`, `m = i²`, `n = 2j²`.
  have ha_sq' : a ^ 2 - i ^ 4 = 4 * j ^ 4 := by
    rw [hm_eq, hn_eq] at ha_sq
    linear_combination ha_sq
  -- j ≠ 0: if j = 0, n = 0, contradicting h_n_pos.
  have hj_ne : j ≠ 0 := by
    intro hj
    rw [hj] at hn_eq
    simp at hn_eq
    linarith
  -- i odd: m = i² and m odd ⟹ i² odd ⟹ i odd.
  have hi_odd : i % 2 = 1 := by
    rw [hm_eq] at hm_odd
    rw [show (i ^ 2 : ℤ) = i * i from sq i, Int.mul_emod] at hm_odd
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · rw [h] at hm_odd; norm_num at hm_odd
    · exact h
  -- gcd(a, i·j) = 1: follows from gcd(a, b) = 1 and b = 2ij.
  have hab_coprime : IsCoprime a b :=
    Fermat42Sub.coprime_of_minimal h_min
  have ha_ij_coprime : IsCoprime a (i * j) := by
    have hb_fact : b = 2 * (i * j) := by rw [hb_eq]; ring
    have h1 : IsCoprime a (2 * (i * j)) := hb_fact ▸ hab_coprime
    exact h1.of_mul_right_right
  -- Step 3: 4th power split.
  obtain ⟨p, q, hpq, hp_eq, hq_eq⟩ := hSplit2 a i j ha_pos hi_odd hj_ne
    ha_ij_coprime ha_sq'
  -- Step 4: construct new Fermat42Sub (q, p, 2j).
  have h_new_eq : q ^ 4 - p ^ 4 = (2 * j) ^ 2 := by
    have : q ^ 4 - p ^ 4 = (a + 2 * j ^ 2) - (a - 2 * j ^ 2) := by
      rw [hp_eq, hq_eq]
    rw [this]
    ring
  -- p, q nonzero (from pq = i ≠ 0 since i odd implies i ≠ 0).
  have hi_ne : i ≠ 0 := by
    intro h
    rw [h] at hi_odd
    norm_num at hi_odd
  have hp_ne : p ≠ 0 := left_ne_zero_of_mul (by rw [hpq]; exact hi_ne)
  have hq_ne : q ≠ 0 := right_ne_zero_of_mul (by rw [hpq]; exact hi_ne)
  have h2j_ne : (2 * j : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hj_ne
  have h_new : Fermat42Sub q p (2 * j) := ⟨hq_ne, hp_ne, h2j_ne, h_new_eq⟩
  -- Step 5: |2j| < |c| contradicts minimality.
  have h_le : Int.natAbs c ≤ Int.natAbs (2 * j) := h_min.2 q p (2 * j) h_new
  -- c = m² - n² = i⁴ - 4j⁴. |c| ≥ 4j² + 1 ≥ 2|j| + 1 for |j| ≥ 1.
  -- Need |2j| < |c|.
  have hj_abs_pos : 0 < Int.natAbs j := Int.natAbs_pos.mpr hj_ne
  have hc_eq' : c = i ^ 4 - 4 * j ^ 4 := by
    rw [hc_eq, hm_eq, hn_eq]
    ring
  -- c > 0 and c = i⁴ - 4j⁴ > 0 → i⁴ > 4j⁴ → i² > 2j² (taking sqrt).
  have hi_sq_gt : i ^ 2 > 2 * j ^ 2 := by
    by_contra h_le_ij
    push_neg at h_le_ij
    have h_i4_le : i ^ 4 ≤ 4 * j ^ 4 := by
      have : i ^ 2 * i ^ 2 ≤ (2 * j ^ 2) * (2 * j ^ 2) := by
        exact mul_le_mul h_le_ij h_le_ij (sq_nonneg _) (by positivity)
      calc i ^ 4 = i ^ 2 * i ^ 2 := by ring
        _ ≤ (2 * j ^ 2) * (2 * j ^ 2) := this
        _ = 4 * j ^ 4 := by ring
    linarith
  -- From i² > 2j²: i² ≥ 2j² + 1 (since both integers). So i⁴ ≥ (2j² + 1)² = 4j⁴ + 4j² + 1.
  -- Hence c = i⁴ - 4j⁴ ≥ 4j² + 1.
  have hc_ge : 4 * j ^ 2 + 1 ≤ c := by
    have h1 : 2 * j ^ 2 + 1 ≤ i ^ 2 := hi_sq_gt
    have h2j_nn : 0 ≤ 2 * j ^ 2 + 1 := by positivity
    have h2 : (2 * j ^ 2 + 1) ^ 2 ≤ (i ^ 2) ^ 2 :=
      pow_le_pow_left₀ h2j_nn h1 2
    have h3 : (2 * j ^ 2 + 1) ^ 2 = 4 * j ^ 4 + 4 * j ^ 2 + 1 := by ring
    have h4 : (i ^ 2) ^ 2 = i ^ 4 := by ring
    rw [hc_eq']
    linarith [h2, h3, h4]
  -- Now |2j| ≤ 2|j|, and |c| ≥ 4j² + 1 ≥ 4|j|² + 1 > 2|j|.
  have h_abs_lt : Int.natAbs (2 * j) < Int.natAbs c := by
    have h2j_abs : Int.natAbs (2 * j) = 2 * Int.natAbs j := by
      rw [Int.natAbs_mul]; rfl
    have hc_cast : (Int.natAbs c : ℤ) = c := Int.natAbs_of_nonneg hc_pos.le
    have h_jsq_cast : (j : ℤ) ^ 2 = (Int.natAbs j : ℤ) ^ 2 := by
      rw [show ((Int.natAbs j : ℤ)) = |j| from (Int.abs_eq_natAbs j).symm,
          sq_abs]
    have hc_abs_ge : (4 * (Int.natAbs j : ℤ) ^ 2 + 1 : ℤ) ≤ (Int.natAbs c : ℤ) := by
      rw [hc_cast, ← h_jsq_cast]
      exact hc_ge
    have hc_abs_nat : 4 * (Int.natAbs j) ^ 2 + 1 ≤ Int.natAbs c := by
      have h1 : ((4 * (Int.natAbs j) ^ 2 + 1 : ℕ) : ℤ)
            = 4 * (Int.natAbs j : ℤ) ^ 2 + 1 := by push_cast; ring
      have h2 : ((Int.natAbs c : ℕ) : ℤ) = (Int.natAbs c : ℤ) := by rfl
      have h3 : ((4 * (Int.natAbs j) ^ 2 + 1 : ℕ) : ℤ) ≤ ((Int.natAbs c : ℕ) : ℤ) := by
        rw [h1, h2]; exact hc_abs_ge
      exact_mod_cast h3
    rw [h2j_abs]
    have := hj_abs_pos
    calc 2 * Int.natAbs j
        < 4 * (Int.natAbs j) ^ 2 + 1 := by nlinarith
      _ ≤ Int.natAbs c := hc_abs_nat
  exact absurd h_le (not_le_of_gt h_abs_lt)

end Fermat42Sub

/-! ## Section: Fermat42SubSplitLemmas_2026_11_13 -/

namespace Fermat42Sub
open Int

/-- Helper: if `x ≥ 0` and `x = y² ∨ x = -y²`, then `x = y²`. -/
private lemma eq_sq_of_nonneg_of_or {x y : ℤ} (hx : 0 ≤ x)
    (h : x = y ^ 2 ∨ x = -y ^ 2) : x = y ^ 2 := by
  rcases h with h | h
  · exact h
  · have hneg : -y ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg y)
    have hx_le : x ≤ 0 := h ▸ hneg
    have hx_eq_zero : x = 0 := le_antisymm hx_le hx
    have hy_sq_zero : y ^ 2 = 0 := by linarith [hx_eq_zero, h]
    have hy_zero : y = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hy_sq_zero
    rw [hx_eq_zero, hy_zero]; ring

/-- Discharge of `Fermat42SubCaseB_squareSplit`. -/
theorem fermat42SubCaseB_squareSplit_holds : Fermat42SubCaseB_squareSplit := by
  intro m n b hm_nn hn_pos hmn_coprime hm_odd hn_even hb_sq
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hn_even
  subst hk
  have hk_pos : 0 < k := by linarith
  have hmk_coprime : IsCoprime m k := hmn_coprime.of_mul_right_right
  have hb_sq_mk : b ^ 2 = 4 * (m * k) := by linarith
  have h_two_dvd_bsq : (2 : ℤ) ∣ b ^ 2 := ⟨2 * (m * k), by linarith⟩
  have h_two_dvd_b : (2 : ℤ) ∣ b :=
    Int.Prime.dvd_pow' Nat.prime_two h_two_dvd_bsq
  obtain ⟨b₀, hb₀⟩ := h_two_dvd_b
  have hb0_sq : b₀ ^ 2 = m * k := by
    have h1 : (2 * b₀) ^ 2 = 4 * (m * k) := by rw [← hb₀]; exact hb_sq_mk
    linarith [h1]
  have hmk_gcd : Int.gcd m k = 1 := isCoprime_iff_gcd_eq_one.mp hmk_coprime
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one hmk_gcd hb0_sq.symm
  have hkm_coprime : IsCoprime k m := hmk_coprime.symm
  have hkm_gcd : Int.gcd k m = 1 := isCoprime_iff_gcd_eq_one.mp hkm_coprime
  have hb0_sq' : k * m = b₀ ^ 2 := by linarith
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one hkm_gcd hb0_sq'
  have hm_eq : m = i ^ 2 := eq_sq_of_nonneg_of_or hm_nn hi
  have hk_eq : k = j ^ 2 := eq_sq_of_nonneg_of_or hk_pos.le hj
  have hb0_sq'' : b₀ ^ 2 = (i * j) ^ 2 := by
    rw [hb0_sq, hm_eq, hk_eq]; ring
  have hb0_abs : b₀ = i * j ∨ b₀ = -(i * j) := by
    have h : (b₀ - i * j) * (b₀ + i * j) = 0 := by
      have : b₀ ^ 2 - (i * j) ^ 2 = 0 := by rw [hb0_sq'']; ring
      linear_combination this
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  rcases hb0_abs with hb₀_eq | hb₀_neg
  · refine ⟨i, j, hm_eq, ?_, ?_⟩
    · rw [hk_eq]
    · rw [hb₀, hb₀_eq]; ring
  · refine ⟨i, -j, hm_eq, ?_, ?_⟩
    · rw [hk_eq]; ring
    · rw [hb₀, hb₀_neg]; ring

/-- Discharge of `Fermat42SubCaseA_squareSplit`. -/
theorem fermat42SubCaseA_squareSplit_holds : Fermat42SubCaseA_squareSplit := by
  intro m k b hm_minus_nn hm_plus_nn hpair_coprime hb_sq
  have h_gcd : Int.gcd (m - 2 * k) (m + 2 * k) = 1 :=
    isCoprime_iff_gcd_eq_one.mp hpair_coprime
  have h_eq : (m - 2 * k) * (m + 2 * k) = b ^ 2 := hb_sq.symm
  obtain ⟨s, hs⟩ := Int.sq_of_gcd_eq_one h_gcd h_eq
  have h_gcd_sym : Int.gcd (m + 2 * k) (m - 2 * k) = 1 :=
    isCoprime_iff_gcd_eq_one.mp hpair_coprime.symm
  have h_eq_sym : (m + 2 * k) * (m - 2 * k) = b ^ 2 := by linarith
  obtain ⟨t, ht⟩ := Int.sq_of_gcd_eq_one h_gcd_sym h_eq_sym
  have hs_eq : m - 2 * k = s ^ 2 := eq_sq_of_nonneg_of_or hm_minus_nn hs
  have ht_eq : m + 2 * k = t ^ 2 := eq_sq_of_nonneg_of_or hm_plus_nn ht
  have hb_sq' : b ^ 2 = (s * t) ^ 2 := by rw [hb_sq, hs_eq, ht_eq]; ring
  have hb_cases : b = s * t ∨ b = -(s * t) := by
    have h : (b - s * t) * (b + s * t) = 0 := by linear_combination hb_sq'
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  have hs_sq_coprime : IsCoprime (s ^ 2) (t ^ 2) := by
    rw [← hs_eq, ← ht_eq]; exact hpair_coprime
  have hst_coprime : IsCoprime s t := by
    rw [show s ^ 2 = s * s from sq s, show t ^ 2 = t * t from sq t] at hs_sq_coprime
    exact (hs_sq_coprime.of_mul_left_left).of_mul_right_left
  rcases hb_cases with hb_eq | hb_neg
  · exact ⟨s, t, hs_eq, ht_eq, hb_eq.symm, hst_coprime⟩
  · refine ⟨-s, t, ?_, ht_eq, ?_, ?_⟩
    · rw [hs_eq]; ring
    · rw [hb_neg]; ring
    · exact hst_coprime.neg_left

/-- **Helper**: for coprime `u, v ≥ 0` with `uv = c²`, we have
`u = e²` and `v = f²` for some `e, f` with `ef = ±c`. -/
private lemma coprime_mul_eq_sq_split {u v c : ℤ}
    (hu_nn : 0 ≤ u) (hv_nn : 0 ≤ v) (huv_coprime : IsCoprime u v)
    (huv : u * v = c ^ 2) :
    ∃ e f : ℤ, u = e ^ 2 ∧ v = f ^ 2 ∧ (e * f = c ∨ e * f = -c) := by
  have h_gcd : Int.gcd u v = 1 := isCoprime_iff_gcd_eq_one.mp huv_coprime
  obtain ⟨e, he⟩ := Int.sq_of_gcd_eq_one h_gcd huv
  have h_gcd' : Int.gcd v u = 1 := isCoprime_iff_gcd_eq_one.mp huv_coprime.symm
  have huv' : v * u = c ^ 2 := by linarith
  obtain ⟨f, hf⟩ := Int.sq_of_gcd_eq_one h_gcd' huv'
  have he_eq : u = e ^ 2 := eq_sq_of_nonneg_of_or hu_nn he
  have hf_eq : v = f ^ 2 := eq_sq_of_nonneg_of_or hv_nn hf
  have h_prod : (e * f) ^ 2 = c ^ 2 := by
    have : (e * f) ^ 2 = e ^ 2 * f ^ 2 := by ring
    rw [this, ← he_eq, ← hf_eq, huv]
  have h_cases : e * f = c ∨ e * f = -c := by
    have h : (e * f - c) * (e * f + c) = 0 := by linear_combination h_prod
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  exact ⟨e, f, he_eq, hf_eq, h_cases⟩

/-- **Discharge of `Fermat42SubCaseB_fourthPowerSplit`**.
Iterates `coprime_mul_eq_sq_split` twice (on `uv = (i²)²` then on
the roots via `|e|·|f| = i²`), with sign adjustment. -/
theorem fermat42SubCaseB_fourthPowerSplit_holds :
    Fermat42SubCaseB_fourthPowerSplit := by
  intro a i j ha_pos hi_odd hj_ne haij_coprime ha_eq
  have hj_sq_pos : 0 < j ^ 2 := by positivity
  have hi_ne : i ≠ 0 := by
    intro h; rw [h] at hi_odd; norm_num at hi_odd
  have hi_sq_pos : 0 < i ^ 2 := by positivity
  have ha_sq_eq : a ^ 2 = i ^ 4 + 4 * j ^ 4 := by linarith
  have ha_ge : 2 * j ^ 2 < a := by
    have h1 : (2 * j ^ 2) ^ 2 < a ^ 2 := by
      rw [ha_sq_eq]
      have h2 : (2 * j ^ 2) ^ 2 = 4 * j ^ 4 := by ring
      have hi4_pos : 0 < i ^ 4 := by positivity
      linarith
    nlinarith [h1, sq_nonneg (2 * j ^ 2), ha_pos]
  have ha_minus_pos : 0 < a - 2 * j ^ 2 := by linarith
  have ha_plus_pos : 0 < a + 2 * j ^ 2 := by positivity
  have h_prod_sq : (a - 2 * j ^ 2) * (a + 2 * j ^ 2) = (i ^ 2) ^ 2 := by
    have h : (a - 2 * j ^ 2) * (a + 2 * j ^ 2) = a ^ 2 - 4 * j ^ 4 := by ring
    rw [h, show (i ^ 2 : ℤ) ^ 2 = i ^ 4 from by ring]; linarith
  -- a odd.
  have ha_odd : a % 2 = 1 := by
    have h_i2_odd : i ^ 2 % 2 = 1 := by
      rw [show i ^ 2 = i * i from sq i, Int.mul_emod, hi_odd]; decide
    have h_i4_odd : i ^ 4 % 2 = 1 := by
      rw [show i ^ 4 = i ^ 2 * i ^ 2 from by ring, Int.mul_emod, h_i2_odd]; decide
    have h_4j4_even : (4 * j ^ 4) % 2 = 0 := by
      rw [show (4 : ℤ) * j ^ 4 = 2 * (2 * j ^ 4) from by ring]
      exact Int.mul_emod_right 2 _
    have h_asq_odd : a ^ 2 % 2 = 1 := by
      rw [ha_sq_eq, Int.add_emod, h_i4_odd, h_4j4_even]; decide
    rcases Int.emod_two_eq_zero_or_one a with h | h
    · exfalso
      have : a ^ 2 % 2 = 0 := by
        rw [show a ^ 2 = a * a from sq a, Int.mul_emod, h]; decide
      rw [this] at h_asq_odd; norm_num at h_asq_odd
    · exact h
  -- Coprime pair (a - 2j², a + 2j²).
  have hpair : IsCoprime (a - 2 * j ^ 2) (a + 2 * j ^ 2) := by
    have hdiff_odd : (a - 2 * j ^ 2) % 2 = 1 := by
      have h_2jsq_even : (2 * j ^ 2) % 2 = 0 := Int.mul_emod_right 2 _
      rw [Int.sub_emod, ha_odd, h_2jsq_even]; rfl
    have hdiff_two : IsCoprime (a - 2 * j ^ 2) (2 : ℤ) := by
      refine (Int.isCoprime_iff_gcd_eq_one).mpr ?_
      rw [Int.gcd]
      have h2 : Int.natAbs 2 = 2 := rfl
      rw [h2]
      exact Nat.Coprime.symm
        (Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr (Int.odd_iff.mpr hdiff_odd)))
    have ha_j : IsCoprime a j := haij_coprime.of_mul_right_right
    have ha_jsq : IsCoprime a (j ^ 2) := by
      rw [show (j : ℤ) ^ 2 = j * j from sq j]
      exact ha_j.mul_right ha_j
    have hdiff_jsq : IsCoprime (a - 2 * j ^ 2) (j ^ 2) := by
      have : a - 2 * j ^ 2 = a + (-2) * j ^ 2 := by ring
      rw [this]; exact ha_jsq.add_mul_right_left (-2)
    have hdiff_4jsq : IsCoprime (a - 2 * j ^ 2) (4 * j ^ 2) := by
      have h22 : IsCoprime (a - 2 * j ^ 2) ((2 : ℤ) * 2) :=
        hdiff_two.mul_right hdiff_two
      have h_rw : (4 : ℤ) * j ^ 2 = (2 * 2) * (j ^ 2) := by ring
      rw [h_rw]
      exact h22.mul_right hdiff_jsq
    have h_sum_rw : a + 2 * j ^ 2 = 4 * j ^ 2 + 1 * (a - 2 * j ^ 2) := by ring
    rw [h_sum_rw]
    exact hdiff_4jsq.add_mul_right_right 1
  -- First iteration: `(a-2j²)(a+2j²) = (i²)²`.
  obtain ⟨e, f, he_eq, hf_eq, _⟩ :=
    coprime_mul_eq_sq_split ha_minus_pos.le ha_plus_pos.le hpair h_prod_sq
  -- Define e' = |e|, f' = |f| (nonneg).
  set e' : ℤ := |e| with he'_def
  set f' : ℤ := |f| with hf'_def
  have he'_nn : 0 ≤ e' := abs_nonneg e
  have hf'_nn : 0 ≤ f' := abs_nonneg f
  have he'_sq : e' ^ 2 = e ^ 2 := sq_abs e
  have hf'_sq : f' ^ 2 = f ^ 2 := sq_abs f
  have hu_e' : a - 2 * j ^ 2 = e' ^ 2 := by rw [he'_sq]; exact he_eq
  have hv_f' : a + 2 * j ^ 2 = f' ^ 2 := by rw [hf'_sq]; exact hf_eq
  -- e' · f' = i² (nonneg since both nonneg).
  have hef'_prod : e' * f' = i ^ 2 := by
    have h1 : (e' * f') ^ 2 = (i ^ 2) ^ 2 := by
      have hef_sq : (e' * f') ^ 2 = e' ^ 2 * f' ^ 2 := by ring
      rw [hef_sq, ← hu_e', ← hv_f']
      exact h_prod_sq
    have h_ef_nn : 0 ≤ e' * f' := mul_nonneg he'_nn hf'_nn
    have h_isq_nn : 0 ≤ i ^ 2 := sq_nonneg i
    have h2 : (e' * f' - i ^ 2) * (e' * f' + i ^ 2) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · -- e'f' + i² = 0 with both nonneg → both zero; contradiction with i ≠ 0.
      have h_sum : e' * f' + i ^ 2 = 0 := h
      have h_isq_zero : i ^ 2 = 0 := by linarith
      have : i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_isq_zero
      exact absurd this hi_ne
  -- Coprime e', f' (from coprime e, f via squares; and e', f' = |e|, |f|).
  have hef_coprime : IsCoprime e f := by
    have h_sq_coprime : IsCoprime (e ^ 2) (f ^ 2) := by
      rw [← he_eq, ← hf_eq]; exact hpair
    rw [show e ^ 2 = e * e from sq e, show f ^ 2 = f * f from sq f] at h_sq_coprime
    exact (h_sq_coprime.of_mul_left_left).of_mul_right_left
  have hef'_coprime : IsCoprime e' f' := by
    rw [he'_def, hf'_def]
    rcases abs_cases e with ⟨he_abs, _⟩ | ⟨he_abs, _⟩
    · rcases abs_cases f with ⟨hf_abs, _⟩ | ⟨hf_abs, _⟩
      · rw [he_abs, hf_abs]; exact hef_coprime
      · rw [he_abs, hf_abs]; exact hef_coprime.neg_right
    · rcases abs_cases f with ⟨hf_abs, _⟩ | ⟨hf_abs, _⟩
      · rw [he_abs, hf_abs]; exact hef_coprime.neg_left
      · rw [he_abs, hf_abs]; exact (hef_coprime.neg_left).neg_right
  -- Second iteration: e' · f' = i² = c² with c = i.
  obtain ⟨p, q, hp_eq, hq_eq, h_pq_cases⟩ :=
    coprime_mul_eq_sq_split he'_nn hf'_nn hef'_coprime hef'_prod
  -- Recover u = p⁴, v = q⁴.
  have hu_p4 : a - 2 * j ^ 2 = p ^ 4 := by
    rw [hu_e', hp_eq]; ring
  have hv_q4 : a + 2 * j ^ 2 = q ^ 4 := by
    rw [hv_f', hq_eq]; ring
  -- Sign adjustment for pq = i.
  rcases h_pq_cases with hpq_pos | hpq_neg
  · exact ⟨p, q, hpq_pos, hu_p4, hv_q4⟩
  · refine ⟨-p, q, ?_, ?_, hv_q4⟩
    · rw [neg_mul]; linarith
    · rw [hu_p4]; ring

end Fermat42Sub

/-! ## Section: Fermat42DoubleImpossible_2026_11_13 -/

namespace Fermat42Sub
open Int

/-- **Parity reduction for Fermat42Double**: both `s` and `t` must be odd. -/
theorem fermat42Double_parity {s t a : ℤ} (hs_ne : s ≠ 0) (ht_ne : t ≠ 0)
    (hst_coprime : IsCoprime s t)
    (ha_eq : 2 * a ^ 2 = s ^ 4 + t ^ 4) :
    s % 2 = 1 ∧ t % 2 = 1 := by
  by_contra h_not_both
  push_neg at h_not_both
  have hs_par : s % 2 = 0 ∨ s % 2 = 1 := Int.emod_two_eq_zero_or_one s
  have ht_par : t % 2 = 0 ∨ t % 2 = 1 := Int.emod_two_eq_zero_or_one t
  rcases hs_par with hs_ev | hs_od
  · rcases ht_par with ht_ev | ht_od
    · have hs_dvd : (2 : ℤ) ∣ s := Int.dvd_of_emod_eq_zero hs_ev
      have ht_dvd : (2 : ℤ) ∣ t := Int.dvd_of_emod_eq_zero ht_ev
      have h_gcd : (2 : ℤ) ∣ (Int.gcd s t : ℤ) := Int.dvd_coe_gcd hs_dvd ht_dvd
      rw [Int.isCoprime_iff_gcd_eq_one.mp hst_coprime] at h_gcd
      norm_num at h_gcd
    · have h_s4_even : s ^ 4 % 2 = 0 := by
        rw [show s ^ 4 = s * s * s * s from by ring]
        rw [Int.mul_emod, Int.mul_emod (s * s) s, Int.mul_emod s s, hs_ev]; rfl
      have h_t4_odd : t ^ 4 % 2 = 1 := by
        have h_t2 : t ^ 2 % 2 = 1 := by
          rw [show t ^ 2 = t * t from sq t, Int.mul_emod, ht_od]; decide
        rw [show t ^ 4 = t ^ 2 * t ^ 2 from by ring, Int.mul_emod, h_t2]; decide
      have h_sum_odd : (s ^ 4 + t ^ 4) % 2 = 1 := by
        rw [Int.add_emod, h_s4_even, h_t4_odd]; rfl
      have h_2asq_even : (2 * a ^ 2) % 2 = 0 := Int.mul_emod_right 2 _
      rw [ha_eq] at h_2asq_even
      rw [h_sum_odd] at h_2asq_even
      norm_num at h_2asq_even
  · rcases ht_par with ht_ev | ht_od
    · have h_s4_odd : s ^ 4 % 2 = 1 := by
        have h_s2 : s ^ 2 % 2 = 1 := by
          rw [show s ^ 2 = s * s from sq s, Int.mul_emod, hs_od]; decide
        rw [show s ^ 4 = s ^ 2 * s ^ 2 from by ring, Int.mul_emod, h_s2]; decide
      have h_t4_even : t ^ 4 % 2 = 0 := by
        rw [show t ^ 4 = t * t * t * t from by ring]
        rw [Int.mul_emod, Int.mul_emod (t * t) t, Int.mul_emod t t, ht_ev]; rfl
      have h_sum_odd : (s ^ 4 + t ^ 4) % 2 = 1 := by
        rw [Int.add_emod, h_s4_odd, h_t4_even]; rfl
      have h_2asq_even : (2 * a ^ 2) % 2 = 0 := Int.mul_emod_right 2 _
      rw [ha_eq] at h_2asq_even
      rw [h_sum_odd] at h_2asq_even
      norm_num at h_2asq_even
    · exact h_not_both hs_od ht_od

/-- Helper: `s % 2 = 1 → s² % 8 = 1`. -/
private lemma odd_sq_mod_eight (s : ℤ) (hs : s % 2 = 1) : s ^ 2 % 8 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, s = 2 * k + 1 := ⟨s / 2, by omega⟩
  subst hk
  have h_expand : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
  rw [h_expand]
  rcases Int.emod_two_eq_zero_or_one k with hk_ev | hk_od
  · obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    subst hj
    have h : 4 * (2 * j) * (2 * j + 1) + 1 = 8 * (j * (2 * j + 1)) + 1 := by ring
    rw [h]; omega
  · obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    subst hj
    have h : 4 * (2 * j + 1) * (2 * j + 1 + 1) + 1 = 8 * ((2 * j + 1) * (j + 1)) + 1 := by
      ring
    rw [h]; omega

/-- **`u` mod-4 characterization**. -/
theorem fermat42Double_u_mod_four {s t a : ℤ} (hs_odd : s % 2 = 1)
    (ht_odd : t % 2 = 1) (ha_eq : 2 * a ^ 2 = s ^ 4 + t ^ 4) :
    ∀ u : ℤ, 2 * u = s ^ 2 + t ^ 2 → u % 4 = 1 := by
  intro u hu_def
  have h_ssq_mod : s ^ 2 % 8 = 1 := odd_sq_mod_eight s hs_odd
  have h_tsq_mod : t ^ 2 % 8 = 1 := odd_sq_mod_eight t ht_odd
  omega

/-- **Key lemma**: `x² = 5y²` has only the trivial solution `x = y = 0` in ℤ.

Proof via infinite descent: `5 ∣ x² → 5 ∣ x` (5 prime), so `x = 5x'`;
then `25 x'² = 5 y²`, i.e., `5 x'² = y²`, so `5 ∣ y`, `y = 5y'`;
then `x'² = 5 y'²` with `|y'| < |y|`.  By strong induction on
`y.natAbs`, we get `y = 0`, hence `x = 0`. -/
theorem int_sq_eq_five_sq_imp_zero : ∀ (y : ℤ) (x : ℤ),
    x ^ 2 = 5 * y ^ 2 → x = 0 ∧ y = 0 := by
  -- Strong induction on y.natAbs.
  have H : ∀ n : ℕ, ∀ (y : ℤ), y.natAbs = n → ∀ (x : ℤ),
      x ^ 2 = 5 * y ^ 2 → x = 0 ∧ y = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hn x h
      by_cases hy_zero : y = 0
      · refine ⟨?_, hy_zero⟩
        rw [hy_zero] at h
        simp at h
        exact h
      · exfalso
        have h_five_prime : Prime (5 : ℤ) := by
          rw [Int.prime_iff_natAbs_prime]; decide
        have h_dvd_xsq : (5 : ℤ) ∣ x ^ 2 := ⟨y ^ 2, h⟩
        have h_dvd_x : (5 : ℤ) ∣ x :=
          h_five_prime.dvd_of_dvd_pow h_dvd_xsq
        obtain ⟨x', hx'⟩ := h_dvd_x
        have h_x'_eq : 5 * x' ^ 2 = y ^ 2 := by
          have h1 : (5 * x') ^ 2 = 5 * y ^ 2 := by rw [← hx']; exact h
          nlinarith [h1]
        have h_dvd_ysq : (5 : ℤ) ∣ y ^ 2 := ⟨x' ^ 2, h_x'_eq.symm⟩
        have h_dvd_y : (5 : ℤ) ∣ y :=
          h_five_prime.dvd_of_dvd_pow h_dvd_ysq
        obtain ⟨y', hy'⟩ := h_dvd_y
        have h_new : x' ^ 2 = 5 * y' ^ 2 := by
          have h2 : y ^ 2 = (5 * y') ^ 2 := by rw [← hy']
          rw [h2] at h_x'_eq
          nlinarith [h_x'_eq]
        have hy'_natAbs_lt : y'.natAbs < n := by
          rw [← hn, hy', Int.natAbs_mul]
          have h5 : Int.natAbs 5 = 5 := rfl
          rw [h5]
          have hy'_ne : y' ≠ 0 := by
            intro hz
            rw [hz, mul_zero] at hy'
            exact hy_zero hy'
          have hy'_pos : 0 < y'.natAbs := Int.natAbs_pos.mpr hy'_ne
          omega
        have ih_result := ih y'.natAbs hy'_natAbs_lt y' rfl x' h_new
        have hy'_zero : y' = 0 := ih_result.2
        rw [hy'_zero, mul_zero] at hy'
        exact hy_zero hy'
  intro y x hxy
  exact H y.natAbs y rfl x hxy

/-- **Key quadratic lemma**: `p² + 4pq - q² = 0` has only the trivial solution
`p = q = 0` in ℤ.

Proof: Rearrange `(p + 2q)² = p² + 4pq + 4q² = q² + 5q² = ... wait`.
Actually: `p² + 4pq - q² = 0` means `p² + 4pq + 4q² = 5q²`, i.e.,
`(p + 2q)² = 5q²`.  By `int_sq_eq_five_sq_imp_zero` applied to
`(p + 2q, q)`: `p + 2q = 0` and `q = 0`, hence `p = 0`. -/
theorem fermat42_key_quadratic_no_solutions (p q : ℤ) (h : p ^ 2 + 4 * p * q - q ^ 2 = 0) :
    p = 0 ∧ q = 0 := by
  have h_eq : (p + 2 * q) ^ 2 = 5 * q ^ 2 := by linear_combination h
  obtain ⟨h1, h2⟩ := int_sq_eq_five_sq_imp_zero q (p + 2 * q) h_eq
  refine ⟨?_, h2⟩
  linarith

/-- **Variant: `p² - 4pq - q² = 0` also has only `p = q = 0`.**
By the substitution `p → -p`: `(-p)² - 4(-p)q - q² = p² + 4pq - q² = 0`,
reducing to the prior lemma. -/
theorem fermat42_key_quadratic_variant (p q : ℤ) (h : p ^ 2 - 4 * p * q - q ^ 2 = 0) :
    p = 0 ∧ q = 0 := by
  have h' : (-p) ^ 2 + 4 * (-p) * q - q ^ 2 = 0 := by linear_combination h
  obtain ⟨hnp, hq⟩ := fermat42_key_quadratic_no_solutions (-p) q h'
  refine ⟨?_, hq⟩
  linarith

/-- **Pythagorean descent assembler (named sub-gap)** — the ~200-line
assembly that takes the Fermat42Double hypothesis, runs
`coprime_classification'` on `(u, v, a)`, writes `n = 2k`, performs the
coprime-factorization case analysis on `(t - s)(t + s) = 8mk` and
`(m - 2k)² - s² = 8k²`, and in each case derives either `k = 0`
(immediate contradiction) or produces integers `(p, q)` satisfying
`p² + 4pq - q² = 0` (closed via `fermat42_key_quadratic_no_solutions`).

This is the mechanical case-enumeration piece; its ~200-line
discharge is left to a dedicated session.  Note that the *hard
mathematical content* — the irrationality of √5 forcing
`p² + 4pq - q² = 0 ↔ p = q = 0` — is already fully proved above
(`int_sq_eq_five_sq_imp_zero` + `fermat42_key_quadratic_no_solutions`). -/
def Fermat42DoubleAssembler : Prop :=
  ∀ s t a : ℤ, s ≠ 0 → t ≠ 0 → a ≠ 0 → IsCoprime s t → s ^ 2 ≠ t ^ 2 →
    s % 2 = 1 → t % 2 = 1 →
    2 * a ^ 2 = s ^ 4 + t ^ 4 →
    (∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ p ^ 2 + 4 * p * q - q ^ 2 = 0) ∨
    (∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ p ^ 2 - 4 * p * q - q ^ 2 = 0)

/-- **`Fermat42Double_impossible` holds** conditional on the
Pythagorean assembler.  Composition: parity reduction forces `s, t`
odd, then the assembler produces either variant of the key quadratic,
and the key-quadratic lemma forces `p = q = 0`, contradicting the
assembler's output. -/
theorem fermat42Double_impossible_of_assembler
    (hAssemble : Fermat42DoubleAssembler) :
    Fermat42Double_impossible := by
  intro s t a hs_ne ht_ne ha_ne hst_coprime hst_sq_ne h_eq
  obtain ⟨hs_odd, ht_odd⟩ :=
    fermat42Double_parity hs_ne ht_ne hst_coprime h_eq
  rcases hAssemble s t a hs_ne ht_ne ha_ne hst_coprime hst_sq_ne hs_odd ht_odd h_eq
      with ⟨p, q, hpq_ne, hquad⟩ | ⟨p, q, hpq_ne, hquad⟩
  · obtain ⟨hp, hq⟩ := fermat42_key_quadratic_no_solutions p q hquad
    rcases hpq_ne with h | h
    · exact h hp
    · exact h hq
  · obtain ⟨hp, hq⟩ := fermat42_key_quadratic_variant p q hquad
    rcases hpq_ne with h | h
    · exact h hp
    · exact h hq

/-- **Reusable Pythagorean setup** — from the Fermat42Double hypothesis
with `a > 0, s² < t²`, produces `(m, k)` with the full descent-chain
identities ready for Stage 2 / descent step application. -/
private theorem fermat42Double_pythagorean_setup
    (s t a : ℤ) (hs_ne : s ≠ 0) (ht_ne : t ≠ 0) (ha_pos : 0 < a)
    (hst_coprime : IsCoprime s t) (hst_lt : s ^ 2 < t ^ 2)
    (hs_odd : s % 2 = 1) (ht_odd : t % 2 = 1)
    (h_eq : 2 * a ^ 2 = s ^ 4 + t ^ 4) :
    ∃ m k : ℤ, 0 < m ∧ 0 < k ∧ m % 2 = 1 ∧ IsCoprime m k ∧
      s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2 ∧
      t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2 ∧
      a = m ^ 2 + 4 * k ^ 2 := by
  have hs2_mod : s ^ 2 % 2 = 1 := by
    rw [show s ^ 2 = s * s from sq s, Int.mul_emod, hs_odd]; decide
  have ht2_mod : t ^ 2 % 2 = 1 := by
    rw [show t ^ 2 = t * t from sq t, Int.mul_emod, ht_odd]; decide
  have h2_dvd_sum : (2 : ℤ) ∣ (s ^ 2 + t ^ 2) := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.add_emod, hs2_mod, ht2_mod]; decide
  obtain ⟨u, hu_def⟩ := h2_dvd_sum
  have h2_dvd_diff : (2 : ℤ) ∣ (t ^ 2 - s ^ 2) := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.sub_emod, ht2_mod, hs2_mod]; decide
  obtain ⟨v, hv_def⟩ := h2_dvd_diff
  have hs2_pos : 0 < s ^ 2 :=
    (sq_nonneg s).lt_of_ne (fun h => hs_ne (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h.symm))
  have ht2_pos : 0 < t ^ 2 :=
    (sq_nonneg t).lt_of_ne (fun h => ht_ne (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h.symm))
  have hu_pos : 0 < u := by linarith
  have hv_pos : 0 < v := by linarith
  have h_sum_eq : u + v = t ^ 2 := by linarith
  have h_diff_eq : u - v = s ^ 2 := by linarith
  have hu_mod4 : u % 4 = 1 :=
    fermat42Double_u_mod_four hs_odd ht_odd h_eq u (by linarith)
  have hu_odd : u % 2 = 1 := by omega
  have hv_mod4 : v % 4 = 0 := by
    have h8s : s ^ 2 % 8 = 1 := odd_sq_mod_eight s hs_odd
    have h8t : t ^ 2 % 8 = 1 := odd_sq_mod_eight t ht_odd
    omega
  have h_pyth : u ^ 2 + v ^ 2 = a ^ 2 := by
    have h1 : (2 * u) ^ 2 + (2 * v) ^ 2 = 4 * a ^ 2 := by
      rw [← hu_def]
      have hv2 : 2 * v = t ^ 2 - s ^ 2 := by linarith
      rw [hv2]
      have : (s ^ 2 + t ^ 2) ^ 2 + (t ^ 2 - s ^ 2) ^ 2 = 2 * (s ^ 4 + t ^ 4) := by ring
      rw [this, ← h_eq]; ring
    nlinarith [h1]
  -- gcd(u, v) = 1 via Bezout from IsCoprime (s²) (t²) and u ± v identities.
  have huv_gcd : Int.gcd u v = 1 := by
    have hst2_cop : IsCoprime (s ^ 2) (t ^ 2) := hst_coprime.pow
    obtain ⟨x, y, hxy⟩ := hst2_cop
    have hgu : (Int.gcd u v : ℤ) ∣ u := Int.gcd_dvd_left u v
    have hgv : (Int.gcd u v : ℤ) ∣ v := Int.gcd_dvd_right u v
    have hdvd_1 : (Int.gcd u v : ℤ) ∣ (1 : ℤ) := by
      have : (1 : ℤ) = (u - v) * x + (u + v) * y := by rw [h_diff_eq, h_sum_eq]; linarith
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_left (dvd_sub hgu hgv) _)
                    (dvd_mul_of_dvd_left (dvd_add hgu hgv) _)
    have : Int.gcd u v ∣ 1 := by exact_mod_cast hdvd_1
    exact Nat.dvd_one.mp this
  have huv_coprime : IsCoprime u v := Int.isCoprime_iff_gcd_eq_one.mpr huv_gcd
  -- Pythagorean classification on (u, v, a) directly.
  have h_pyth_tri : PythagoreanTriple u v a := by
    show u * u + v * v = a * a
    nlinarith [h_pyth]
  obtain ⟨m, n, hv_eq, hu_eq, ha_eq_mn, hmn_gcd, hmn_par, hm_nn⟩ :=
    h_pyth_tri.coprime_classification' huv_gcd hu_odd ha_pos
  -- hv_eq : u = m^2 - n^2, hu_eq : v = 2*m*n, ha_eq_mn : a = m^2 + n^2
  -- Wait — the variable names are swapped. Let me re-read.
  -- `coprime_classification'` returns: x = m² - n², y = 2*m*n, z = m² + n².
  -- Applied to h_pyth_tri.symm variant (u, v, a) — but mathlib's PythagoreanTriple x y z
  -- means x² + y² = z². So we want to apply with x = u (odd), y = v, z = a (positive).
  -- The pythagoreanTriple_comm.mp converts PythagoreanTriple v u a to PythagoreanTriple u v a.
  -- So after .mp, triple is (u, v, a) with u odd.
  -- Classification: u = m² - n², v = 2mn, a = m² + n².
  -- So hv_eq : u = m² - n², hu_eq : v = 2*m*n, ha_eq_mn : a = m² + n².
  -- The naming is: first binder is x-equation, second is y-equation, third is z-equation.
  -- Variable names in classification' are also m, n.
  -- m parity: u = m² - n² ≡ 1 mod 4 forces m odd, n even.
  have hmn_coprime : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
  have hm_odd : m % 2 = 1 := by
    rcases hmn_par with ⟨hm_ev, hn_od⟩ | ⟨hm_od, _⟩
    · exfalso
      obtain ⟨m₀, hm₀⟩ : (2 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero hm_ev
      have hm2 : m ^ 2 % 4 = 0 := by
        rw [hm₀]
        have : (2 * m₀) ^ 2 = 4 * (m₀ ^ 2) := by ring
        rw [this, Int.mul_emod_right]
      have hn2 : n ^ 2 % 4 = 1 := by
        have h8 : n ^ 2 % 8 = 1 := odd_sq_mod_eight n hn_od
        omega
      have hu4 : u % 4 = 3 := by rw [hv_eq]; omega
      omega
    · exact hm_od
  have hn_even : n % 2 = 0 := by
    rcases hmn_par with ⟨hm_ev, _⟩ | ⟨_, hn_ev⟩
    · exfalso; omega
    · exact hn_ev
  obtain ⟨k, hk_def⟩ : (2 : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hn_even
  -- m > 0, k > 0 required.
  -- From ha_eq_mn : a = m² + n² = m² + 4k². And a > 0.
  -- From hv_eq : u = m² - n² with u > 0. So m² > n² ≥ 0, m² > 0.
  have hm_ne : m ≠ 0 := by
    intro h
    rw [h] at hv_eq
    simp at hv_eq
    -- hv_eq : u = -n^2, but u > 0 and -n² ≤ 0.
    have : u ≤ 0 := by rw [hv_eq]; nlinarith [sq_nonneg n]
    linarith
  have hm_pos : 0 < m := lt_of_le_of_ne hm_nn (Ne.symm hm_ne)
  have hn_ne : n ≠ 0 := by
    intro h
    rw [h] at hu_eq
    -- hu_eq : v = 2*m*0 = 0, but v > 0.
    simp at hu_eq
    linarith
  have hk_ne : k ≠ 0 := by
    intro h
    rw [h] at hk_def
    simp at hk_def
    exact hn_ne hk_def
  have hk_pos : 0 < k := by
    -- k = n / 2 and n > 0 (since v = 2mn > 0 and m > 0 ⟹ n > 0).
    have hn_pos : 0 < n := by
      by_contra h_not_pos
      push_neg at h_not_pos
      have hn_le : n ≤ 0 := h_not_pos
      have : v ≤ 0 := by
        rw [hu_eq]
        have : 2 * m * n ≤ 0 := by nlinarith
        exact this
      linarith
    have : 0 < 2 * k := by linarith [hk_def ▸ hn_pos]
    linarith
  -- IsCoprime m k: from IsCoprime m n and n = 2k.
  have hmk_coprime : IsCoprime m k := by
    rw [hk_def] at hmn_coprime
    exact hmn_coprime.of_mul_right_right
  -- Derive s² = (m - 2k)² - 8k², t² = (m + 2k)² - 8k².
  have hu_mk : u = m ^ 2 - 4 * k ^ 2 := by rw [hv_eq, hk_def]; ring
  have hv_mk : v = 4 * m * k := by rw [hu_eq, hk_def]; ring
  have hs_sq : s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2 := by
    have : s ^ 2 = u - v := h_diff_eq.symm
    rw [this, hu_mk, hv_mk]; ring
  have ht_sq : t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2 := by
    have : t ^ 2 = u + v := h_sum_eq.symm
    rw [this, hu_mk, hv_mk]; ring
  have ha_mk : a = m ^ 2 + 4 * k ^ 2 := by rw [ha_eq_mn, hk_def]; ring
  exact ⟨m, k, hm_pos, hk_pos, hm_odd, hmk_coprime, hs_sq, ht_sq, ha_mk⟩

/-- **Stage 2 sub-gap** — assumes Pythagorean (m, k) structure as input,
produces the key quadratic witness.  Note: likely vacuously true since
the actual descent produces a smaller `Fermat42Double` instance (see
`Fermat42DoubleDescentStep`), not a key quadratic.  Kept for the
composition theorem `fermat42Double_impossible_of_assembler`. -/
def Fermat42DoubleStage2 : Prop :=
  ∀ s t a m k : ℤ,
    s ≠ 0 → t ≠ 0 → 0 < a →
    IsCoprime s t →
    s ^ 2 < t ^ 2 →
    s % 2 = 1 → t % 2 = 1 →
    0 < m → 0 < k → m % 2 = 1 →
    IsCoprime m k →
    s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2 →
    t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2 →
    a = m ^ 2 + 4 * k ^ 2 →
    2 * a ^ 2 = s ^ 4 + t ^ 4 →
    (∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ p ^ 2 + 4 * p * q - q ^ 2 = 0) ∨
    (∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ p ^ 2 - 4 * p * q - q ^ 2 = 0)

/-- **Stage 1 (quadratic route)**: reduces `Fermat42DoubleAssembler` to
`Fermat42DoubleStage2` via the Pythagorean setup. -/
theorem fermat42Double_assembler_of_stage2
    (hStage2 : Fermat42DoubleStage2) :
    Fermat42DoubleAssembler := by
  intro s t a hs_ne ht_ne ha_ne hst_coprime hst_sq_ne hs_odd ht_odd h_eq
  have h_abs_eq : 2 * |a| ^ 2 = s ^ 4 + t ^ 4 := by rw [sq_abs]; exact h_eq
  have h_abs_pos : 0 < |a| := abs_pos.mpr ha_ne
  rcases lt_trichotomy (s ^ 2) (t ^ 2) with h_lt | h_eq2 | h_gt
  · obtain ⟨m, k, hm_pos, hk_pos, hm_odd, hmk_cop, hs_sq, ht_sq, ha_mk⟩ :=
      fermat42Double_pythagorean_setup s t |a| hs_ne ht_ne h_abs_pos
        hst_coprime h_lt hs_odd ht_odd h_abs_eq
    exact hStage2 s t |a| m k hs_ne ht_ne h_abs_pos hst_coprime h_lt hs_odd ht_odd
      hm_pos hk_pos hm_odd hmk_cop hs_sq ht_sq ha_mk h_abs_eq
  · exact absurd h_eq2 hst_sq_ne
  · have hts_coprime : IsCoprime t s := hst_coprime.symm
    have h_abs_eq_sw : 2 * |a| ^ 2 = t ^ 4 + s ^ 4 := by linarith
    obtain ⟨m, k, hm_pos, hk_pos, hm_odd, hmk_cop, hs_sq, ht_sq, ha_mk⟩ :=
      fermat42Double_pythagorean_setup t s |a| ht_ne hs_ne h_abs_pos
        hts_coprime h_gt ht_odd hs_odd h_abs_eq_sw
    exact hStage2 t s |a| m k ht_ne hs_ne h_abs_pos hts_coprime h_gt ht_odd hs_odd
      hm_pos hk_pos hm_odd hmk_cop hs_sq ht_sq ha_mk h_abs_eq_sw

/-- **Descent factorization facts** — given the Pythagorean (m, k) structure
from Stage 1, derive:
* `(m - 2k)² - s² = 8k²`, factoring as `(m - 2k - s)(m - 2k + s) = 8k²`
* `(m + 2k)² - t² = 8k²`, factoring as `(m + 2k - t)(m + 2k + t) = 8k²`
* Each pair of factors has both elements even (parity: m - 2k, m + 2k odd; s, t odd).
* Each pair's elements are coprime after dividing by 2.

These are the structural prerequisites for the UFD-split Fermat descent. -/
private theorem fermat42Double_descent_factorization_facts
    (s t m k : ℤ) (hs_odd : s % 2 = 1) (ht_odd : t % 2 = 1)
    (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_coprime : IsCoprime m k)
    (hs_sq : s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2)
    (ht_sq : t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2) :
    (m - 2 * k - s) * (m - 2 * k + s) = 8 * k ^ 2 ∧
    (m + 2 * k - t) * (m + 2 * k + t) = 8 * k ^ 2 ∧
    (m - 2 * k - s) % 2 = 0 ∧ (m - 2 * k + s) % 2 = 0 ∧
    (m + 2 * k - t) % 2 = 0 ∧ (m + 2 * k + t) % 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (m - 2k - s)(m - 2k + s) = (m - 2k)² - s² = 8k²
    have h1 : (m - 2 * k - s) * (m - 2 * k + s) = (m - 2 * k) ^ 2 - s ^ 2 := by ring
    rw [h1]; linarith [hs_sq]
  · have h1 : (m + 2 * k - t) * (m + 2 * k + t) = (m + 2 * k) ^ 2 - t ^ 2 := by ring
    rw [h1]; linarith [ht_sq]
  · -- m - 2k - s even: m odd, 2k even, s odd ⟹ odd - even - odd = even.
    omega
  · omega
  · omega
  · omega

/-- **Coprimality lemma** — `IsCoprime (m - 2k) s` from `IsCoprime m k` + identity.

Proof chain:
* `IsCoprime (m - 2k) k` via `IsCoprime.add_mul_right_left`
* `d := gcd(m - 2k, s)` divides `8k²` via `(m - 2k)² - s² = 8k²`
* `d` is coprime to `k` (from `d ∣ (m - 2k)`)
* Hence `d ∣ 8` (dividing 8k² and coprime to `k²`)
* `d` odd (dividing `m - 2k` which is odd) forces `d ∣ gcd(8, odd) = 1`. -/
private theorem fermat42Double_m2k_sub_s_coprime
    (s m k : ℤ) (hs_odd : s % 2 = 1) (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_coprime : IsCoprime m k)
    (hs_sq : s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2) :
    IsCoprime (m - 2 * k) s := by
  -- IsCoprime (m - 2k) k.
  have hmk_sub_cop_k : IsCoprime (m - 2 * k) k := by
    have h_rw : m - 2 * k = m + (-2) * k := by ring
    rw [h_rw]
    exact hmk_coprime.add_mul_right_left (-2)
  -- Apply gcd argument.
  rw [Int.isCoprime_iff_gcd_eq_one]
  set d := Int.gcd (m - 2 * k) s
  have hd_dvd_mk : (d : ℤ) ∣ (m - 2 * k) := Int.gcd_dvd_left (m - 2 * k) s
  have hd_dvd_s : (d : ℤ) ∣ s := Int.gcd_dvd_right (m - 2 * k) s
  -- d | 8k² from d | (m - 2k)² - s² = 8k².
  have hd_dvd_8ksq : (d : ℤ) ∣ 8 * k ^ 2 := by
    have h3 : (m - 2 * k) ^ 2 - s ^ 2 = 8 * k ^ 2 := by linarith [hs_sq]
    rw [← h3]
    exact dvd_sub (dvd_pow hd_dvd_mk (by norm_num))
                  (dvd_pow hd_dvd_s (by norm_num))
  -- d odd via IsCoprime (m - 2k) 2 + divisibility.
  have hm2k_odd : (m - 2 * k) % 2 = 1 := by omega
  have hmk_sub_cop_2 : IsCoprime (m - 2 * k) (2 : ℤ) := by
    obtain ⟨q, hq⟩ : ∃ q, m - 2 * k = 2 * q + 1 := ⟨(m - 2 * k - 1) / 2, by omega⟩
    exact ⟨1, -q, by linarith [hq]⟩
  have hd_cop_2 : IsCoprime (d : ℤ) 2 :=
    hmk_sub_cop_2.of_isCoprime_of_dvd_left hd_dvd_mk
  -- IsCoprime d 8 (from IsCoprime d 2, by cube).
  have hd_cop_8 : IsCoprime (d : ℤ) 8 := by
    have h : IsCoprime (d : ℤ) (2 ^ 3) := hd_cop_2.pow_right
    simpa [show (2 : ℤ) ^ 3 = 8 from by norm_num] using h
  -- IsCoprime d k via IsCoprime (m - 2k) k + divisibility.
  have hd_cop_k : IsCoprime (d : ℤ) k :=
    hmk_sub_cop_k.of_isCoprime_of_dvd_left hd_dvd_mk
  -- IsCoprime d k² (pow of IsCoprime d k).
  have hd_cop_ksq : IsCoprime (d : ℤ) (k ^ 2) := hd_cop_k.pow_right
  -- From d | 8k² and IsCoprime d k²: d | 8.
  have hd_dvd_8 : (d : ℤ) ∣ 8 := by
    have h1 : (d : ℤ) ∣ 8 * k ^ 2 := hd_dvd_8ksq
    exact hd_cop_ksq.dvd_of_dvd_mul_right h1
  -- From d | 8 and IsCoprime d 8: d | 1.
  have : (d : ℤ) ∣ 1 := hd_cop_8.dvd_of_dvd_mul_left (by simpa using hd_dvd_8)
  have h_nat : d ∣ 1 := by exact_mod_cast this
  exact Nat.dvd_one.mp h_nat

/-- **Coprimality lemma (second factorization)** — `IsCoprime (m + 2k) t`
from `IsCoprime m k` + identity `t² = (m + 2k)² - 8k²`.

Proof structure identical to `fermat42Double_m2k_sub_s_coprime` with
`m - 2k → m + 2k` and `s → t`. -/
private theorem fermat42Double_m2k_add_t_coprime
    (t m k : ℤ) (ht_odd : t % 2 = 1) (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_coprime : IsCoprime m k)
    (ht_sq : t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2) :
    IsCoprime (m + 2 * k) t := by
  have hmk_add_cop_k : IsCoprime (m + 2 * k) k := by
    have h_rw : m + 2 * k = m + 2 * k := rfl
    exact hmk_coprime.add_mul_right_left 2
  rw [Int.isCoprime_iff_gcd_eq_one]
  set d := Int.gcd (m + 2 * k) t
  have hd_dvd_mk : (d : ℤ) ∣ (m + 2 * k) := Int.gcd_dvd_left (m + 2 * k) t
  have hd_dvd_t : (d : ℤ) ∣ t := Int.gcd_dvd_right (m + 2 * k) t
  have hd_dvd_8ksq : (d : ℤ) ∣ 8 * k ^ 2 := by
    have h3 : (m + 2 * k) ^ 2 - t ^ 2 = 8 * k ^ 2 := by linarith [ht_sq]
    rw [← h3]
    exact dvd_sub (dvd_pow hd_dvd_mk (by norm_num))
                  (dvd_pow hd_dvd_t (by norm_num))
  have hm2k_odd : (m + 2 * k) % 2 = 1 := by omega
  have hmk_add_cop_2 : IsCoprime (m + 2 * k) (2 : ℤ) := by
    obtain ⟨q, hq⟩ : ∃ q, m + 2 * k = 2 * q + 1 := ⟨(m + 2 * k - 1) / 2, by omega⟩
    exact ⟨1, -q, by linarith [hq]⟩
  have hd_cop_2 : IsCoprime (d : ℤ) 2 :=
    hmk_add_cop_2.of_isCoprime_of_dvd_left hd_dvd_mk
  have hd_cop_8 : IsCoprime (d : ℤ) 8 := by
    have h : IsCoprime (d : ℤ) (2 ^ 3) := hd_cop_2.pow_right
    simpa [show (2 : ℤ) ^ 3 = 8 from by norm_num] using h
  have hd_cop_k : IsCoprime (d : ℤ) k :=
    hmk_add_cop_k.of_isCoprime_of_dvd_left hd_dvd_mk
  have hd_cop_ksq : IsCoprime (d : ℤ) (k ^ 2) := hd_cop_k.pow_right
  have hd_dvd_8 : (d : ℤ) ∣ 8 :=
    hd_cop_ksq.dvd_of_dvd_mul_right hd_dvd_8ksq
  have : (d : ℤ) ∣ 1 := hd_cop_8.dvd_of_dvd_mul_left (by simpa using hd_dvd_8)
  have h_nat : d ∣ 1 := by exact_mod_cast this
  exact Nat.dvd_one.mp h_nat

/-- **Half-factor data (s-side)** — extract `A, B` with
`m - 2k - s = 2A`, `m - 2k + s = 2B`, `A * B = 2k²`, `IsCoprime A B`. -/
private theorem fermat42Double_m2k_half_factors_s
    (s m k : ℤ) (hs_odd : s % 2 = 1) (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_coprime : IsCoprime m k)
    (hs_sq : s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2) :
    ∃ A B : ℤ, m - 2 * k - s = 2 * A ∧ m - 2 * k + s = 2 * B ∧
      A * B = 2 * k ^ 2 ∧ IsCoprime A B := by
  have hAeven : (m - 2 * k - s) % 2 = 0 := by omega
  have hBeven : (m - 2 * k + s) % 2 = 0 := by omega
  obtain ⟨A, hA⟩ : (2 : ℤ) ∣ (m - 2 * k - s) := Int.dvd_of_emod_eq_zero hAeven
  obtain ⟨B, hB⟩ : (2 : ℤ) ∣ (m - 2 * k + s) := Int.dvd_of_emod_eq_zero hBeven
  have hm2k_cop_s : IsCoprime (m - 2 * k) s :=
    fermat42Double_m2k_sub_s_coprime s m k hs_odd hk_pos hm_odd hmk_coprime hs_sq
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · -- A * B = 2k²: compute via 4AB = (m-2k-s)(m-2k+s) = 8k²
    have h4AB : 4 * (A * B) = 8 * k ^ 2 := by
      have h1 : (m - 2 * k - s) * (m - 2 * k + s) = 8 * k ^ 2 := by
        have : (m - 2 * k - s) * (m - 2 * k + s) = (m - 2 * k) ^ 2 - s ^ 2 := by ring
        rw [this]; linarith [hs_sq]
      have h2 : (2 * A) * (2 * B) = 8 * k ^ 2 := by rw [← hA, ← hB]; exact h1
      linarith [h2]
    linarith [h4AB]
  · -- IsCoprime A B: from IsCoprime (m - 2k) s and 2A = m - 2k - s, 2B = m - 2k + s.
    -- gcd(A, B) | A + B = (m - 2k) (via (2A + 2B)/2) and | B - A = s (via (2B - 2A)/2).
    -- So 2·gcd(A, B) | gcd(m - 2k, s) = 1... hmm, gcd(A, B) | gcd(m-2k, s) more precisely.
    -- Use Bezout: IsCoprime (m - 2k) s ⟹ ∃ u v, u(m-2k) + vs = 1.
    --   Then u(2A + 2B)/2... but division by 2 doesn't preserve Bezout.
    -- Alt: ∃ u v, u(m - 2k) + vs = 1. Express via A, B: m - 2k = A + B, s = B - A.
    --   u(A + B) + v(B - A) = 1, i.e., (u - v)A + (u + v)B = 1.
    --   So IsCoprime A B with witnesses (u - v, u + v).
    obtain ⟨u, v, huv⟩ := hm2k_cop_s
    refine ⟨u - v, u + v, ?_⟩
    have h_mk_eq : m - 2 * k = A + B := by linarith [hA, hB]
    have h_s_eq : s = B - A := by linarith [hA, hB]
    have : (u - v) * A + (u + v) * B = u * (m - 2 * k) + v * s := by
      rw [h_mk_eq, h_s_eq]; ring
    rw [this]; exact huv

/-- **Half-factor data (t-side)** — extract `C, D` with
`m + 2k - t = 2C`, `m + 2k + t = 2D`, `C * D = 2k²`, `IsCoprime C D`. -/
private theorem fermat42Double_m2k_half_factors_t
    (t m k : ℤ) (ht_odd : t % 2 = 1) (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_coprime : IsCoprime m k)
    (ht_sq : t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2) :
    ∃ C D : ℤ, m + 2 * k - t = 2 * C ∧ m + 2 * k + t = 2 * D ∧
      C * D = 2 * k ^ 2 ∧ IsCoprime C D := by
  have hCeven : (m + 2 * k - t) % 2 = 0 := by omega
  have hDeven : (m + 2 * k + t) % 2 = 0 := by omega
  obtain ⟨C, hC⟩ : (2 : ℤ) ∣ (m + 2 * k - t) := Int.dvd_of_emod_eq_zero hCeven
  obtain ⟨D, hD⟩ : (2 : ℤ) ∣ (m + 2 * k + t) := Int.dvd_of_emod_eq_zero hDeven
  have hm2k_cop_t : IsCoprime (m + 2 * k) t :=
    fermat42Double_m2k_add_t_coprime t m k ht_odd hk_pos hm_odd hmk_coprime ht_sq
  refine ⟨C, D, hC, hD, ?_, ?_⟩
  · have h4CD : 4 * (C * D) = 8 * k ^ 2 := by
      have h1 : (m + 2 * k - t) * (m + 2 * k + t) = 8 * k ^ 2 := by
        have : (m + 2 * k - t) * (m + 2 * k + t) = (m + 2 * k) ^ 2 - t ^ 2 := by ring
        rw [this]; linarith [ht_sq]
      have h2 : (2 * C) * (2 * D) = 8 * k ^ 2 := by rw [← hC, ← hD]; exact h1
      linarith [h2]
    linarith [h4CD]
  · obtain ⟨u, v, huv⟩ := hm2k_cop_t
    refine ⟨u - v, u + v, ?_⟩
    have h_mk_eq : m + 2 * k = C + D := by linarith [hC, hD]
    have h_t_eq : t = D - C := by linarith [hC, hD]
    have : (u - v) * C + (u + v) * D = u * (m + 2 * k) + v * t := by
      rw [h_mk_eq, h_t_eq]; ring
    rw [this]; exact huv

/-- Helper: `x ≥ 0` and `x = y² ∨ x = -y² → x = y²`. -/
private lemma eq_sq_of_nonneg_of_or' {x y : ℤ} (hx : 0 ≤ x)
    (h : x = y ^ 2 ∨ x = -y ^ 2) : x = y ^ 2 := by
  rcases h with h | h
  · exact h
  · have hneg : -y ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg y)
    have hx_eq_zero : x = 0 := le_antisymm (h ▸ hneg) hx
    have hy_sq_zero : y ^ 2 = 0 := by linarith [hx_eq_zero, h]
    have hy_zero : y = 0 :=
      pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hy_sq_zero
    rw [hx_eq_zero, hy_zero]; ring

/-- Helper: for coprime `u, v ≥ 0` with `uv = c²`: `u = e²`, `v = f²`, `ef = ±c`. -/
private lemma coprime_mul_eq_sq_split_local {u v c : ℤ}
    (hu_nn : 0 ≤ u) (hv_nn : 0 ≤ v) (huv_coprime : IsCoprime u v)
    (huv : u * v = c ^ 2) :
    ∃ e f : ℤ, u = e ^ 2 ∧ v = f ^ 2 ∧ (e * f = c ∨ e * f = -c) := by
  have h_gcd : Int.gcd u v = 1 := isCoprime_iff_gcd_eq_one.mp huv_coprime
  obtain ⟨e, he⟩ := Int.sq_of_gcd_eq_one h_gcd huv
  have h_gcd' : Int.gcd v u = 1 := isCoprime_iff_gcd_eq_one.mp huv_coprime.symm
  have huv' : v * u = c ^ 2 := by linarith
  obtain ⟨f, hf⟩ := Int.sq_of_gcd_eq_one h_gcd' huv'
  have he_eq : u = e ^ 2 := eq_sq_of_nonneg_of_or' hu_nn he
  have hf_eq : v = f ^ 2 := eq_sq_of_nonneg_of_or' hv_nn hf
  have h_prod : (e * f) ^ 2 = c ^ 2 := by
    have : (e * f) ^ 2 = e ^ 2 * f ^ 2 := by ring
    rw [this, ← he_eq, ← hf_eq, huv]
  have h_cases : e * f = c ∨ e * f = -c := by
    have h : (e * f - c) * (e * f + c) = 0 := by linear_combination h_prod
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  exact ⟨e, f, he_eq, hf_eq, h_cases⟩

/-- **UFD split for `A·B = 2k²`** with `A` odd, `B` even, `A, B ≥ 0`, `IsCoprime A B`:
produce `α, β` with `A = β²`, `B = 2α²`, `α·β = ±k`. -/
private theorem fermat42Double_sq_split_two_odd_even
    (A B k : ℤ) (hA_nn : 0 ≤ A) (hB_nn : 0 ≤ B) (hA_odd : A % 2 = 1)
    (hAB_cop : IsCoprime A B) (hAB : A * B = 2 * k ^ 2) (hk_ne : k ≠ 0) :
    ∃ α β : ℤ, A = β ^ 2 ∧ B = 2 * α ^ 2 ∧ (α * β = k ∨ α * β = -k) := by
  have hB_even : B % 2 = 0 := by
    by_contra h
    have hB_odd : B % 2 = 1 := by omega
    have hAB_odd : (A * B) % 2 = 1 := by
      rw [Int.mul_emod, hA_odd, hB_odd]; decide
    have h2k2_even : (2 * k ^ 2) % 2 = 0 := Int.mul_emod_right 2 _
    rw [hAB] at hAB_odd
    rw [hAB_odd] at h2k2_even
    norm_num at h2k2_even
  obtain ⟨B', hB'⟩ : (2 : ℤ) ∣ B := Int.dvd_of_emod_eq_zero hB_even
  have hAB' : A * B' = k ^ 2 := by
    have : A * (2 * B') = 2 * k ^ 2 := by rw [← hB']; exact hAB
    linarith
  have hAB'_cop : IsCoprime A B' := by
    obtain ⟨u, v, huv⟩ := hAB_cop
    -- u*A + v*B = 1 with B = 2B', so u*A + (2v)*B' = 1.
    refine ⟨u, 2 * v, ?_⟩
    have : u * A + 2 * v * B' = u * A + v * B := by rw [hB']; ring
    rw [this]; exact huv
  have hB'_nn : 0 ≤ B' := by nlinarith [hB_nn, hB']
  obtain ⟨β, α, hA_eq, hB'_eq, hcases⟩ :=
    coprime_mul_eq_sq_split_local hA_nn hB'_nn hAB'_cop hAB'
  refine ⟨α, β, hA_eq, ?_, ?_⟩
  · rw [hB', hB'_eq]
  · rcases hcases with h | h
    · left; linarith
    · right; linarith

/-- **Positivity of `m - 2k`** — from the Pythagorean setup (Stage 1 output),
`m > 2k` holds, so `m - 2k > 0`.

Follows from `u = m² - 4k² > 0` (since `u > 0` and `u = m² - n²`, `n = 2k`),
hence `m² > (2k)²`, and `m > 0, k > 0` gives `m > 2k`. -/
private theorem fermat42Double_m_gt_2k
    (m k : ℤ) (hm_pos : 0 < m) (hk_pos : 0 < k)
    (hu_pos : 0 < m ^ 2 - 4 * k ^ 2) :
    2 * k < m := by
  -- m² > 4k² = (2k)². Since m > 0 and 2k > 0, m > 2k.
  have h1 : m ^ 2 > (2 * k) ^ 2 := by nlinarith
  have h2 : 0 < 2 * k := by linarith
  nlinarith [sq_nonneg (m - 2 * k), sq_nonneg (m + 2 * k)]

/-- **Half-factor positivity (s-side)** — `(m - 2k - s)/2 > 0` and `(m - 2k + s)/2 > 0`.

Follows from `m - 2k > 0` (`m > 2k`) and `(m - 2k)² > s²` (from `s² = (m - 2k)² - 8k²`
with `k ≠ 0`), so `m - 2k > |s|`, hence both `m - 2k ± s > 0`. -/
private theorem fermat42Double_half_factors_s_pos
    (s m k A B : ℤ) (hs_ne : s ≠ 0) (hm_pos : 0 < m) (hk_pos : 0 < k)
    (hu_pos : 0 < m ^ 2 - 4 * k ^ 2)
    (hs_sq : s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2)
    (hA : m - 2 * k - s = 2 * A) (hB : m - 2 * k + s = 2 * B) :
    0 < A ∧ 0 < B := by
  have hm2k_pos : 2 * k < m := fermat42Double_m_gt_2k m k hm_pos hk_pos hu_pos
  have h_m2k : 0 < m - 2 * k := by linarith
  have h_sq_lt : s ^ 2 < (m - 2 * k) ^ 2 := by
    have hksq_pos : 0 < 8 * k ^ 2 := by positivity
    linarith [hs_sq]
  -- From h_sq_lt and h_m2k, we have |s| < m - 2k. Both directions follow.
  constructor
  · -- s < m - 2k (then m - 2k - s > 0, so 2A > 0, so A > 0).
    have h : s < m - 2 * k := by nlinarith [h_sq_lt, h_m2k, sq_nonneg (m - 2 * k - s), sq_nonneg (m - 2 * k + s)]
    linarith
  · -- -s < m - 2k (then m - 2k + s > 0, so 2B > 0, so B > 0).
    have h : -s < m - 2 * k := by nlinarith [h_sq_lt, h_m2k, sq_nonneg (m - 2 * k - s), sq_nonneg (m - 2 * k + s)]
    linarith

/-- **Half-factor positivity (t-side)** — mirror of the s-side lemma. -/
private theorem fermat42Double_half_factors_t_pos
    (t m k C D : ℤ) (ht_ne : t ≠ 0) (hm_pos : 0 < m) (hk_pos : 0 < k)
    (ht_sq : t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2)
    (hC : m + 2 * k - t = 2 * C) (hD : m + 2 * k + t = 2 * D) :
    0 < C ∧ 0 < D := by
  have h_m2k_pos : 0 < m + 2 * k := by linarith
  have h_sq_lt : t ^ 2 < (m + 2 * k) ^ 2 := by
    have hksq_pos : 0 < 8 * k ^ 2 := by positivity
    linarith [ht_sq]
  constructor
  · have h : t < m + 2 * k := by
      nlinarith [h_sq_lt, h_m2k_pos, sq_nonneg (m + 2 * k - t), sq_nonneg (m + 2 * k + t)]
    linarith
  · have h : -t < m + 2 * k := by
      nlinarith [h_sq_lt, h_m2k_pos, sq_nonneg (m + 2 * k - t), sq_nonneg (m + 2 * k + t)]
    linarith

/-- **S-side quadruple extraction** — given the Pythagorean setup, extract
`(α, β)` with `A = β²` or `A = 2α²` (parity case) and `α·β = ±k`.

Combines half-factor extraction, positivity, and UFD split. -/
private theorem fermat42Double_s_side_split
    (s m k : ℤ) (hs_ne : s ≠ 0) (hs_odd : s % 2 = 1)
    (hm_pos : 0 < m) (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_cop : IsCoprime m k)
    (hu_pos : 0 < m ^ 2 - 4 * k ^ 2)
    (hs_sq : s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2) :
    ∃ A B α β : ℤ, m - 2 * k - s = 2 * A ∧ m - 2 * k + s = 2 * B ∧
      0 < A ∧ 0 < B ∧ IsCoprime A B ∧ A * B = 2 * k ^ 2 ∧
      ((A = β ^ 2 ∧ B = 2 * α ^ 2) ∨ (A = 2 * α ^ 2 ∧ B = β ^ 2)) ∧
      (α * β = k ∨ α * β = -k) := by
  have hk_ne : k ≠ 0 := Int.ne_of_gt hk_pos
  obtain ⟨A, B, hA, hB, hAB_prod, hAB_cop⟩ :=
    fermat42Double_m2k_half_factors_s s m k hs_odd hk_pos hm_odd hmk_cop hs_sq
  obtain ⟨hA_pos, hB_pos⟩ :=
    fermat42Double_half_factors_s_pos s m k A B hs_ne hm_pos hk_pos hu_pos hs_sq hA hB
  -- Parity case on A.
  rcases Int.emod_two_eq_zero_or_one A with hA_ev | hA_od
  · have hB_odd : B % 2 = 1 := by omega
    obtain ⟨α, β, hB_eq, hA_eq, hcases⟩ :=
      fermat42Double_sq_split_two_odd_even B A k hB_pos.le hA_pos.le hB_odd
        hAB_cop.symm (by linarith) hk_ne
    refine ⟨A, B, α, β, hA, hB, hA_pos, hB_pos, hAB_cop, hAB_prod,
            Or.inr ⟨hA_eq, hB_eq⟩, ?_⟩
    rcases hcases with h | h
    · left; linarith
    · right; linarith
  · obtain ⟨α, β, hA_eq, hB_eq, hcases⟩ :=
      fermat42Double_sq_split_two_odd_even A B k hA_pos.le hB_pos.le hA_od
        hAB_cop hAB_prod hk_ne
    exact ⟨A, B, α, β, hA, hB, hA_pos, hB_pos, hAB_cop, hAB_prod,
           Or.inl ⟨hA_eq, hB_eq⟩, hcases⟩

/-- **T-side quadruple extraction** — mirror for the t-factorization. -/
private theorem fermat42Double_t_side_split
    (t m k : ℤ) (ht_ne : t ≠ 0) (ht_odd : t % 2 = 1)
    (hm_pos : 0 < m) (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_cop : IsCoprime m k)
    (ht_sq : t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2) :
    ∃ C D γ δ : ℤ, m + 2 * k - t = 2 * C ∧ m + 2 * k + t = 2 * D ∧
      0 < C ∧ 0 < D ∧ IsCoprime C D ∧ C * D = 2 * k ^ 2 ∧
      ((C = δ ^ 2 ∧ D = 2 * γ ^ 2) ∨ (C = 2 * γ ^ 2 ∧ D = δ ^ 2)) ∧
      (γ * δ = k ∨ γ * δ = -k) := by
  have hk_ne : k ≠ 0 := Int.ne_of_gt hk_pos
  obtain ⟨C, D, hC, hD, hCD_prod, hCD_cop⟩ :=
    fermat42Double_m2k_half_factors_t t m k ht_odd hk_pos hm_odd hmk_cop ht_sq
  obtain ⟨hC_pos, hD_pos⟩ :=
    fermat42Double_half_factors_t_pos t m k C D ht_ne hm_pos hk_pos ht_sq hC hD
  rcases Int.emod_two_eq_zero_or_one C with hC_ev | hC_od
  · have hD_odd : D % 2 = 1 := by omega
    obtain ⟨γ, δ, hD_eq, hC_eq, hcases⟩ :=
      fermat42Double_sq_split_two_odd_even D C k hD_pos.le hC_pos.le hD_odd
        hCD_cop.symm (by linarith) hk_ne
    refine ⟨C, D, γ, δ, hC, hD, hC_pos, hD_pos, hCD_cop, hCD_prod,
            Or.inr ⟨hC_eq, hD_eq⟩, ?_⟩
    rcases hcases with h | h
    · left; linarith
    · right; linarith
  · obtain ⟨γ, δ, hC_eq, hD_eq, hcases⟩ :=
      fermat42Double_sq_split_two_odd_even C D k hC_pos.le hD_pos.le hC_od
        hCD_cop hCD_prod hk_ne
    exact ⟨C, D, γ, δ, hC, hD, hC_pos, hD_pos, hCD_cop, hCD_prod,
           Or.inl ⟨hC_eq, hD_eq⟩, hcases⟩

/-- **UFD 4-way split** — `αβ = γδ` in ℤ with positive values yields
`α = e·α', γ = e·γ', β = γ'·f, δ = α'·f` where `e = gcd(α, γ)`.

Standard integer UFD factorization via `Int.exists_gcd_one`. -/
private theorem fermat42Double_four_way_split
    (α β γ δ : ℤ) (hα_pos : 0 < α) (hβ_pos : 0 < β) (hγ_pos : 0 < γ) (hδ_pos : 0 < δ)
    (heq : α * β = γ * δ) :
    ∃ e α' γ' f : ℤ, 0 < e ∧ 0 < α' ∧ 0 < γ' ∧ 0 < f ∧
      IsCoprime α' γ' ∧
      α = e * α' ∧ γ = e * γ' ∧ β = γ' * f ∧ δ = α' * f := by
  have hgcd_pos : 0 < Int.gcd α γ :=
    Int.gcd_pos_of_ne_zero_left γ (Int.ne_of_gt hα_pos)
  obtain ⟨α', γ', h_cop_gcd, hα_eq, hγ_eq⟩ := Int.exists_gcd_one hgcd_pos
  set e : ℤ := (Int.gcd α γ : ℤ) with he_def
  have he_pos : 0 < e := by rw [he_def]; exact_mod_cast hgcd_pos
  have hα_rw : α = e * α' := by rw [hα_eq]; ring
  have hγ_rw : γ = e * γ' := by rw [hγ_eq]; ring
  have hα'_pos : 0 < α' := by
    rcases lt_trichotomy α' 0 with h | h | h
    · exfalso; have : α < 0 := by rw [hα_rw]; exact mul_neg_of_pos_of_neg he_pos h
      linarith
    · exfalso; rw [h, mul_zero] at hα_rw; linarith
    · exact h
  have hγ'_pos : 0 < γ' := by
    rcases lt_trichotomy γ' 0 with h | h | h
    · exfalso; have : γ < 0 := by rw [hγ_rw]; exact mul_neg_of_pos_of_neg he_pos h
      linarith
    · exfalso; rw [h, mul_zero] at hγ_rw; linarith
    · exact h
  have h_cop_cop : IsCoprime α' γ' := Int.isCoprime_iff_gcd_eq_one.mpr h_cop_gcd
  have h_α'β : α' * β = γ' * δ := by
    have hne : e ≠ 0 := Int.ne_of_gt he_pos
    have h1 : e * (α' * β) = e * (γ' * δ) := by
      calc e * (α' * β) = (e * α') * β := by ring
        _ = α * β := by rw [← hα_rw]
        _ = γ * δ := heq
        _ = (e * γ') * δ := by rw [← hγ_rw]
        _ = e * (γ' * δ) := by ring
    exact mul_left_cancel₀ hne h1
  have hγ'_dvd_β : γ' ∣ β := by
    have h1 : γ' ∣ α' * β := ⟨δ, by linarith [h_α'β]⟩
    exact h_cop_cop.symm.dvd_of_dvd_mul_left h1
  obtain ⟨f, hf⟩ := hγ'_dvd_β
  have hf_pos : 0 < f := by
    rcases lt_trichotomy f 0 with h | h | h
    · exfalso; have : β < 0 := by rw [hf]; exact mul_neg_of_pos_of_neg hγ'_pos h
      linarith
    · exfalso; rw [h, mul_zero] at hf; linarith
    · exact h
  have hδ_eq : δ = α' * f := by
    have hγ'_ne : γ' ≠ 0 := Int.ne_of_gt hγ'_pos
    have h2 : γ' * (α' * f) = γ' * δ := by
      calc γ' * (α' * f) = α' * (γ' * f) := by ring
        _ = α' * β := by rw [← hf]
        _ = γ' * δ := h_α'β
    exact (mul_left_cancel₀ hγ'_ne h2).symm
  exact ⟨e, α', γ', f, he_pos, hα'_pos, hγ'_pos, hf_pos, h_cop_cop,
         hα_rw, hγ_rw, hf, hδ_eq⟩

/-- **Quadruple extraction** — combines the s-side + t-side square splits
with the four-way UFD split to produce positive `(a, b, c, d)` with
`k = a·b·c·d` and the key identities. -/
private theorem fermat42Double_quadruple_extraction
    (s t m k : ℤ) (hs_ne : s ≠ 0) (ht_ne : t ≠ 0)
    (hs_odd : s % 2 = 1) (ht_odd : t % 2 = 1)
    (hm_pos : 0 < m) (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_cop : IsCoprime m k)
    (hu_pos : 0 < m ^ 2 - 4 * k ^ 2)
    (hs_sq : s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2)
    (ht_sq : t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2) :
    ∃ a b c d : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ IsCoprime b c ∧
      k = a * b * c * d ∧
      m - 2 * k = 2 * a ^ 2 * b ^ 2 + c ^ 2 * d ^ 2 ∧
      m + 2 * k = 2 * a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 := by
  obtain ⟨A, B, α, β, hA_def, hB_def, hA_pos, hB_pos, _, hAB_prod, hAB_case, hαβ⟩ :=
    fermat42Double_s_side_split s m k hs_ne hs_odd hm_pos hk_pos hm_odd hmk_cop hu_pos hs_sq
  obtain ⟨C, D, γ, δ, hC_def, hD_def, hC_pos, hD_pos, _, hCD_prod, hCD_case, hγδ⟩ :=
    fermat42Double_t_side_split t m k ht_ne ht_odd hm_pos hk_pos hm_odd hmk_cop ht_sq
  -- Normalize to positive via |·|.
  have hk_ne : k ≠ 0 := Int.ne_of_gt hk_pos
  have hα'β'_eq : |α| * |β| = k := by
    rw [← abs_mul]
    rcases hαβ with heq | heq
    · rw [heq, abs_of_pos hk_pos]
    · rw [heq, abs_neg, abs_of_pos hk_pos]
  have hγ'δ'_eq : |γ| * |δ| = k := by
    rw [← abs_mul]
    rcases hγδ with heq | heq
    · rw [heq, abs_of_pos hk_pos]
    · rw [heq, abs_neg, abs_of_pos hk_pos]
  have hα'_pos : 0 < |α| := by
    by_contra h; push_neg at h
    have : |α| = 0 := le_antisymm h (abs_nonneg α)
    rw [this, zero_mul] at hα'β'_eq
    exact hk_ne hα'β'_eq.symm
  have hβ'_pos : 0 < |β| := by
    by_contra h; push_neg at h
    have : |β| = 0 := le_antisymm h (abs_nonneg β)
    rw [this, mul_zero] at hα'β'_eq
    exact hk_ne hα'β'_eq.symm
  have hγ'_pos : 0 < |γ| := by
    by_contra h; push_neg at h
    have : |γ| = 0 := le_antisymm h (abs_nonneg γ)
    rw [this, zero_mul] at hγ'δ'_eq
    exact hk_ne hγ'δ'_eq.symm
  have hδ'_pos : 0 < |δ| := by
    by_contra h; push_neg at h
    have : |δ| = 0 := le_antisymm h (abs_nonneg δ)
    rw [this, mul_zero] at hγ'δ'_eq
    exact hk_ne hγ'δ'_eq.symm
  -- Apply four-way split.
  have heq_prod : |α| * |β| = |γ| * |δ| := by rw [hα'β'_eq, hγ'δ'_eq]
  obtain ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos, hbc_cop,
          hα_rw, hγ_rw, hβ_rw, hδ_rw⟩ :=
    fermat42Double_four_way_split |α| |β| |γ| |δ| hα'_pos hβ'_pos hγ'_pos hδ'_pos heq_prod
  refine ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos, hbc_cop, ?_, ?_, ?_⟩
  · -- k = a*b*c*d.
    rw [← hα'β'_eq, hα_rw, hβ_rw]; ring
  · -- m - 2k = 2a²b² + c²d²: m - 2k = A + B = 2α² + β² (either case) = 2|α|² + |β|² = 2(ab)² + (cd)².
    have h_AB_sum : A + B = 2 * α ^ 2 + β ^ 2 := by
      rcases hAB_case with ⟨hA_eq, hB_eq⟩ | ⟨hA_eq, hB_eq⟩
      · rw [hA_eq, hB_eq]; ring
      · rw [hA_eq, hB_eq]
    have h_m2k : m - 2 * k = A + B := by linarith [hA_def, hB_def]
    rw [h_m2k, h_AB_sum, show (α : ℤ) ^ 2 = |α| ^ 2 from (sq_abs α).symm,
        show (β : ℤ) ^ 2 = |β| ^ 2 from (sq_abs β).symm, hα_rw, hβ_rw]
    try ring
  · -- m + 2k = 2a²c² + b²d².
    have h_CD_sum : C + D = 2 * γ ^ 2 + δ ^ 2 := by
      rcases hCD_case with ⟨hC_eq, hD_eq⟩ | ⟨hC_eq, hD_eq⟩
      · rw [hC_eq, hD_eq]; ring
      · rw [hC_eq, hD_eq]
    have h_m2k : m + 2 * k = C + D := by linarith [hC_def, hD_def]
    rw [h_m2k, h_CD_sum, show (γ : ℤ) ^ 2 = |γ| ^ 2 from (sq_abs γ).symm,
        show (δ : ℤ) ^ 2 = |δ| ^ 2 from (sq_abs δ).symm, hγ_rw, hδ_rw]
    try ring

/-- **Key relation** — from the quadruple identities, derive
`4·a·b·c·d = (c² - b²)·(2a² - d²)`. -/
private theorem fermat42Double_key_relation
    (a b c d k : ℤ) (hk_abcd : k = a * b * c * d)
    (m : ℤ) (hm_minus : m - 2 * k = 2 * a ^ 2 * b ^ 2 + c ^ 2 * d ^ 2)
    (hm_plus : m + 2 * k = 2 * a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2) :
    4 * (a * b * c * d) = (c ^ 2 - b ^ 2) * (2 * a ^ 2 - d ^ 2) := by
  have h_diff : 4 * k = (2 * a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2) -
                       (2 * a ^ 2 * b ^ 2 + c ^ 2 * d ^ 2) := by
    linarith [hm_plus, hm_minus]
  rw [hk_abcd] at h_diff
  linear_combination h_diff

/-- **Smaller Fermat42Double extraction** — from the key relation,
derive `∃ e, 2e² = b⁴ + c⁴`.

Proof chain:
* Completing the square on the key relation: `(2(c² - b²)·d + 4abc)² = 8a²(b⁴ + c⁴)`.
* Set `M := 2(c² - b²)·d + 4abc`.  Then `M² = 8a²(b⁴ + c⁴) = (2a)²·2(b⁴ + c⁴)`.
* `(2a)² ∣ M²` via `Int.pow_dvd_pow_iff` gives `2a ∣ M`.  Write `M = 2a·e'`.
* `e'² = 2(b⁴ + c⁴)`.  `2 ∣ e'²` so `2 ∣ e'`.  Write `e' = 2e''`.
* `4e''² = 2(b⁴ + c⁴)`, i.e., `2e''² = b⁴ + c⁴`. -/
private theorem fermat42Double_smaller_equation
    (a b c d : ℤ) (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c) (hd_pos : 0 < d)
    (h_key : 4 * (a * b * c * d) = (c ^ 2 - b ^ 2) * (2 * a ^ 2 - d ^ 2)) :
    ∃ e : ℤ, 2 * e ^ 2 = b ^ 4 + c ^ 4 := by
  -- Step 1: (2(c² - b²)d + 4abc)² = 8a²(b⁴ + c⁴).
  have h_sq_eq : (2 * (c ^ 2 - b ^ 2) * d + 4 * a * b * c) ^ 2 = 8 * a ^ 2 * (b ^ 4 + c ^ 4) := by
    linear_combination 4 * (c ^ 2 - b ^ 2) * h_key
  set M : ℤ := 2 * (c ^ 2 - b ^ 2) * d + 4 * a * b * c with hM_def
  -- Step 2: (2a)² ∣ M² via M² = (2a)² · 2(b⁴ + c⁴).
  have h_2a_sq_dvd : (2 * a) ^ 2 ∣ M ^ 2 := by
    refine ⟨2 * (b ^ 4 + c ^ 4), ?_⟩
    linear_combination h_sq_eq
  -- Step 3: 2a ∣ M.
  have h_2a_dvd : (2 * a) ∣ M :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp h_2a_sq_dvd
  obtain ⟨e', hM_eq⟩ := h_2a_dvd
  -- Step 4: e'² = 2(b⁴ + c⁴).
  have h_e'_sq : e' ^ 2 = 2 * (b ^ 4 + c ^ 4) := by
    have h1 : M ^ 2 = (2 * a) ^ 2 * e' ^ 2 := by rw [hM_eq]; ring
    have h2a_sq_pos : 0 < (2 * a) ^ 2 := by positivity
    have h2a_sq_ne : (2 * a) ^ 2 ≠ 0 := Int.ne_of_gt h2a_sq_pos
    have h3 : (2 * a) ^ 2 * e' ^ 2 = (2 * a) ^ 2 * (2 * (b ^ 4 + c ^ 4)) := by
      rw [← h1, h_sq_eq]; ring
    exact mul_left_cancel₀ h2a_sq_ne h3
  -- Step 5: 2 ∣ e' via e'² = 2·(b⁴+c⁴) (so 2 ∣ e'², hence 2 ∣ e').
  have h_two_prime : Prime (2 : ℤ) := Int.prime_two
  have h_two_dvd_e' : (2 : ℤ) ∣ e' := by
    have h_two_dvd_sq : (2 : ℤ) ∣ e' ^ 2 := ⟨b ^ 4 + c ^ 4, h_e'_sq⟩
    exact h_two_prime.dvd_of_dvd_pow h_two_dvd_sq
  obtain ⟨e'', he'_eq⟩ := h_two_dvd_e'
  refine ⟨e'', ?_⟩
  -- Step 6: 2e''² = b⁴ + c⁴ from (2e'')² = e'² = 2(b⁴+c⁴).
  have h1 : (2 * e'') ^ 2 = 2 * (b ^ 4 + c ^ 4) := by rw [← he'_eq]; exact h_e'_sq
  have h2 : 4 * e'' ^ 2 = 2 * (b ^ 4 + c ^ 4) := by linear_combination h1
  linarith

/-- Core of the descent step — used by `fermat42Double_descent_step_holds`
(declared below `Fermat42DoubleDescentStep` def). -/
private theorem fermat42Double_descent_step_body
    (s t a m k : ℤ) (hs_ne : s ≠ 0) (ht_ne : t ≠ 0) (ha_pos : 0 < a)
    (_hst_coprime : IsCoprime s t) (_hst_lt : s ^ 2 < t ^ 2)
    (hs_odd : s % 2 = 1) (ht_odd : t % 2 = 1)
    (hm_pos : 0 < m) (hk_pos : 0 < k) (hm_odd : m % 2 = 1)
    (hmk_cop : IsCoprime m k)
    (hs_sq : s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2)
    (ht_sq : t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2)
    (ha_eq : a = m ^ 2 + 4 * k ^ 2)
    (_h_eq : 2 * a ^ 2 = s ^ 4 + t ^ 4) :
    ∃ b c e : ℤ, b ≠ 0 ∧ c ≠ 0 ∧ e ≠ 0 ∧ IsCoprime b c ∧ b ^ 2 ≠ c ^ 2 ∧
      2 * e ^ 2 = b ^ 4 + c ^ 4 ∧ e.natAbs < a.natAbs := by
  have hs2_pos : 0 < s ^ 2 :=
    (sq_nonneg s).lt_of_ne (fun h => hs_ne (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h.symm))
  have ht2_pos : 0 < t ^ 2 :=
    (sq_nonneg t).lt_of_ne (fun h => ht_ne (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h.symm))
  have hu_pos : 0 < m ^ 2 - 4 * k ^ 2 := by
    have hsum : s ^ 2 + t ^ 2 = 2 * (m ^ 2 - 4 * k ^ 2) := by linarith [hs_sq, ht_sq]
    linarith
  obtain ⟨a', b, c, d, ha'_pos, hb_pos, hc_pos, hd_pos, hbc_cop, hk_abcd, h_m_minus, h_m_plus⟩ :=
    fermat42Double_quadruple_extraction s t m k hs_ne ht_ne hs_odd ht_odd hm_pos hk_pos hm_odd
      hmk_cop hu_pos hs_sq ht_sq
  have h_key :=
    fermat42Double_key_relation a' b c d k hk_abcd m h_m_minus h_m_plus
  obtain ⟨e, h_new_eq⟩ :=
    fermat42Double_smaller_equation a' b c d ha'_pos hb_pos hc_pos hd_pos h_key
  have hb_ne_c : b ≠ c := by
    intro hbc
    have h1 : m - 2 * k = 2 * a' ^ 2 * b ^ 2 + c ^ 2 * d ^ 2 := h_m_minus
    have h2 : m + 2 * k = 2 * a' ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 := h_m_plus
    rw [hbc] at h1 h2
    linarith
  have hb_sq_ne : b ^ 2 ≠ c ^ 2 := by
    intro h
    apply hb_ne_c
    have : b = c ∨ b = -c := by
      have h1 : (b - c) * (b + c) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h1 with h2 | h2
      · left; linarith
      · right; linarith
    rcases this with h | h
    · exact h
    · exfalso; linarith
  have hb_ne : b ≠ 0 := Int.ne_of_gt hb_pos
  have hc_ne : c ≠ 0 := Int.ne_of_gt hc_pos
  have he_ne : e ≠ 0 := by
    intro he
    rw [he] at h_new_eq; simp at h_new_eq
    have hb4_pos : 0 < b ^ 4 := by positivity
    have hc4_pos : 0 < c ^ 4 := by positivity
    linarith
  -- Size bound: |e| < a.
  have ha'_ge_1 : 1 ≤ a' := ha'_pos
  have hd_ge_1 : 1 ≤ d := hd_pos
  have hb_ge_1 : 1 ≤ b := hb_pos
  have hc_ge_1 : 1 ≤ c := hc_pos
  have hk_ge_1 : 1 ≤ k := hk_pos
  have hb_le_k : b ≤ k := by
    have h1 : (1 : ℤ) ≤ a' * c * d := by
      have h : 0 < a' * c * d := mul_pos (mul_pos ha'_pos hc_pos) hd_pos
      linarith
    have h2 : b ≤ b * (a' * c * d) := le_mul_of_one_le_right hb_pos.le h1
    have h3 : b * (a' * c * d) = a' * b * c * d := by ring
    rw [h3] at h2
    linarith [h2, hk_abcd]
  have hc_le_k : c ≤ k := by
    have h1 : (1 : ℤ) ≤ a' * b * d := by
      have h : 0 < a' * b * d := mul_pos (mul_pos ha'_pos hb_pos) hd_pos
      linarith
    have h2 : c ≤ c * (a' * b * d) := le_mul_of_one_le_right hc_pos.le h1
    have h3 : c * (a' * b * d) = a' * b * c * d := by ring
    rw [h3] at h2
    linarith [h2, hk_abcd]
  have h_m_gt_2k : 2 * k < m := fermat42Double_m_gt_2k m k hm_pos hk_pos hu_pos
  have h_a_ge : 8 * k ^ 2 + 4 * k + 1 ≤ a := by
    have h_m_ge : 2 * k + 1 ≤ m := h_m_gt_2k
    have h_m_sq_ge : (2 * k + 1) ^ 2 ≤ m ^ 2 := by nlinarith
    linarith [ha_eq, h_m_sq_ge]
  have h_e_sq_le : e ^ 2 ≤ k ^ 4 := by
    have hb4_le : b ^ 4 ≤ k ^ 4 := pow_le_pow_left₀ hb_pos.le hb_le_k 4
    have hc4_le : c ^ 4 ≤ k ^ 4 := pow_le_pow_left₀ hc_pos.le hc_le_k 4
    linarith [h_new_eq]
  have h_e_lt_a : e.natAbs < a.natAbs := by
    have h_e_abs_sq : (e.natAbs : ℤ) ^ 2 ≤ k ^ 4 := by
      rw [show ((e.natAbs : ℤ)) = |e| from (Int.abs_eq_natAbs e).symm, sq_abs]
      exact h_e_sq_le
    have h_e_abs_le_ksq : (e.natAbs : ℤ) ≤ k ^ 2 := by
      have h_e_nn : 0 ≤ (e.natAbs : ℤ) := Int.natCast_nonneg _
      have h_k_sq_nn : 0 ≤ k ^ 2 := sq_nonneg _
      have h_ksq4 : (k ^ 2) ^ 2 = k ^ 4 := by ring
      nlinarith [h_e_abs_sq, sq_nonneg ((e.natAbs : ℤ) - k ^ 2), h_ksq4]
    have h_a_cast : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha_pos.le
    have h_e_lt_a_int : (e.natAbs : ℤ) < (a.natAbs : ℤ) := by
      rw [h_a_cast]; linarith [h_e_abs_le_ksq, h_a_ge, hk_pos]
    exact_mod_cast h_e_lt_a_int
  exact ⟨b, c, e, hb_ne, hc_ne, he_ne, hbc_cop, hb_sq_ne, h_new_eq, h_e_lt_a⟩

/-- **`Fermat42DoubleDescentStep` sub-gap** — from a `Fermat42Double`
counterexample with Pythagorean (m, k) structure, produces a strictly
smaller `Fermat42Double` counterexample `(b, c, e)` with
`e.natAbs < a.natAbs`.

This is the classical Fermat descent step: UFD-split the two factorizations
`(m - 2k)² - s² = 8k²` and `(m + 2k)² - t² = 8k²`, derive the relation
`(c² - b²)(d² - 2a²) = 4abcd` on the quadruple `(a, b, c, d)`, solve as
quadratic in `d` to force the discriminant `2(b⁴ + c⁴)` to be a perfect
square, yielding `2e² = b⁴ + c⁴` with `e = ⌊√(2(b⁴ + c⁴))⌋ / 2`.

Composed via strong induction on `a.natAbs`, this closes
`Fermat42Double_impossible`.

Structural prerequisites (parity, coprime factors, product = 8k²) are
discharged in `fermat42Double_descent_factorization_facts`. -/
def Fermat42DoubleDescentStep : Prop :=
  ∀ s t a m k : ℤ,
    s ≠ 0 → t ≠ 0 → 0 < a →
    IsCoprime s t →
    s ^ 2 < t ^ 2 →
    s % 2 = 1 → t % 2 = 1 →
    0 < m → 0 < k → m % 2 = 1 →
    IsCoprime m k →
    s ^ 2 = (m - 2 * k) ^ 2 - 8 * k ^ 2 →
    t ^ 2 = (m + 2 * k) ^ 2 - 8 * k ^ 2 →
    a = m ^ 2 + 4 * k ^ 2 →
    2 * a ^ 2 = s ^ 4 + t ^ 4 →
    ∃ b c e : ℤ, b ≠ 0 ∧ c ≠ 0 ∧ e ≠ 0 ∧ IsCoprime b c ∧ b ^ 2 ≠ c ^ 2 ∧
      2 * e ^ 2 = b ^ 4 + c ^ 4 ∧ e.natAbs < a.natAbs

/-- **`Fermat42Double_impossible` via descent step** — strong induction
on `a.natAbs` composed with the Pythagorean setup + descent step. -/
theorem fermat42Double_impossible_of_descent_step
    (hDescent : Fermat42DoubleDescentStep) :
    Fermat42Double_impossible := by
  have H : ∀ n : ℕ, ∀ s t a : ℤ, a.natAbs = n →
      s ≠ 0 → t ≠ 0 → a ≠ 0 → IsCoprime s t → s ^ 2 ≠ t ^ 2 →
      2 * a ^ 2 ≠ s ^ 4 + t ^ 4 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s t a hn hs_ne ht_ne ha_ne hst_coprime hst_sq_ne h_eq
      obtain ⟨hs_odd, ht_odd⟩ :=
        fermat42Double_parity hs_ne ht_ne hst_coprime h_eq
      -- WLOG a > 0.
      have h_abs_eq : 2 * |a| ^ 2 = s ^ 4 + t ^ 4 := by rw [sq_abs]; exact h_eq
      have h_abs_pos : 0 < |a| := abs_pos.mpr ha_ne
      have h_abs_natAbs : |a|.natAbs = n := by rw [Int.natAbs_abs]; exact hn
      -- WLOG s^2 < t^2.
      rcases lt_trichotomy (s ^ 2) (t ^ 2) with h_lt | h_eq2 | h_gt
      · obtain ⟨m, k, hm_pos, hk_pos, hm_odd, hmk_cop, hs_sq, ht_sq, ha_mk⟩ :=
          fermat42Double_pythagorean_setup s t |a| hs_ne ht_ne h_abs_pos
            hst_coprime h_lt hs_odd ht_odd h_abs_eq
        obtain ⟨b, c, e, hb_ne, hc_ne, he_ne, hbc_cop, hbc_sq_ne, h_new, h_lt_abs⟩ :=
          hDescent s t |a| m k hs_ne ht_ne h_abs_pos hst_coprime h_lt hs_odd ht_odd
            hm_pos hk_pos hm_odd hmk_cop hs_sq ht_sq ha_mk h_abs_eq
        have h_lt_n : e.natAbs < n := h_abs_natAbs ▸ h_lt_abs
        have : 2 * e ^ 2 ≠ b ^ 4 + c ^ 4 :=
          ih e.natAbs h_lt_n b c e rfl hb_ne hc_ne he_ne hbc_cop hbc_sq_ne
        exact this h_new
      · exact hst_sq_ne h_eq2
      · have hts_coprime : IsCoprime t s := hst_coprime.symm
        have hts_sq_ne : t ^ 2 ≠ s ^ 2 := fun h => hst_sq_ne h.symm
        have h_abs_eq_sw : 2 * |a| ^ 2 = t ^ 4 + s ^ 4 := by linarith
        obtain ⟨m, k, hm_pos, hk_pos, hm_odd, hmk_cop, hs_sq, ht_sq, ha_mk⟩ :=
          fermat42Double_pythagorean_setup t s |a| ht_ne hs_ne h_abs_pos
            hts_coprime h_gt ht_odd hs_odd h_abs_eq_sw
        obtain ⟨b, c, e, hb_ne, hc_ne, he_ne, hbc_cop, hbc_sq_ne, h_new, h_lt_abs⟩ :=
          hDescent t s |a| m k ht_ne hs_ne h_abs_pos hts_coprime h_gt ht_odd hs_odd
            hm_pos hk_pos hm_odd hmk_cop hs_sq ht_sq ha_mk h_abs_eq_sw
        have h_lt_n : e.natAbs < n := h_abs_natAbs ▸ h_lt_abs
        have : 2 * e ^ 2 ≠ b ^ 4 + c ^ 4 :=
          ih e.natAbs h_lt_n b c e rfl hb_ne hc_ne he_ne hbc_cop hbc_sq_ne
        exact this h_new
  intro s t a hs_ne ht_ne ha_ne hst_coprime hst_sq_ne h_eq
  exact H a.natAbs s t a rfl hs_ne ht_ne ha_ne hst_coprime hst_sq_ne h_eq

/-- **Discharge of `Fermat42DoubleDescentStep`** — the top-level theorem
composing the descent-step body with its type. -/
theorem fermat42Double_descent_step_holds : Fermat42DoubleDescentStep := by
  intro s t a m k hs_ne ht_ne ha_pos hst_coprime hst_lt hs_odd ht_odd
    hm_pos hk_pos hm_odd hmk_cop hs_sq ht_sq ha_eq h_eq
  exact fermat42Double_descent_step_body s t a m k hs_ne ht_ne ha_pos
    hst_coprime hst_lt hs_odd ht_odd hm_pos hk_pos hm_odd hmk_cop hs_sq ht_sq ha_eq h_eq

/-- **★★★ `Fermat42Double_impossible` IS UNCONDITIONAL ★★★**

Composition of the strong-induction wrapper `fermat42Double_impossible_of_descent_step`
with the full descent-step discharge `fermat42Double_descent_step_holds`. -/
theorem fermat42Double_impossible_unconditional : Fermat42Double_impossible :=
  fermat42Double_impossible_of_descent_step fermat42Double_descent_step_holds

end Fermat42Sub

/-! ## Section: Fermat42SubAssembly_2026_11_14 -/

namespace Fermat42Sub

/-- **Case B mirror** — same as `fermat42Sub_caseB_descends` but with
`(m even, n odd)` instead of `(m odd, n even)`.  Arises when the
Pythagorean classification of a primitive triple with odd leg
`c ≡ 3 mod 4` picks the other parity assignment.

Proof structure mirrors `fermat42Sub_caseB_descends` by calling
`hSplit1` with the (m, n) roles swapped. -/
theorem fermat42Sub_caseB_descends_mirror
    (hSplit1 : Fermat42SubCaseB_squareSplit)
    (hSplit2 : Fermat42SubCaseB_fourthPowerSplit)
    (a b c m n : ℤ)
    (h_min : Minimal a b c)
    (ha_pos : 0 < a) (hc_pos : 0 < c)
    (h_m_pos : 0 < m) (h_n_pos : 0 < n)
    (hmn_coprime : IsCoprime m n)
    (hm_even : m % 2 = 0) (hn_odd : n % 2 = 1)
    (hc_eq : c = m ^ 2 - n ^ 2)
    (hb_sq : b ^ 2 = 2 * m * n)
    (ha_sq : a ^ 2 = m ^ 2 + n ^ 2) : False := by
  -- Mirror square split: call hSplit1 with (n, m, b) so that n plays "m odd" and m plays "n even".
  have hb_sq' : b ^ 2 = 2 * n * m := by linarith [hb_sq]
  obtain ⟨i, j, hn_eq, hm_eq, hb_eq⟩ :=
    hSplit1 n m b h_n_pos.le h_m_pos hmn_coprime.symm hn_odd hm_even hb_sq'
  -- hn_eq : n = i², hm_eq : m = 2 j², hb_eq : b = 2 i j.
  -- a² = m² + n² = (2j²)² + (i²)² = 4j⁴ + i⁴, so a² - i⁴ = 4j⁴.
  have ha_sq' : a ^ 2 - i ^ 4 = 4 * j ^ 4 := by
    rw [hm_eq, hn_eq] at ha_sq
    linear_combination ha_sq
  have hj_ne : j ≠ 0 := by
    intro hj
    rw [hj] at hm_eq
    simp at hm_eq
    linarith
  have hi_odd : i % 2 = 1 := by
    rw [hn_eq] at hn_odd
    rw [show (i ^ 2 : ℤ) = i * i from sq i, Int.mul_emod] at hn_odd
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · rw [h] at hn_odd; norm_num at hn_odd
    · exact h
  have hab_coprime : IsCoprime a b :=
    Fermat42Sub.coprime_of_minimal h_min
  have ha_ij_coprime : IsCoprime a (i * j) := by
    have hb_fact : b = 2 * (i * j) := by rw [hb_eq]; ring
    have h1 : IsCoprime a (2 * (i * j)) := hb_fact ▸ hab_coprime
    exact h1.of_mul_right_right
  obtain ⟨p, q, hpq, hp_eq, hq_eq⟩ := hSplit2 a i j ha_pos hi_odd hj_ne
    ha_ij_coprime ha_sq'
  have h_new_eq : q ^ 4 - p ^ 4 = (2 * j) ^ 2 := by
    have : q ^ 4 - p ^ 4 = (a + 2 * j ^ 2) - (a - 2 * j ^ 2) := by
      rw [hp_eq, hq_eq]
    rw [this]; ring
  have hi_ne : i ≠ 0 := by
    intro h; rw [h] at hi_odd; norm_num at hi_odd
  have hp_ne : p ≠ 0 := left_ne_zero_of_mul (by rw [hpq]; exact hi_ne)
  have hq_ne : q ≠ 0 := right_ne_zero_of_mul (by rw [hpq]; exact hi_ne)
  have h2j_ne : (2 * j : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hj_ne
  have h_new : Fermat42Sub q p (2 * j) := ⟨hq_ne, hp_ne, h2j_ne, h_new_eq⟩
  have h_le : Int.natAbs c ≤ Int.natAbs (2 * j) := h_min.2 q p (2 * j) h_new
  -- Mirror bound: c = m² - n² = 4j⁴ - i⁴ = (2j² - i²)(2j² + i²).
  have hj_abs_pos : 0 < Int.natAbs j := Int.natAbs_pos.mpr hj_ne
  have hc_eq' : c = 4 * j ^ 4 - i ^ 4 := by
    rw [hc_eq, hm_eq, hn_eq]; ring
  have h_2j_sq_gt : 2 * j ^ 2 > i ^ 2 := by
    by_contra h_le_ij
    push_neg at h_le_ij
    have h_4j4_le : 4 * j ^ 4 ≤ i ^ 4 := by
      have h1 : (2 * j ^ 2) * (2 * j ^ 2) ≤ i ^ 2 * i ^ 2 := by
        exact mul_le_mul h_le_ij h_le_ij (by positivity) (sq_nonneg _)
      calc 4 * j ^ 4 = (2 * j ^ 2) * (2 * j ^ 2) := by ring
        _ ≤ i ^ 2 * i ^ 2 := h1
        _ = i ^ 4 := by ring
    linarith
  have hc_ge : 2 * j ^ 2 + 1 ≤ c := by
    -- c = (2j² - i²)(2j² + i²), 2j² - i² ≥ 1, 2j² + i² ≥ 2j² + 1.
    have h1 : 2 * j ^ 2 - i ^ 2 ≥ 1 := by linarith [h_2j_sq_gt]
    have h2 : 2 * j ^ 2 + i ^ 2 ≥ 2 * j ^ 2 + 1 := by
      have hi_sq_ge : i ^ 2 ≥ 1 := by
        have hi_sq_pos : 0 < i ^ 2 := by positivity
        omega
      linarith
    have h3 : c = (2 * j ^ 2 - i ^ 2) * (2 * j ^ 2 + i ^ 2) := by
      rw [hc_eq']; ring
    have h4 : (2 * j ^ 2 - i ^ 2) * (2 * j ^ 2 + i ^ 2) ≥ 1 * (2 * j ^ 2 + 1) := by
      have h5 : 0 ≤ 2 * j ^ 2 + i ^ 2 := by positivity
      nlinarith [h1, h2]
    linarith
  -- |2j|.natAbs = 2 · j.natAbs; c.natAbs = c.
  have h_abs_lt : Int.natAbs (2 * j) < Int.natAbs c := by
    have h2j_abs : Int.natAbs (2 * j) = 2 * Int.natAbs j := by
      rw [Int.natAbs_mul]; rfl
    have hc_cast : (Int.natAbs c : ℤ) = c := Int.natAbs_of_nonneg hc_pos.le
    have h_jsq_cast : (j : ℤ) ^ 2 = (Int.natAbs j : ℤ) ^ 2 := by
      rw [show ((Int.natAbs j : ℤ)) = |j| from (Int.abs_eq_natAbs j).symm, sq_abs]
    have hc_abs_ge : (2 * (Int.natAbs j : ℤ) ^ 2 + 1 : ℤ) ≤ (Int.natAbs c : ℤ) := by
      rw [hc_cast, ← h_jsq_cast]; exact hc_ge
    have hc_abs_nat : 2 * (Int.natAbs j) ^ 2 + 1 ≤ Int.natAbs c := by
      have h1 : ((2 * (Int.natAbs j) ^ 2 + 1 : ℕ) : ℤ)
            = 2 * (Int.natAbs j : ℤ) ^ 2 + 1 := by push_cast; ring
      have h2 : ((Int.natAbs c : ℕ) : ℤ) = (Int.natAbs c : ℤ) := by rfl
      have h3 : ((2 * (Int.natAbs j) ^ 2 + 1 : ℕ) : ℤ) ≤ ((Int.natAbs c : ℕ) : ℤ) := by
        rw [h1, h2]; exact hc_abs_ge
      exact_mod_cast h3
    rw [h2j_abs]
    calc 2 * Int.natAbs j
        < 2 * (Int.natAbs j) ^ 2 + 1 := by nlinarith [hj_abs_pos]
      _ ≤ Int.natAbs c := hc_abs_nat
  exact absurd h_le (not_le_of_gt h_abs_lt)

end Fermat42Sub

open Fermat42Sub

/-- **`not_fermat_42_sub`** — the difference form of Fermat's `n = 4`.

Full composition: `exists_minimal` + normalize-to-positive-via-abs +
primitive Pythagorean classification on `(b², c, a²)` (or `(c, b², a²)`)
based on parity of `b`, followed by `fermat42Sub_caseA_reduces` (Case A,
`b` odd) or `fermat42Sub_caseB_descends` / `_mirror` (Case B, `b` even,
mirror based on parity assignment of the Pyth classification). -/
theorem not_fermat_42_sub : ∀ a b c : ℤ,
    a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 - b ^ 4 ≠ c ^ 2 := by
  intro a b c ha hb hc h_eq
  have h_sub : Fermat42Sub a b c := ⟨ha, hb, hc, h_eq⟩
  obtain ⟨a₀, b₀, c₀, h_min⟩ := Fermat42Sub.exists_minimal h_sub
  have ha₀_ne : a₀ ≠ 0 := h_min.1.1
  have hb₀_ne : b₀ ≠ 0 := h_min.1.2.1
  have hc₀_ne : c₀ ≠ 0 := h_min.1.2.2.1
  have h_abs_eq : |a₀| ^ 4 - |b₀| ^ 4 = |c₀| ^ 2 := by
    have h1 : |a₀| ^ 4 = a₀ ^ 4 := by
      have : (|a₀|) ^ 2 = a₀ ^ 2 := sq_abs a₀
      calc |a₀| ^ 4 = (|a₀| ^ 2) ^ 2 := by ring
        _ = (a₀ ^ 2) ^ 2 := by rw [this]
        _ = a₀ ^ 4 := by ring
    have h2 : |b₀| ^ 4 = b₀ ^ 4 := by
      have : (|b₀|) ^ 2 = b₀ ^ 2 := sq_abs b₀
      calc |b₀| ^ 4 = (|b₀| ^ 2) ^ 2 := by ring
        _ = (b₀ ^ 2) ^ 2 := by rw [this]
        _ = b₀ ^ 4 := by ring
    have h3 : |c₀| ^ 2 = c₀ ^ 2 := sq_abs c₀
    linarith [h_min.1.2.2.2]
  have h_abs_sub : Fermat42Sub |a₀| |b₀| |c₀| :=
    ⟨abs_ne_zero.mpr ha₀_ne, abs_ne_zero.mpr hb₀_ne, abs_ne_zero.mpr hc₀_ne, h_abs_eq⟩
  have h_abs_min : Fermat42Sub.Minimal |a₀| |b₀| |c₀| := by
    refine ⟨h_abs_sub, ?_⟩
    intro a1 b1 c1 hf1
    have : (|c₀|).natAbs = c₀.natAbs := Int.natAbs_abs c₀
    rw [this]; exact h_min.2 a1 b1 c1 hf1
  set A : ℤ := |a₀|
  set B : ℤ := |b₀|
  set C : ℤ := |c₀|
  have hA_pos : 0 < A := abs_pos.mpr ha₀_ne
  have hB_pos : 0 < B := abs_pos.mpr hb₀_ne
  have hC_pos : 0 < C := abs_pos.mpr hc₀_ne
  have hAB_cop : IsCoprime A B := Fermat42Sub.coprime_of_minimal h_abs_min
  have hpyth_eq : A ^ 4 - B ^ 4 = C ^ 2 := h_abs_sub.2.2.2
  have hpyth : PythagoreanTriple (B ^ 2) C (A ^ 2) := by
    show B ^ 2 * B ^ 2 + C * C = A ^ 2 * A ^ 2
    nlinarith [hpyth_eq]
  have hpyth' : PythagoreanTriple C (B ^ 2) (A ^ 2) :=
    pythagoreanTriple_comm.mp hpyth
  -- IsCoprime (B²) C via Bezout from IsCoprime (A⁴) (B⁴).
  have hB2_cop_C : IsCoprime (B ^ 2) C := by
    obtain ⟨u, v, huv⟩ : IsCoprime (A ^ 4) (B ^ 4) := hAB_cop.pow
    -- gcd divides B² so divides B⁴. gcd divides C so divides C² = A⁴ - B⁴, hence divides A⁴.
    rw [Int.isCoprime_iff_gcd_eq_one]
    set d := Int.gcd (B ^ 2) C
    have hd_dvd_B2 : (d : ℤ) ∣ B ^ 2 := Int.gcd_dvd_left _ _
    have hd_dvd_C : (d : ℤ) ∣ C := Int.gcd_dvd_right _ _
    have hd_dvd_B4 : (d : ℤ) ∣ B ^ 4 := by
      have h : B ^ 4 = B ^ 2 * B ^ 2 := by ring
      rw [h]; exact Dvd.dvd.mul_left hd_dvd_B2 _
    have hd_dvd_C2 : (d : ℤ) ∣ C ^ 2 := dvd_pow hd_dvd_C (by norm_num)
    have hd_dvd_A4 : (d : ℤ) ∣ A ^ 4 := by
      have h : A ^ 4 = C ^ 2 + B ^ 4 := by linarith [hpyth_eq]
      rw [h]; exact dvd_add hd_dvd_C2 hd_dvd_B4
    have hd_dvd_1 : (d : ℤ) ∣ 1 := by
      have h : (1 : ℤ) = u * A ^ 4 + v * B ^ 4 := huv.symm
      rw [h]
      exact dvd_add (dvd_mul_of_dvd_right hd_dvd_A4 _)
                    (dvd_mul_of_dvd_right hd_dvd_B4 _)
    have : d ∣ 1 := by exact_mod_cast hd_dvd_1
    exact Nat.dvd_one.mp this
  have hC_cop_B2 : IsCoprime C (B ^ 2) := hB2_cop_C.symm
  have hA2_pos : 0 < A ^ 2 := by positivity
  rcases Int.emod_two_eq_zero_or_one B with hB_ev | hB_od
  · -- Case B: B even, C odd.
    have hB2_ev : B ^ 2 % 2 = 0 := by
      rw [show B ^ 2 = B * B from sq B, Int.mul_emod, hB_ev]; decide
    have hA_odd : A % 2 = 1 := by
      by_contra hA_ev'
      push_neg at hA_ev'
      have : A % 2 = 0 := by omega
      have h2_dvd_A : (2 : ℤ) ∣ A := Int.dvd_of_emod_eq_zero this
      have h2_dvd_B : (2 : ℤ) ∣ B := Int.dvd_of_emod_eq_zero hB_ev
      have h2_dvd_gcd : (2 : ℤ) ∣ Int.gcd A B := Int.dvd_coe_gcd h2_dvd_A h2_dvd_B
      rw [Int.isCoprime_iff_gcd_eq_one.mp hAB_cop] at h2_dvd_gcd
      norm_num at h2_dvd_gcd
    have hA2_odd : A ^ 2 % 2 = 1 := by
      rw [show A ^ 2 = A * A from sq A, Int.mul_emod, hA_odd]; decide
    have hA4_odd : A ^ 4 % 2 = 1 := by
      rw [show A ^ 4 = A ^ 2 * A ^ 2 from by ring, Int.mul_emod, hA2_odd]; decide
    have hB4_ev : B ^ 4 % 2 = 0 := by
      rw [show B ^ 4 = B ^ 2 * B ^ 2 from by ring, Int.mul_emod, hB2_ev]; decide
    have hC2_odd : C ^ 2 % 2 = 1 := by
      rw [← hpyth_eq, Int.sub_emod, hA4_odd, hB4_ev]; decide
    have hC_odd : C % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one C with h | h
      · exfalso
        have : C ^ 2 % 2 = 0 := by rw [sq, Int.mul_emod, h]; decide
        rw [this] at hC2_odd; norm_num at hC2_odd
      · exact h
    have hC_cop_nat : Int.gcd C (B ^ 2) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp hC_cop_B2
    obtain ⟨m, n, hc_eq, hb2_eq, ha2_eq, hmn_gcd, hmn_par, hm_nn⟩ :=
      hpyth'.coprime_classification' hC_cop_nat hC_odd hA2_pos
    have hmn_cop : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
    -- m > 0 and n > 0 since 2mn = B² > 0 and m ≥ 0.
    have hm_pos_strict : 0 < m := by
      rcases lt_or_eq_of_le hm_nn with h | h
      · exact h
      · exfalso
        rw [← h] at hb2_eq
        simp at hb2_eq
        have : 0 < B ^ 2 := by positivity
        linarith
    have hn_pos : 0 < n := by
      have hB2_pos : 0 < B ^ 2 := by positivity
      have : 0 < 2 * m * n := by rw [← hb2_eq]; exact hB2_pos
      nlinarith [hm_pos_strict]
    rcases hmn_par with ⟨hm_ev, hn_od⟩ | ⟨hm_od, hn_ev⟩
    · -- (m even, n odd) sub-case: use mirror.
      exact fermat42Sub_caseB_descends_mirror
        fermat42SubCaseB_squareSplit_holds
        fermat42SubCaseB_fourthPowerSplit_holds
        A B C m n h_abs_min hA_pos hC_pos hm_pos_strict hn_pos hmn_cop
        hm_ev hn_od hc_eq hb2_eq ha2_eq
    · -- (m odd, n even) sub-case: standard caseB_descends.
      exact fermat42Sub_caseB_descends
        fermat42SubCaseB_squareSplit_holds
        fermat42SubCaseB_fourthPowerSplit_holds
        A B C m n h_abs_min hA_pos hC_pos hm_nn hn_pos hmn_cop hm_od hn_ev
        hc_eq hb2_eq ha2_eq
  · -- Case A: B odd.
    have hB2_odd : B ^ 2 % 2 = 1 := by
      rw [show B ^ 2 = B * B from sq B, Int.mul_emod, hB_od]; decide
    have hB2_cop_nat : Int.gcd (B ^ 2) C = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp hB2_cop_C
    obtain ⟨m, n, hb2_eq, hc_eq, ha2_eq, hmn_gcd, hmn_par, hm_nn⟩ :=
      hpyth.coprime_classification' hB2_cop_nat hB2_odd hA2_pos
    have hmn_cop : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
    -- In Case A: B² ≡ 1 mod 4 (B odd, B² ≡ 1 mod 8).  So m² - n² = B² ≡ 1 mod 4,
    -- which forces m odd, n even.
    have hm_odd : m % 2 = 1 ∧ n % 2 = 0 := by
      have hB2_mod : B ^ 2 % 4 = 1 := by
        obtain ⟨k, hk⟩ : ∃ k, B = 2 * k + 1 := ⟨(B - 1) / 2, by omega⟩
        have : B ^ 2 = 4 * (k * k + k) + 1 := by rw [hk]; ring
        rw [this]; omega
      rcases hmn_par with ⟨hm_ev, hn_od⟩ | ⟨hm_od, hn_ev⟩
      · exfalso
        -- m even, n odd: m² ≡ 0, n² ≡ 1 mod 4 ⟹ B² = m² - n² ≡ -1 ≡ 3 mod 4. Contradiction.
        obtain ⟨m₀, hm₀⟩ : (2 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero hm_ev
        have hm2_mod : m ^ 2 % 4 = 0 := by
          rw [hm₀]
          have : (2 * m₀) ^ 2 = 4 * m₀ ^ 2 := by ring
          rw [this, Int.mul_emod_right]
        have hn2_mod : n ^ 2 % 4 = 1 := by
          obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨(n - 1) / 2, by omega⟩
          subst hk
          have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
          rw [this]; omega
        have : B ^ 2 % 4 = 3 := by
          rw [hb2_eq, Int.sub_emod, hm2_mod, hn2_mod]; decide
        rw [this] at hB2_mod; norm_num at hB2_mod
      · exact ⟨hm_od, hn_ev⟩
    have hn_pos : 0 < n := by
      rcases lt_or_eq_of_le hm_nn with hm_pos' | hm_zero
      · have : 0 < 2 * m * n := by rw [← hc_eq]; exact hC_pos
        nlinarith [hm_pos']
      · exfalso
        rw [← hm_zero] at hc_eq
        simp at hc_eq
        linarith
    exact fermat42Sub_caseA_reduces
      fermat42SubCaseA_squareSplit_holds
      fermat42Double_impossible_unconditional
      A B C m n h_abs_min hA_pos hC_pos hm_nn hn_pos hmn_cop hm_odd.1 hm_odd.2
      hb2_eq ha2_eq


end  -- noncomputable section
