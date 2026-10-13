import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# The Jacobsthal function

The Jacobsthal function `j(n)` (Jacobsthal, 1961) is the maximal gap between consecutive
integers coprime to `n`. This file defines `Nat.jacobsthal` and proves the exact value for
the primorial `2310 = 2·3·5·7·11`:

> **`jacobsthal 2310 = 14`**: every interval of length 14 contains an integer coprime to
> 2310, and the bound is attained — after `113`, the next coprime is `127`.

## Main results
* `Nat.jacobsthal` — the Jacobsthal function.
* `Nat.coprime_2310_iff` — a characterization of coprimality to 2310.
* `Nat.jacobsthal_2310` — the window/attainment theorem for the primorial 2310.
* `Nat.jacobsthal_2310_value` — `jacobsthal 2310 = 14`.

## Structure of the proof
1. `coprimeTo2310` — predicate "coprime to 2310" (not divisible by 2, 3, 5, 7, 11);
2. periodicity mod 2310 (`coprimeTo2310_shift`, `coprimeTo2310_add_mul`);
3. a bounded check of the 2310 residues (`jacobsthal_residues`);
4. transfer from residues to all `n` (`jacobsthal_2310`);
5. the bridge to `Nat.Coprime` (`coprime_2310_iff`);
6. the general function `jacobsthal` and the value `jacobsthal 2310 = 14` via `sSup`.
-/

namespace Nat


/-- An integer coprime to the primorial `2310 = 2·3·5·7·11`:
not divisible by any of 2, 3, 5, 7, 11. Equivalent to `Nat.Coprime n 2310`. -/
def coprimeTo2310 (n : ℕ) : Bool :=
  n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && n % 7 != 0 && n % 11 != 0

/-! ## Periodicity mod 2310 -/

/-- Adding `2310` (a multiple of `q`) does not change the residue mod `q`. -/
lemma mod_add_period (x q : ℕ) (hdiv : q ∣ 2310) : (x + 2310) % q = x % q := by
  rw [← Nat.div_mul_cancel hdiv]
  rw [Nat.mul_comm]
  exact Nat.add_mul_mod_self_left x q (2310 / q)

/-- `coprimeTo2310` is periodic with period 2310. -/
lemma coprimeTo2310_shift (x : ℕ) : coprimeTo2310 (x + 2310) = coprimeTo2310 x := by
  unfold coprimeTo2310
  have h2 : (x + 2310) % 2 = x % 2 := mod_add_period x 2 (by norm_num)
  have h3 : (x + 2310) % 3 = x % 3 := mod_add_period x 3 (by norm_num)
  have h5 : (x + 2310) % 5 = x % 5 := mod_add_period x 5 (by norm_num)
  have h7 : (x + 2310) % 7 = x % 7 := mod_add_period x 7 (by norm_num)
  have h11 : (x + 2310) % 11 = x % 11 := mod_add_period x 11 (by norm_num)
  simp [h2, h3, h5, h7, h11]

/-- Periodicity on any number of periods. -/
lemma coprimeTo2310_add_mul (x t : ℕ) : coprimeTo2310 (x + 2310 * t) = coprimeTo2310 x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ]
    rw [← add_assoc]
    rw [coprimeTo2310_shift (x + 2310 * t)]
    exact ih

/-! ## The bound -/

/-- Every residue class mod 2310 has, within distance 13, a coprime-to-2310 element.
  A finite exhaustive check (2310 residues × 13 offsets) — a proof, not a computation. -/
lemma jacobsthal_residues : ∀ r : ℕ, r < 2310 → ∃ d : ℕ, d < 14 ∧ coprimeTo2310 (r + d + 1) = true := by
  native_decide

/-- The Jacobsthal value for the primorial 2310: `j(2310) = 14`.
  The upper bound holds for all `n`; the value 14 is attained at `n = 113`. -/
theorem jacobsthal_2310 :
    (∀ n : ℕ, ∃ d : ℕ, d < 14 ∧ coprimeTo2310 (n + d + 1) = true) ∧
    ∃ n : ℕ, coprimeTo2310 (n + 14) = true ∧ ∀ d : ℕ, d < 13 → coprimeTo2310 (n + d + 1) = false := by
  constructor
  · intro n
    have hn := Nat.div_add_mod n 2310
    let r := n % 2310
    have hr : r < 2310 := Nat.mod_lt n (by norm_num : 0 < 2310)
    rcases jacobsthal_residues r hr with ⟨d, hd, hcop⟩
    refine ⟨d, hd, ?_⟩
    have hpath : n + d + 1 = r + d + 1 + 2310 * (n / 2310) := by omega
    rw [hpath]
    rw [coprimeTo2310_add_mul (r + d + 1) (n / 2310)]
    exact hcop
  · refine ⟨113, ?_, ?_⟩
    · native_decide
    · native_decide

/-! ## Bridge to the standard `Nat.Coprime`

`coprimeTo2310` is equivalent to the standard `Nat.Coprime n 2310`. This connects the
formalization to the library and lets the general Jacobsthal function (see `Jacobsthal.lean`)
be stated in terms of the standard coprimeness predicate. -/

/-- Prop version of the predicate (clean projections instead of `Bool`). -/
def CoprimeTo2310 (n : ℕ) : Prop :=
  n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0 ∧ n % 11 ≠ 0

/-- The `Bool` and `Prop` versions are equivalent. -/
lemma coprimeTo2310_bool_iff (n : ℕ) : coprimeTo2310 n = true ↔ CoprimeTo2310 n := by
  constructor
  · intro h
    have h2 : n % 2 ≠ 0 := by
      intro hnz
      have hf : coprimeTo2310 n = false := by simp [coprimeTo2310, hnz]
      rw [h] at hf
      simp at hf
    have h3 : n % 3 ≠ 0 := by
      intro hnz
      have hf : coprimeTo2310 n = false := by simp [coprimeTo2310, hnz]
      rw [h] at hf
      simp at hf
    have h5 : n % 5 ≠ 0 := by
      intro hnz
      have hf : coprimeTo2310 n = false := by simp [coprimeTo2310, hnz]
      rw [h] at hf
      simp at hf
    have h7 : n % 7 ≠ 0 := by
      intro hnz
      have hf : coprimeTo2310 n = false := by simp [coprimeTo2310, hnz]
      rw [h] at hf
      simp at hf
    have h11 : n % 11 ≠ 0 := by
      intro hnz
      have hf : coprimeTo2310 n = false := by simp [coprimeTo2310, hnz]
      rw [h] at hf
      simp at hf
    exact ⟨h2, h3, h5, h7, h11⟩
  · intro h
    rcases h with ⟨h2, h3, h5, h7, h11⟩
    unfold coprimeTo2310
    have h2b : (n % 2 != 0) = true := by simpa using h2
    rw [h2b]
    have h3b : (n % 3 != 0) = true := by simpa using h3
    rw [h3b]
    have h5b : (n % 5 != 0) = true := by simpa using h5
    rw [h5b]
    have h7b : (n % 7 != 0) = true := by simpa using h7
    rw [h7b]
    have h11b : (n % 11 != 0) = true := by simpa using h11
    rw [h11b]
    simp

/-- If `n` is coprime to 2310, none of 2, 3, 5, 7, 11 divides `n`. -/
lemma coprime2310_not_dvd {n q : ℕ} (h : Nat.Coprime n 2310) (hq : q ∣ 2310) (hq1 : q ≠ 1) : ¬ q ∣ n := by
  intro hqn
  have hqgcd : q ∣ Nat.gcd n 2310 := Nat.dvd_gcd hqn hq
  have hq1' : q ∣ 1 := by
    rw [Nat.Coprime] at h
    simpa [h] using hqgcd
  exact hq1 (Nat.dvd_one.mp hq1')

/-- Direction `Nat.Coprime n 2310 → CoprimeTo2310 n`. -/
lemma coprimeTo2310_of_coprime (n : ℕ) (h : Nat.Coprime n 2310) : CoprimeTo2310 n := by
  have h2 : ¬ 2 ∣ n := coprime2310_not_dvd h (by norm_num) (by norm_num)
  have h3 : ¬ 3 ∣ n := coprime2310_not_dvd h (by norm_num) (by norm_num)
  have h5 : ¬ 5 ∣ n := coprime2310_not_dvd h (by norm_num) (by norm_num)
  have h7 : ¬ 7 ∣ n := coprime2310_not_dvd h (by norm_num) (by norm_num)
  have h11 : ¬ 11 ∣ n := coprime2310_not_dvd h (by norm_num) (by norm_num)
  unfold CoprimeTo2310
  constructor
  · intro hm; exact h2 (Nat.dvd_iff_mod_eq_zero.2 hm)
  · constructor
    · intro hm; exact h3 (Nat.dvd_iff_mod_eq_zero.2 hm)
    · constructor
      · intro hm; exact h5 (Nat.dvd_iff_mod_eq_zero.2 hm)
      · constructor
        · intro hm; exact h7 (Nat.dvd_iff_mod_eq_zero.2 hm)
        · intro hm; exact h11 (Nat.dvd_iff_mod_eq_zero.2 hm)

/-- Every prime divisor of 2310 is one of 2, 3, 5, 7, 11. -/
lemma prime_dvd_2310 {p : ℕ} (hp : p.Prime) (h : p ∣ 2310) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have h' : p ∣ 2 * (3 * (5 * (7 * 11))) := by
    rw [show 2 * (3 * (5 * (7 * 11))) = 2310 by norm_num]
    exact h
  rcases (hp.dvd_mul).mp h' with h2 | hrest
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).mp h2)
  · rcases (hp.dvd_mul).mp hrest with h3 | hrest
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h3))
    · rcases (hp.dvd_mul).mp hrest with h5 | hrest
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h5)))
      · rcases (hp.dvd_mul).mp hrest with h7 | hrest
        · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h7))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11)).mp hrest))))

/-- Direction `CoprimeTo2310 n → Nat.Coprime n 2310`. -/
lemma coprime_of_CoprimeTo2310 {n : ℕ} (h : CoprimeTo2310 n) : Nat.Coprime n 2310 := by
  by_contra hnot
  rw [Nat.Coprime] at hnot
  have hn0 : n ≠ 0 := by
    intro hz
    simp [CoprimeTo2310, hz] at h
  have hgpos : 0 < Nat.gcd n 2310 := Nat.gcd_pos_of_pos_left 2310 (Nat.pos_of_ne_zero hn0)
  have hge1 : 1 ≤ Nat.gcd n 2310 := by omega
  have hgt1 : 1 < Nat.gcd n 2310 := lt_of_le_of_ne hge1 (fun heq => hnot heq.symm)
  rcases Nat.exists_prime_and_dvd (by omega : Nat.gcd n 2310 ≠ 1) with ⟨p, hp, hpgcd⟩
  have hpn : p ∣ n := Nat.dvd_trans hpgcd (Nat.gcd_dvd_left n 2310)
  have hp2310 : p ∣ 2310 := Nat.dvd_trans hpgcd (Nat.gcd_dvd_right n 2310)
  have hpsmall := prime_dvd_2310 hp hp2310
  rcases hpsmall with h2 | h3 | h5 | h7 | h11
  · subst h2; exact h.1 (Nat.dvd_iff_mod_eq_zero.mp hpn)
  · subst h3; exact (h.2).1 (Nat.dvd_iff_mod_eq_zero.mp hpn)
  · subst h5; exact ((h.2).2).1 (Nat.dvd_iff_mod_eq_zero.mp hpn)
  · subst h7; exact (((h.2).2).2).1 (Nat.dvd_iff_mod_eq_zero.mp hpn)
  · subst h11; exact (((h.2).2).2).2 (Nat.dvd_iff_mod_eq_zero.mp hpn)

/-- **Bridge:** `coprimeTo2310` is equivalent to the standard `Nat.Coprime n 2310`. -/
theorem coprime_2310_iff (n : ℕ) : CoprimeTo2310 n ↔ Nat.Coprime n 2310 := by
  exact ⟨coprime_of_CoprimeTo2310, coprimeTo2310_of_coprime n⟩


/-- The Jacobsthal function: the maximal gap between consecutive integers coprime to `m`. -/
noncomputable def jacobsthal (m : ℕ) : ℕ :=
  sSup {d : ℕ | ∃ n, n.Coprime m ∧ (n + d).Coprime m ∧ ∀ k, n < k → k < n + d → ¬ k.Coprime m}

/-- Every interval of length 14 contains an integer coprime to 2310 (via the bridge). -/
lemma window_coprime_2310 (n : ℕ) : ∃ e, e < 14 ∧ (n + e + 1).Coprime 2310 := by
  rcases jacobsthal_2310.1 n with ⟨d, hd, hcop⟩
  refine ⟨d, hd, ?_⟩
  exact (coprime_2310_iff (n + d + 1)).1 ((coprimeTo2310_bool_iff (n + d + 1)).1 hcop)

/-- The gap 14 is attained: 113 and 127 are coprime to 2310, and 114..126 are not. -/
lemma attained_14 : (14 ∈ {d : ℕ | ∃ n, n.Coprime 2310 ∧ (n + d).Coprime 2310 ∧
    ∀ k, n < k → k < n + d → ¬ k.Coprime 2310}) := by
  refine ⟨113, ?_, ?_, ?_⟩
  · exact (coprime_2310_iff 113).1 (by norm_num [CoprimeTo2310] : CoprimeTo2310 113)
  · exact (coprime_2310_iff 127).1 (by norm_num [CoprimeTo2310] : CoprimeTo2310 127)
  · intro k hk1 hk2
    have hC : ∀ d : ℕ, d < 13 → coprimeTo2310 (113 + d + 1) = false := by native_decide
    have hmod : coprimeTo2310 k = false := by
      have hd : k - 114 < 13 := by omega
      have hpath : k = 113 + (k - 114) + 1 := by omega
      rw [hpath]
      exact hC (k - 114) hd
    have hnp : ¬ CoprimeTo2310 k := by
      intro hp
      have htrue : coprimeTo2310 k = true := (coprimeTo2310_bool_iff k).2 hp
      rw [hmod] at htrue
      simp at htrue
    intro hkc
    exact hnp ((coprime_2310_iff k).2 hkc)

/-- No gap between consecutive coprimes to 2310 exceeds 14 (from the window property). -/
lemma gap_le_2310 {d : ℕ} (hd : ∃ n, n.Coprime 2310 ∧ (n + d).Coprime 2310 ∧
    ∀ k, n < k → k < n + d → ¬ k.Coprime 2310) : d ≤ 14 := by
  rcases hd with ⟨n, hn, hnd, hgap⟩
  by_contra hnot
  have hgt : 14 < d := lt_of_not_ge hnot
  rcases window_coprime_2310 n with ⟨e, he, hcop⟩
  exact hgap (n + e + 1) (by omega) (by omega) hcop

/-- **The Jacobsthal value for the primorial 2310: `jacobsthal 2310 = 14`.** -/
theorem jacobsthal_2310_value : jacobsthal 2310 = 14 := by
  unfold jacobsthal
  apply le_antisymm
  · apply csSup_le
    · exact ⟨14, attained_14⟩
    · intro d hd
      exact gap_le_2310 hd
  · apply le_csSup
    · refine ⟨14, ?_⟩
      intro d hd
      exact gap_le_2310 hd
    · exact attained_14


end Nat
