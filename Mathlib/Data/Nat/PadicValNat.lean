/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.RingTheory.Multiplicity

/-!
# The p-adic valuation on natural numbers
-/

@[expose] public section

namespace Nat

/-- For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such
that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`. -/
def _root_.padicValNat (p n : ℕ) : ℕ := (maxPowDvdDiv p n).fst

open maxPowDvdDiv in
@[simp]
theorem divMaxPow_mul_pow_padicValNat (p n : ℕ) : divMaxPow n p * p ^ padicValNat p n = n := by
  unfold divMaxPow padicValNat
  fun_cases maxPowDvdDiv with
  | case1 h => exact go_spec h |>.1
  | case2 h => simp

theorem padicValNat_def {p n : ℕ} : padicValNat p n = multiplicity p n := by
  by_cases hn : n = 0
  · simp [padicValNat, maxPowDvdDiv, hn]
  by_cases hp : p = 1
  · simp [padicValNat, maxPowDvdDiv, hp]
  refine .symm <| multiplicity_eq_of_dvd_of_not_dvd
    (Dvd.intro_left (n.divMaxPow p) (divMaxPow_mul_pow_padicValNat p n)) ?_
  by_cases hp0 : p = 0
  · simp_all
  nth_rw 2 [← divMaxPow_mul_pow_padicValNat p n]
  rw [pow_add_one', mul_dvd_mul_iff_right (pow_ne_zero (padicValNat p n) hp0)]
  exact not_dvd_divMaxPow (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hp0, hp⟩) hn

@[deprecated (since := "2026-09-11")] alias _root_.padicValNat_zero_left := multiplicity_zero_left
@[deprecated (since := "2026-09-11")] alias _root_.padicValNat_one_left := multiplicity_one_left
@[deprecated (since := "2026-09-11")] alias _root_.padicValNat_zero_right := multiplicity_zero_right

theorem maxPowDvdDiv_of_not_dvd {p n : ℕ} (h : ¬p ∣ n) : maxPowDvdDiv p n = (0, n) := by
  cases n with
  | zero => simp at h
  | succ n => simp [maxPowDvdDiv, Nat.dvd_iff_mod_eq_zero.not.mp h, maxPowDvdDiv.go]

@[simp]
theorem maxPowDvdDiv_one_right (p : ℕ) : maxPowDvdDiv p 1 = (0, 1) := by
  rcases eq_or_ne p 1 with rfl | hp <;> simp [maxPowDvdDiv_of_not_dvd, *]

@[deprecated (since := "2026-09-11")] alias _root_.padicValNat_one_right := multiplicity_one_right

@[simp]
theorem divMaxPow_one_left (p : ℕ) : divMaxPow 1 p = 1 := by simp [divMaxPow]

@[simp]
theorem pow_multiplicity_mul_divMaxPow (p n : ℕ) : p ^ multiplicity p n * divMaxPow n p = n := by
  rw [← padicValNat_def, Nat.mul_comm, divMaxPow_mul_pow_padicValNat]

@[deprecated (since := "2026-09-11")] alias pow_padicValNat_mul_divMaxPow :=
  pow_multiplicity_mul_divMaxPow

@[deprecated (since := "2026-09-11")] alias _root_.pow_padicValNat_dvd := pow_multiplicity_dvd

theorem multiplicity_lt_self {p n : ℕ} (hn : n ≠ 0) : multiplicity p n < n := by
  match p with
  | 0 | 1 => simp [Nat.pos_of_ne_zero hn]
  | p + 2 =>
    apply (p + 2 |>.pow_lt_pow_iff_right <| by lia).mp
    apply Nat.lt_of_le_of_lt ?_ <| Nat.lt_pow_self <| by lia
    exact le_of_dvd (Nat.pos_of_ne_zero hn) (pow_multiplicity_dvd ..)

@[deprecated (since := "2026-09-11")] alias padicValNat_lt_self := multiplicity_lt_self

theorem multiplicity_le_self {p : ℕ} (n : ℕ) : multiplicity p n ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact Nat.le_of_lt <| multiplicity_lt_self hn

@[deprecated (since := "2026-09-11")] alias padicValNat_le_self := multiplicity_le_self

private theorem pow_dvd_iff_le_of_spec {p k n a b : ℕ} (hp : 1 < p) (hn : n ≠ 0)
    (hab : p ^ a * b = n) (hb : ¬p ∣ b) : p ^ k ∣ n ↔ k ≤ a := by
  subst hab
  cases Nat.lt_or_ge a k with
  | inl hlt =>
    refine iff_of_false (fun hdvd ↦ ?_) (Nat.not_le_of_lt hlt)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc, Nat.pow_add,
      Nat.mul_dvd_mul_iff_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))] at hdvd
    exact hb <| Nat.dvd_of_pow_dvd (Nat.le_add_left 1 l) hdvd
  | inr hle =>
    refine iff_of_true (Nat.dvd_mul_right_of_dvd ?_ _) hle
    exact Nat.pow_dvd_pow p hle

/-- If `p > 1`, `n > 0`, then the first component of `maxPowDvdDiv` is the maximal power of `p`
that divides `n`. -/
theorem pow_dvd_iff_le_multiplicity {p k n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ multiplicity p n := by
  obtain rfl | hp₁ : p = 0 ∨ 1 < p := by grind
  · rcases k.eq_zero_or_pos with rfl | hk <;> simp [Nat.ne_of_gt, *]
  · exact pow_dvd_iff_le_of_spec hp₁ hn (pow_multiplicity_mul_divMaxPow p n)
      (not_dvd_divMaxPow hp₁ hn)

@[deprecated (since := "2026-09-11")] alias pow_dvd_iff_le_padicValNat :=
  pow_dvd_iff_le_multiplicity

theorem maxPowDvdDiv_of_pow_mul_eq {p n k l : ℕ} (hn : n ≠ 0) (h : p ^ k * l = n)
    (hl : ¬p ∣ l) : maxPowDvdDiv p n = (k, l) := by
  obtain rfl | rfl | hp : p = 0 ∨ p = 1 ∨ 1 < p := by grind
  · cases k.eq_zero_or_pos <;> simp_all
  · simp_all
  · have hk : k = (p.maxPowDvdDiv n).1 := by
      · apply Nat.le_antisymm
        · rw [← padicValNat, padicValNat_def, ← pow_dvd_iff_le_multiplicity (Nat.ne_of_gt hp) hn,
            pow_dvd_iff_le_of_spec hp hn h hl]
        · rw [← pow_dvd_iff_le_of_spec hp hn h hl, pow_dvd_iff_le_multiplicity (Nat.ne_of_gt hp) hn]
          exact padicValNat_def.le
    rw [← pow_multiplicity_mul_divMaxPow p n, hk, ← padicValNat_def, padicValNat,
      Nat.mul_left_cancel_iff] at h
    · exact Prod.ext hk.symm h.symm
    · exact Nat.pow_pos <| Nat.zero_lt_of_lt hp

@[simp]
theorem maxPowDvdDiv_base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (k : ℕ) :
    p.maxPowDvdDiv (p ^ k * n) = (multiplicity p n + k, divMaxPow n p) := by
  apply maxPowDvdDiv_of_pow_mul_eq
  · exact Nat.mul_ne_zero (Nat.ne_of_gt <| Nat.pow_pos <| Nat.zero_lt_of_lt hp) hn
  · rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, pow_multiplicity_mul_divMaxPow]
  · exact not_dvd_divMaxPow hp hn

@[simp]
theorem _root_.multiplicity_base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (k : ℕ) :
    multiplicity p (p ^ k * n) = multiplicity p n + k := by
  simp [← padicValNat_def, padicValNat, *]

@[deprecated (since := "2026-09-11")] alias _root_.padicValNat_base_pow_mul :=
  multiplicity_base_pow_mul

@[simp]
theorem divMaxPow_base_pow_mul {p : ℕ} (hp : p ≠ 0) (n k : ℕ) :
    (p ^ k * n).divMaxPow p = n.divMaxPow p := by
  obtain rfl | hp1 : p = 1 ∨ 1 < p := by grind
  · simp
  · rcases eq_or_ne n 0 with rfl | hn <;> simp [divMaxPow, *]

@[simp]
theorem maxPowDvdDiv_base_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    p.maxPowDvdDiv (p * n) = (multiplicity p n + 1, divMaxPow n p) := by
  simpa using maxPowDvdDiv_base_pow_mul hp hn 1

@[simp]
theorem _root_.multiplicity_base_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    multiplicity p (p * n) = multiplicity p n + 1 := by
  simp [← padicValNat_def, padicValNat, *]

@[deprecated (since := "2026-09-11")] alias _root_.padicValNat_base_mul := multiplicity_base_mul

@[simp]
theorem divMaxPow_base_mul {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    (p * n).divMaxPow p = n.divMaxPow p := by
  simpa using divMaxPow_base_pow_mul hp n 1

@[simp]
theorem maxPowDvdDiv_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : p.maxPowDvdDiv (p ^ k) = (k, 1) := by
  simpa using maxPowDvdDiv_base_pow_mul hp Nat.one_ne_zero k

@[simp]
theorem _root_.multiplicity_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : multiplicity p (p ^ k) = k := by
  simp [← padicValNat_def, padicValNat, hp]

@[deprecated (since := "2026-09-11")] alias _root_.padicValNat_base_pow := multiplicity_base_pow

@[simp]
theorem divMaxPow_base_pow {p : ℕ} (hp : p ≠ 0) (k : ℕ) : (p ^ k).divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow_mul hp 1 k

@[simp]
theorem maxPowDvdDiv_self {p : ℕ} (hp : 1 < p) : p.maxPowDvdDiv p = (1, 1) := by
  simpa using maxPowDvdDiv_base_pow hp 1

@[simp]
theorem _root_.multiplicity_base {p : ℕ} (hp : 1 < p) : multiplicity p p = 1 := by
  simpa using multiplicity_base_pow hp 1

@[deprecated (since := "2026-09-11")] alias _root_.padicValNat_base := multiplicity_base

@[simp]
theorem divMaxPow_self {p : ℕ} (hp : p ≠ 0) : p.divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow hp 1

@[simp]
theorem fst_maxPowDvdDiv (p n : ℕ) : (p.maxPowDvdDiv n).1 = multiplicity p n := padicValNat_def

@[simp]
theorem snd_maxPowDvdDiv (p n : ℕ) : (p.maxPowDvdDiv n).2 = n.divMaxPow p := rfl

@[deprecated (since := "2026-03-15")]
alias maxPowDiv := multiplicity

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_mul_eq_succ := multiplicity_base_mul

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_pow_mul := multiplicity_base_pow_mul

@[deprecated (since := "2026-03-15")]
alias ⟨_, maxPowDiv.le_of_dvd⟩ := pow_dvd_iff_le_multiplicity

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.pow_dvd := pow_multiplicity_dvd

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.zero := multiplicity_zero_right

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.zero_base := multiplicity_zero_left

end Nat
