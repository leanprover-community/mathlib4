/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Zify

/-!
# Lemmas about `Nat.nthRoot`

In this file we prove that `Nat.nthRoot n a` is indeed the floor of `ⁿ√a`.

## TODO

Rewrite the proof of `Nat.nthRoot.lt_pow_go_succ_aux` to avoid dependencies on real numbers,
so that we can move this file to `Mathlib/Data/Nat/NthRoot`, then to Batteries.
-/

namespace Nat

variable {m n a b guess fuel : ℕ}

@[simp] theorem nthRoot_zero_left (a : ℕ) : nthRoot 0 a = 1 := rfl

@[simp] theorem nthRoot_one_left : nthRoot 1 = id := rfl

@[simp]
theorem nthRoot_zero_right (h : n ≠ 0) : nthRoot n 0 = 0 := by
  rcases n with _|_|_ <;> grind [nthRoot, nthRoot.go]

@[simp]
theorem nthRoot_one_right : nthRoot n 1 = 1 := by
  rcases n with _|_|_ <;> simp [nthRoot, nthRoot.go, Nat.add_comm 1]

private theorem nthRoot.pow_go_le (hle : guess ≤ fuel) (n a : ℕ) :
    go n a fuel guess ^ (n + 2) ≤ a := by
  induction fuel generalizing guess with
  | zero =>
    obtain rfl : guess = 0 := by grind
    simp [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      grind
    case neg =>
      have : guess ≤ a / guess ^ (n + 1) := by
        linarith only [Nat.mul_le_of_le_div _ _ _ (not_lt.1 h)]
      replace := Nat.mul_le_of_le_div _ _ _ this
      grind

/-- `nthRoot n a ^ n ≤ a` unless both `n` and `a` are zeros. -/
@[simp]
theorem pow_nthRoot_le_iff : nthRoot n a ^ n ≤ a ↔ n ≠ 0 ∨ a ≠ 0 := by
  rcases n with _|_|_ <;> first | grind | simp [nthRoot, nthRoot.pow_go_le]

alias ⟨_, pow_nthRoot_le⟩ := pow_nthRoot_le_iff


lemma binom_pow_ge_first_two_terms (n : ℕ) (u v : ℤ) (hu : u ≥ 0) (huv : u + v > 0) :
    (u + v) ^ (n + 1) ≥ u ^ (n + 1) + (n + 1) * u ^ n * v := by
  induction n;
  case zero =>
    simp
  case succ n ih =>
  calc
  (u + v) ^ (n + 2)
    = (u + v) ^ (n + 1) * (u + v) := by rw [pow_succ]
  _ ≥ (u ^ (n + 1) + (n + 1) * u ^ n * v) * (u + v) := by gcongr
  _ = u ^ (n + 2) + (n + 2) * u ^ (n + 1) * v + (n + 1) * u ^ n * v ^ 2 := by ring1
  _ ≥ u ^ (n + 2) + (n + 2) * u ^ (n + 1) * v := by
    have hh : ((n : ℤ) + 1) * u ^ n * v ^ 2 ≥ 0 := by positivity
    set w :=  (u : ℤ) ^ (n + 2) + (n +2) * u ^ (n + 1) * v with hw
    nth_rw 2 [← add_zero w]
    exact add_le_add_left hh w


private theorem nthRoot.lt_pow_go_succ_aux0 (hb : b ≠ 0) :
    a ≤ ( (a ^ (n + 1) / b ^ n) + n * b) / (n + 1) := by

  rcases a.eq_zero_or_pos with rfl | ha
  · exact Nat.zero_le _

  have b_pow_pos: 0 < (b : Int) ^ n:= by positivity

  have hk : ((b : Int) + ((a - b) : Int)) ^ (n + 1)
    ≥ b ^ (n + 1) + (n + 1) * b ^ n * (a - b) := by
    apply binom_pow_ge_first_two_terms
    · exact Nat.cast_nonneg b
    · rw [add_comm, sub_add_comm, sub_self, zero_add]
      exact_mod_cast ha

  have hj : a = ((b : Int) + ((a - b : Int))) := by
    rw [add_comm, sub_add_comm, sub_self, zero_add]

  rw [← hj, ge_iff_le] at hk
  have hl : (a : Int) ^ (n + 1) + n * b ^ (n + 1) ≥ (n + 1) * b ^ n * a := by
    calc a ^ (n + 1) + n * b ^ (n + 1)
      = (a : Int) ^ (n + 1) + n * b ^ (n + 1) := by norm_cast
    _ ≥ b ^ (n + 1) + (n + 1) * b ^ n * (a - b) + n * b ^ (n + 1) := by linarith only [hk]
    _ = (n + 1) * b ^ n * a := by ring1
  norm_cast at hl
  have hq := @Nat.div_le_div_right ((n+1)*b^n *a) (a ^ (n + 1) + n * b ^ (n+1)) (b ^ n) hl
  nth_rw 1 [Nat.mul_comm] at hq
  rw [← mul_assoc] at hq
  rw [Nat.add_div_of_dvd_left _] at hq
  · nth_rw 2 [Nat.pow_add] at hq
    nth_rw 4 [Nat.mul_comm] at hq
    rw [← Nat.mul_assoc] at hq
    rw [Nat.mul_div_cancel _ (pow_pos (zero_lt_of_ne_zero hb) n)] at hq
    rw [Nat.mul_div_cancel _ (pow_pos (zero_lt_of_ne_zero hb) n)] at hq
    rw [pow_one] at hq
    calc a = a * (n + 1) / (n + 1) := by rw [Nat.mul_div_cancel _ (add_one_pos n)]
    _ ≤ (a ^ (n + 1) / b ^ n + n * b) / (n + 1) := by exact Nat.div_le_div_right hq
  rw [pow_succ, mul_comm, mul_assoc]
  exact dvd_mul_right (b ^ n) _

private theorem nthRoot.always_exists (n a : ℕ) :
    ∃ c, c ^ (n + 1) ≤ a ∧ a < (c + 1) ^ (n + 1) := by
  have H : ∃ c, a < (c + 1) ^ (n + 1) := by
    use a
    apply Nat.le_self_pow
    positivity
  set c := Nat.find H with hc
  use c
  exact ⟨by
    rcases c.eq_zero_or_pos with h₀ | hpos
    · rw [h₀, zero_pow]
      · exact Nat.zero_le _
      positivity
    calc
      c ^ (n + 1) = (c - 1 + 1) ^ (n + 1) := by
                  congr
                  exact (Nat.sub_eq_iff_eq_add hpos).mp rfl
                _ ≤ a := by
                  rw [← Nat.not_gt_eq _ _]
                  apply Nat.find_min H
                  rw [← hc]
                  exact sub_one_lt_of_lt hpos
    , Nat.find_spec H⟩

/--
An auxiliary lemma saying that if `b ≠ 0`,
then `(a / b ^ n + n * b) / (n + 1) + 1` is a strict upper estimate on `√[n + 1] a`.
-/
theorem nthRoot.lt_pow_go_succ_aux (hb : b ≠ 0) :
     a < ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
  have ⟨c, hc1, hc2⟩ := nthRoot.always_exists n a
  calc a < (c + 1)^(n + 1) := hc2
  _ ≤ ((c ^ (n + 1) / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
    gcongr
    exact nthRoot.lt_pow_go_succ_aux0 hb
  _ ≤ ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
    gcongr

private theorem nthRoot.lt_pow_go_succ (hlt : a < (guess + 1) ^ (n + 2)) :
    a < (go n a fuel guess + 1) ^ (n + 2) := by
  induction fuel generalizing guess with
  | zero => simpa [go]
  | succ fuel ih =>
    rw [go]
    split_ifs with h
    case pos =>
      rcases eq_or_ne guess 0 with rfl | hguess
      · grind
      · exact ih <| Nat.nthRoot.lt_pow_go_succ_aux hguess
    case neg =>
      assumption

theorem lt_pow_nthRoot_add_one (hn : n ≠ 0) (a : ℕ) : a < (nthRoot n a + 1) ^ n := by
  match n, hn with
  | 1, _ => simp
  | n + 2, hn =>
    simp only [nthRoot]
    apply nthRoot.lt_pow_go_succ
    exact a.lt_succ_self.trans_le (Nat.le_self_pow hn _)

@[simp]
theorem le_nthRoot_iff (hn : n ≠ 0) : a ≤ nthRoot n b ↔ a ^ n ≤ b := by
  cases le_or_gt a (nthRoot n b) with
  | inl hle =>
    simp only [hle, true_iff]
    refine le_trans ?_ (pow_nthRoot_le (.inl hn))
    gcongr
  | inr hlt =>
    simp only [hlt.not_ge, false_iff, not_le]
    refine (lt_pow_nthRoot_add_one hn b).trans_le ?_
    gcongr
    assumption

@[simp]
theorem nthRoot_lt_iff (hn : n ≠ 0) : nthRoot n a < b ↔ a < b ^ n := by
  simp only [← not_le, le_nthRoot_iff hn]

@[simp]
theorem nthRoot_pow (hn : n ≠ 0) (a : ℕ) : nthRoot n (a ^ n) = a := by
  refine eq_of_forall_le_iff fun b ↦ ?_
  rw [le_nthRoot_iff hn]
  exact (Nat.pow_left_strictMono hn).le_iff_le

/-- If `a ^ n ≤ b < (a + 1) ^ n`, then `n` root of `b` equals `a`. -/
theorem nthRoot_eq_of_le_of_lt (h₁ : a ^ n ≤ b) (h₂ : b < (a + 1) ^ n) :
    nthRoot n b = a := by
  rcases eq_or_ne n 0 with rfl | hn
  · grind
  simp only [← le_nthRoot_iff hn, ← nthRoot_lt_iff hn] at h₁ h₂
  grind

theorem exists_pow_eq_iff' (hn : n ≠ 0) : (∃ x, x ^ n = a) ↔ (nthRoot n a) ^ n = a := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [nthRoot_pow hn]
  · grind

theorem exists_pow_eq_iff :
    (∃ x, x ^ n = a) ↔ ((n = 0 ∧ a = 1) ∨ (n ≠ 0 ∧ (nthRoot n a) ^ n = a)) := by
  rcases eq_or_ne n 0 with rfl | _ <;> grind [exists_pow_eq_iff']

instance instDecidableExistsPowEq : Decidable (∃ x, x ^ n = a) :=
  decidable_of_iff' _ exists_pow_eq_iff

end Nat
