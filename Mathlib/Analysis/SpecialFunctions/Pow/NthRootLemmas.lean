/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Tactic.Rify

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

/--
An auxiliary lemma saying that if `b ≠ 0`,
then `(a / b ^ n + n * b) / (n + 1) + 1` is a strict upper estimate on `√[n + 1] a`.

Currently, the proof relies on the weighted AM-GM inequality,
which increases the dependency closure of this file by a lot.

A PR proving this inequality by more elementary means is very welcome.
-/
theorem nthRoot.lt_pow_go_succ_aux (hb : b ≠ 0) :
    a < ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn; · simp
  rw [← Nat.add_mul_div_left a, Nat.div_div_eq_div_mul] <;> try positivity
  rify
  calc
    (a : ℝ) = ((a / b ^ n) ^ (1 / (n + 1) : ℝ) * b ^ (n / (n + 1) : ℝ)) ^ (n + 1) := by
      rw [mul_pow, ← Real.rpow_mul_natCast, ← Real.rpow_mul_natCast] <;> try positivity
      simp (disch := positivity) [div_mul_cancel₀]
    _ ≤ ((1 / (n + 1)) * (a / b ^ n) + (n / (n + 1)) * b) ^ (n + 1) := by
      gcongr
      apply Real.geom_mean_le_arith_mean2_weighted <;> try positivity
      simp [field, add_comm]
    _ = ((a + b ^ n * (n * b)) / (b ^ n * (n + 1))) ^ (n + 1) := by
      congr 1
      field_simp
    _ < _ := by
      gcongr ?_ ^ _
      convert lt_floor_add_one (R := ℝ) _ using 1
      norm_cast
      rw [Nat.floor_div_natCast, Nat.floor_natCast]

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
