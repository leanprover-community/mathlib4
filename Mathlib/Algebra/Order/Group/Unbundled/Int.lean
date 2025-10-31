/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.Basic

/-!
# Facts about `ℤ` as an (unbundled) ordered group

See note [foundational algebra order theory].

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton Ring

open Function Nat

namespace Int

theorem natCast_strictMono : StrictMono (· : ℕ → ℤ) := fun _ _ ↦ Int.ofNat_lt.2

/-! ### Miscellaneous lemmas -/

theorem abs_eq_natAbs : ∀ a : ℤ, |a| = natAbs a
  | (n : ℕ) => abs_of_nonneg <| natCast_nonneg _
  | -[_+1] => abs_of_nonpos <| le_of_lt <| negSucc_lt_zero _

@[norm_cast] lemma natCast_natAbs (n : ℤ) : (n.natAbs : ℤ) = |n| := n.abs_eq_natAbs.symm

theorem natAbs_abs (a : ℤ) : natAbs |a| = natAbs a := by rw [abs_eq_natAbs]; rfl

theorem sign_mul_abs (a : ℤ) : sign a * |a| = a := by
  rw [abs_eq_natAbs, sign_mul_natAbs a]

theorem sign_mul_self_eq_abs (a : ℤ) : sign a * a = |a| := by
  rw [abs_eq_natAbs, sign_mul_self_eq_natAbs]

lemma natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.natAbs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self

alias natAbs_le_self_pow_two := natAbs_le_self_sq

lemma le_self_sq (b : ℤ) : b ≤ b ^ 2 := le_trans le_natAbs (natAbs_le_self_sq _)

alias le_self_pow_two := le_self_sq

@[norm_cast] lemma abs_natCast (n : ℕ) : |(n : ℤ)| = n := abs_of_nonneg (natCast_nonneg n)

theorem natAbs_sub_pos_iff {i j : ℤ} : 0 < natAbs (i - j) ↔ i ≠ j := by
  rw [natAbs_pos, ne_eq, sub_eq_zero]

theorem natAbs_sub_ne_zero_iff {i j : ℤ} : natAbs (i - j) ≠ 0 ↔ i ≠ j :=
  Nat.ne_zero_iff_zero_lt.trans natAbs_sub_pos_iff

@[simp]
theorem abs_lt_one_iff {a : ℤ} : |a| < 1 ↔ a = 0 := by
  rw [← zero_add 1, lt_add_one_iff, abs_nonpos_iff]

theorem abs_le_one_iff {a : ℤ} : |a| ≤ 1 ↔ a = 0 ∨ a = 1 ∨ a = -1 := by
  rw [le_iff_lt_or_eq, abs_lt_one_iff]
  match a with
  | (n : ℕ) => simp [abs_eq_natAbs]
  | -[n+1] =>
      simp only [negSucc_ne_zero, abs_eq_natAbs, natAbs_negSucc, succ_eq_add_one,
        Int.natCast_add, cast_ofNat_Int, add_eq_right, natCast_eq_zero, false_or, reduceNeg]
      rw [negSucc_eq]
      cutsat

theorem one_le_abs {z : ℤ} (h₀ : z ≠ 0) : 1 ≤ |z| :=
  add_one_le_iff.mpr (abs_pos.mpr h₀)

lemma eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 := by
  by_contra h
  have := Int.natAbs_le_of_dvd_ne_zero h1 h
  rw [Int.abs_eq_natAbs] at h2
  cutsat

lemma abs_sub_lt_of_lt_lt {m a b : ℕ} (ha : a < m) (hb : b < m) : |(b : ℤ) - a| < m := by
  rw [abs_lt]; cutsat

/-! #### `/`  -/

theorem ediv_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < |b|) : a / b = 0 :=
  match b, |b|, abs_eq_natAbs b, H2 with
  | (n : ℕ), _, rfl, H2 => ediv_eq_zero_of_lt H1 H2
  | -[n+1], _, rfl, H2 => neg_injective <| by rw [← Int.ediv_neg]; exact ediv_eq_zero_of_lt H1 H2

/-! #### mod -/

@[simp]
theorem emod_abs (a b : ℤ) : a % |b| = a % b :=
  abs_by_cases (fun i => a % i = a % b) rfl (emod_neg _ _)

theorem emod_lt_abs (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < |b| := by
  rw [← emod_abs]; exact emod_lt_of_pos _ (abs_pos.2 H)

/-! ### properties of `/` and `%` -/

theorem abs_ediv_le_abs : ∀ a b : ℤ, |a / b| ≤ |a| :=
  suffices ∀ (a : ℤ) (n : ℕ), |a / n| ≤ |a| from fun a b =>
    match b, Int.eq_nat_or_neg b with
    | _, ⟨n, Or.inl rfl⟩ => this _ _
    | _, ⟨n, Or.inr rfl⟩ => by rw [Int.ediv_neg, abs_neg]; apply this
  fun a n => by
  rw [abs_eq_natAbs, abs_eq_natAbs];
  exact ofNat_le_ofNat_of_le
    (match a, n with
      | (m : ℕ), n => Nat.div_le_self _ _
      | -[m+1], 0 => Nat.zero_le _
      | -[m+1], n + 1 => Nat.succ_le_succ (Nat.div_le_self _ _))

theorem abs_sign_of_ne_zero {z : ℤ} (hz : z ≠ 0) : |z.sign| = 1 := by
  rw [abs_eq_natAbs, natAbs_sign_of_ne_zero hz, Int.ofNat_one]

@[deprecated (since := "2025-09-03")]
alias abs_sign_of_nonzero := abs_sign_of_ne_zero

protected theorem sign_eq_ediv_abs' (a : ℤ) : sign a = a / |a| :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (sign_mul_abs _).symm).symm

protected theorem sign_eq_abs_ediv (a : ℤ) : sign a = |a| / a :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left az (sign_mul_self_eq_abs _).symm).symm

end Int

section Group
variable {G : Type*} [Group G]

@[to_additive (attr := simp) abs_zsmul_eq_zero]
lemma zpow_abs_eq_one (a : G) (n : ℤ) : a ^ |n| = 1 ↔ a ^ n = 1 := by
  rw [← Int.natCast_natAbs, zpow_natCast, pow_natAbs_eq_one]

end Group
