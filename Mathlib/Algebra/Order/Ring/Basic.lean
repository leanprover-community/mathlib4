/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Bound.Attribute

/-!
# Basic lemmas about ordered rings
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Int

variable {α M R : Type*}

theorem IsSquare.nonneg [Semiring R] [LinearOrder R] [IsRightCancelAdd R]
    [ZeroLEOneClass R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftStrictMono R]
    {x : R} (h : IsSquare x) : 0 ≤ x := by
  rcases h with ⟨y, rfl⟩
  exact mul_self_nonneg y

namespace MonoidHom

variable [Ring R] [Monoid M] [LinearOrder M] [MulLeftMono M] (f : R →* M)

theorem map_neg_one : f (-1) = 1 :=
  (pow_eq_one_iff (Nat.succ_ne_zero 1)).1 <| by rw [← map_pow, neg_one_sq, map_one]

@[simp]
theorem map_neg (x : R) : f (-x) = f x := by rw [← neg_one_mul, map_mul, map_neg_one, one_mul]

theorem map_sub_swap (x y : R) : f (x - y) = f (y - x) := by rw [← map_neg, neg_sub]

end MonoidHom

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b x y : R} {n : ℕ}

theorem pow_add_pow_le (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : n ≠ 0) : x ^ n + y ^ n ≤ (x + y) ^ n := by
  rcases Nat.exists_eq_add_one_of_ne_zero hn with ⟨k, rfl⟩
  induction k with
  | zero => simp only [zero_add, pow_one, le_refl]
  | succ k ih =>
    let n := k.succ
    have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n))
    have h2 := add_nonneg hx hy
    calc
      x ^ (n + 1) + y ^ (n + 1) ≤ x * x ^ n + y * y ^ n + (x * y ^ n + y * x ^ n) := by
        rw [pow_succ' _ n, pow_succ' _ n]
        exact le_add_of_nonneg_right h1
      _ = (x + y) * (x ^ n + y ^ n) := by
        rw [add_mul, mul_add, mul_add, add_comm (y * x ^ n), ← add_assoc, ← add_assoc,
          add_assoc (x * x ^ n) (x * y ^ n), add_comm (x * y ^ n) (y * y ^ n), ← add_assoc]
      _ ≤ (x + y) ^ (n + 1) := by
        rw [pow_succ' _ n]
        exact mul_le_mul_of_nonneg_left (ih (Nat.succ_ne_zero k)) h2

attribute [bound] pow_le_one₀ one_le_pow₀

@[deprecated pow_le_pow_left₀ (since := "2024-11-13")]
theorem pow_le_pow_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n :=
  pow_le_pow_left₀ ha hab

lemma pow_add_pow_le' (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ n + b ^ n ≤ 2 * (a + b) ^ n := by
  rw [two_mul]
  gcongr <;> try assumption
  exacts [le_add_of_nonneg_right hb, le_add_of_nonneg_left ha]

end OrderedSemiring

section StrictOrderedSemiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {a x y : R} {n m : ℕ}

@[deprecated pow_lt_pow_left₀ (since := "2024-11-13")]
theorem pow_lt_pow_left (h : x < y) (hx : 0 ≤ x) : ∀ {n : ℕ}, n ≠ 0 → x ^ n < y ^ n :=
  pow_lt_pow_left₀ h hx

@[deprecated pow_left_strictMonoOn₀ (since := "2024-11-13")]
lemma pow_left_strictMonoOn (hn : n ≠ 0) : StrictMonoOn (· ^ n : R → R) {a | 0 ≤ a} :=
  pow_left_strictMonoOn₀ hn

@[deprecated pow_right_strictMono₀ (since := "2024-11-13")]
lemma pow_right_strictMono (h : 1 < a) : StrictMono (a ^ ·) :=
  pow_right_strictMono₀ h

@[deprecated pow_lt_pow_right₀ (since := "2024-11-13")]
theorem pow_lt_pow_right (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n :=
  pow_lt_pow_right₀ h hmn

@[deprecated pow_lt_pow_iff_right₀ (since := "2024-11-13")]
lemma pow_lt_pow_iff_right (h : 1 < a) : a ^ n < a ^ m ↔ n < m := pow_lt_pow_iff_right₀ h

@[deprecated pow_le_pow_iff_right₀ (since := "2024-11-13")]
lemma pow_le_pow_iff_right (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m := pow_le_pow_iff_right₀ h

@[deprecated lt_self_pow₀ (since := "2024-11-13")]
theorem lt_self_pow (h : 1 < a) (hm : 1 < m) : a < a ^ m := lt_self_pow₀ h hm

@[deprecated pow_right_strictAnti₀ (since := "2024-11-13")]
theorem pow_right_strictAnti (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  pow_right_strictAnti₀ h₀ h₁

@[deprecated pow_lt_pow_iff_right_of_lt_one₀ (since := "2024-11-13")]
theorem pow_lt_pow_iff_right_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁

@[deprecated pow_lt_pow_right_of_lt_one₀ (since := "2024-11-13")]
theorem pow_lt_pow_right_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  pow_lt_pow_right_of_lt_one₀ h₀ h₁ hmn

@[deprecated pow_lt_self_of_lt_one₀ (since := "2024-11-13")]
theorem pow_lt_self_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a :=
  pow_lt_self_of_lt_one₀ h₀ h₁ hn

end StrictOrderedSemiring

section StrictOrderedRing
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] {a : R}

lemma sq_pos_of_neg (ha : a < 0) : 0 < a ^ 2 := by rw [sq]; exact mul_pos_of_neg_of_neg ha ha

end StrictOrderedRing

section LinearOrderedSemiring
variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : ℕ}

@[deprecated pow_le_pow_iff_left₀ (since := "2024-11-12")]
lemma pow_le_pow_iff_left (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  pow_le_pow_iff_left₀ ha hb hn

@[deprecated pow_lt_pow_iff_left₀ (since := "2024-11-12")]
lemma pow_lt_pow_iff_left (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b :=
  pow_lt_pow_iff_left₀ ha hb hn

@[deprecated pow_right_injective₀ (since := "2024-11-12")]
lemma pow_right_injective (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective (a ^ ·) :=
  pow_right_injective₀ ha₀ ha₁

@[deprecated pow_right_inj₀ (since := "2024-11-12")]
lemma pow_right_inj (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n := pow_right_inj₀ ha₀ ha₁

@[deprecated sq_le_one_iff₀ (since := "2024-11-12")]
theorem sq_le_one_iff {a : R} (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 := sq_le_one_iff₀ ha

@[deprecated sq_lt_one_iff₀ (since := "2024-11-12")]
theorem sq_lt_one_iff {a : R} (ha : 0 ≤ a) : a ^ 2 < 1 ↔ a < 1 := sq_lt_one_iff₀ ha

@[deprecated one_le_sq_iff₀ (since := "2024-11-12")]
theorem one_le_sq_iff {a : R} (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a := one_le_sq_iff₀ ha

@[deprecated one_lt_sq_iff₀ (since := "2024-11-12")]
theorem one_lt_sq_iff {a : R} (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a := one_lt_sq_iff₀ ha

@[deprecated lt_of_pow_lt_pow_left₀ (since := "2024-11-12")]
theorem lt_of_pow_lt_pow_left (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_pow_lt_pow_left₀ n hb h

@[deprecated le_of_pow_le_pow_left₀ (since := "2024-11-12")]
theorem le_of_pow_le_pow_left (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_pow_le_pow_left₀ hn hb h

@[deprecated sq_eq_sq₀ (since := "2024-11-12")]
theorem sq_eq_sq {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b := sq_eq_sq₀ ha hb

@[deprecated lt_of_mul_self_lt_mul_self₀ (since := "2024-11-12")]
theorem lt_of_mul_self_lt_mul_self (hb : 0 ≤ b) : a * a < b * b → a < b :=
  lt_of_mul_self_lt_mul_self₀ hb

/-- A function `f : α → R` is nonarchimedean if it satisfies the ultrametric inequality
  `f (a + b) ≤ max (f a) (f b)` for all `a b : α`. -/
def IsNonarchimedean {α : Type*} [Add α] (f : α → R) : Prop := ∀ a b : α, f (a + b) ≤ f a ⊔ f b

/-!
### Lemmas for canonically linear ordered semirings or linear ordered rings

The slightly unusual typeclass assumptions `[LinearOrderedSemiring R] [ExistsAddOfLE R]` cover two
more familiar settings:
* `[LinearOrderedRing R]`, eg `ℤ`, `ℚ` or `ℝ`
* `[CanonicallyLinearOrderedSemiring R]` (although we don't actually have this typeclass), eg `ℕ`,
  `ℚ≥0` or `ℝ≥0`
-/

variable [ExistsAddOfLE R]

lemma add_sq_le : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  calc
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + (a * b + b * a) := by
        simp_rw [pow_succ', pow_zero, mul_one, add_mul, mul_add, add_comm (b * a), add_add_add_comm]
    _ ≤ a ^ 2 + b ^ 2 + (a * a + b * b) := add_le_add_left ?_ _
    _ = _ := by simp_rw [pow_succ', pow_zero, mul_one, two_mul]
  cases le_total a b
  · exact mul_add_mul_le_mul_add_mul ‹_› ‹_›
  · exact mul_add_mul_le_mul_add_mul' ‹_› ‹_›

-- TODO: Use `gcongr`, `positivity`, `ring` once those tactics are made available here
lemma add_pow_le (ha : 0 ≤ a) (hb : 0 ≤ b) : ∀ n, (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [pow_succ]
    calc
      _ ≤ 2 ^ n * (a ^ (n + 1) + b ^ (n + 1)) * (a + b) :=
          mul_le_mul_of_nonneg_right (add_pow_le ha hb (n + 1)) <| add_nonneg ha hb
      _ = 2 ^ n * (a ^ (n + 2) + b ^ (n + 2) + (a ^ (n + 1) * b + b ^ (n + 1) * a)) := by
          rw [mul_assoc, mul_add, add_mul, add_mul, ← pow_succ, ← pow_succ, add_comm _ (b ^ _),
            add_add_add_comm, add_comm (_ * a)]
      _ ≤ 2 ^ n * (a ^ (n + 2) + b ^ (n + 2) + (a ^ (n + 1) * a + b ^ (n + 1) * b)) :=
          mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) <| pow_nonneg (zero_le_two (α := R)) _
      _ = _ := by simp only [← pow_succ, ← two_mul, ← mul_assoc]; rfl
    · obtain hab | hba := le_total a b
      · exact mul_add_mul_le_mul_add_mul (pow_le_pow_left₀ ha hab _) hab
      · exact mul_add_mul_le_mul_add_mul' (pow_le_pow_left₀ hb hba _) hba

protected lemma Even.add_pow_le (hn : Even n) :
    (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n) := by
  obtain ⟨n, rfl⟩ := hn
  rw [← two_mul, pow_mul]
  calc
    _ ≤ (2 * (a ^ 2 + b ^ 2)) ^ n := pow_le_pow_left₀ (sq_nonneg _) add_sq_le _
    _ = 2 ^ n * (a ^ 2 + b ^ 2) ^ n := by -- TODO: Should be `Nat.cast_commute`
        rw [Commute.mul_pow]; simp [Commute, SemiconjBy, two_mul, mul_two]
    _ ≤ 2 ^ n * (2 ^ (n - 1) * ((a ^ 2) ^ n + (b ^ 2) ^ n)) := mul_le_mul_of_nonneg_left
          (add_pow_le (sq_nonneg _) (sq_nonneg _) _) <| pow_nonneg (zero_le_two (α := R)) _
    _ = _ := by
      simp only [← mul_assoc, ← pow_add, ← pow_mul]
      cases n
      · rfl
      · simp [Nat.two_mul]

lemma Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add]; exact mul_self_nonneg _

lemma Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n :=
  (hn.pow_nonneg _).lt_of_ne' (pow_ne_zero _ ha)

lemma Even.pow_pos_iff (hn : Even n) (h₀ : n ≠ 0) : 0 < a ^ n ↔ a ≠ 0 := by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add, mul_self_pos, pow_ne_zero_iff (by simpa using h₀)]

lemma Odd.pow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (pow_nonneg · _), fun ha ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ]
  exact mul_neg_of_pos_of_neg ((even_two_mul _).pow_pos ha.ne) ha

lemma Odd.pow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hn.pow_neg_iff

lemma Odd.pow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hn.pow_neg_iff, pow_eq_zero_iff]
  rintro rfl; simp [Odd, eq_comm (a := 0)] at hn

lemma Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.pow_nonpos_iff

alias ⟨_, Odd.pow_nonpos⟩ := Odd.pow_nonpos_iff
alias ⟨_, Odd.pow_neg⟩ := Odd.pow_neg_iff

lemma Odd.strictMono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by
  have hn₀ : n ≠ 0 := by rintro rfl; simp [Odd, eq_comm (a := 0)] at hn
  intro a b hab
  obtain ha | ha := le_total 0 a
  · exact pow_lt_pow_left₀ hab ha hn₀
  obtain hb | hb := lt_or_ge 0 b
  · exact (hn.pow_nonpos ha).trans_lt (pow_pos hb _)
  obtain ⟨c, hac⟩ := exists_add_of_le ha
  obtain ⟨d, hbd⟩ := exists_add_of_le hb
  have hd := nonneg_of_le_add_right (hb.trans_eq hbd)
  refine lt_of_add_lt_add_right (a := c ^ n + d ^ n) ?_
  dsimp
  calc
    a ^ n + (c ^ n + d ^ n) = d ^ n := by
      rw [← add_assoc, hn.pow_add_pow_eq_zero hac.symm, zero_add]
    _ < c ^ n := pow_lt_pow_left₀ ?_ hd hn₀
    _ = b ^ n + (c ^ n + d ^ n) := by rw [add_left_comm, hn.pow_add_pow_eq_zero hbd.symm, add_zero]
  refine lt_of_add_lt_add_right (a := a + b) ?_
  rwa [add_rotate', ← hbd, add_zero, add_left_comm, ← add_assoc, ← hac, zero_add]

lemma Odd.pow_injective {n : ℕ} (hn : Odd n) : Injective (· ^ n : R → R) :=
  hn.strictMono_pow.injective

lemma Odd.pow_lt_pow {n : ℕ} (hn : Odd n) {a b : R} : a ^ n < b ^ n ↔ a < b :=
  hn.strictMono_pow.lt_iff_lt

lemma Odd.pow_le_pow {n : ℕ} (hn : Odd n) {a b : R} : a ^ n ≤ b ^ n ↔ a ≤ b :=
  hn.strictMono_pow.le_iff_le

lemma Odd.pow_inj {n : ℕ} (hn : Odd n) {a b : R} : a ^ n = b ^ n ↔ a = b :=
  hn.pow_injective.eq_iff

lemma sq_pos_iff {a : R} : 0 < a ^ 2 ↔ a ≠ 0 := even_two.pow_pos_iff two_ne_zero

alias ⟨_, sq_pos_of_ne_zero⟩ := sq_pos_iff
alias pow_two_pos_of_ne_zero := sq_pos_of_ne_zero

lemma pow_four_le_pow_two_of_pow_two_le (h : a ^ 2 ≤ b) : a ^ 4 ≤ b ^ 2 :=
  (pow_mul a 2 2).symm ▸ pow_le_pow_left₀ (sq_nonneg a) h 2

end LinearOrderedSemiring
