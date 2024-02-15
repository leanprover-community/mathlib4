/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Stuart Presnell
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Nat.Order.Basic

#align_import data.nat.choose.basic from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"

/-!
# Binomial coefficients

This file defines binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).

## Main definition and results

* `Nat.choose`: binomial coefficients, defined inductively
* `Nat.choose_eq_factorial_div_factorial`: a proof that `choose n k = n! / (k! * (n - k)!)`
* `Nat.choose_symm`: symmetry of binomial coefficients
* `Nat.choose_le_succ_of_lt_half_left`: `choose n k` is increasing for small values of `k`
* `Nat.choose_le_middle`: `choose n r` is maximised when `r` is `n/2`
* `Nat.descFactorial_eq_factorial_mul_choose`: Relates binomial coefficients to the descending
  factorial. This is used to prove `Nat.choose_le_pow` and variants. We provide similar statements
  for the ascending factorial.
* `Nat.multichoose`: whereas `choose` counts combinations, `multichoose` counts multicombinations.
The fact that this is indeed the correct counting function for multisets is proved in
`Sym.card_sym_eq_multichoose` in `Data.Sym.Card`.
* `Nat.multichoose_eq` : a proof that `multichoose n k = (n + k - 1).choose k`.
This is central to the "stars and bars" technique in informal mathematics, where we switch between
counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
("stars") separated by `n-1` dividers ("bars").  See `Data.Sym.Card` for more detail.

## Tags

binomial coefficient, combination, multicombination, stars and bars
-/


open Nat

namespace Nat

/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. -/
def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)
#align nat.choose Nat.choose

@[simp]
theorem choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n <;> rfl
#align nat.choose_zero_right Nat.choose_zero_right

@[simp]
theorem choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 :=
  rfl
#align nat.choose_zero_succ Nat.choose_zero_succ

theorem choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) :=
  rfl
#align nat.choose_succ_succ Nat.choose_succ_succ

theorem choose_succ_succ' (n k : ℕ) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) :=
  rfl

theorem choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, k + 1, _ => choose_zero_succ _
  | n + 1, k + 1, hk => by
    have hnk : n < k := lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [choose_succ_succ, choose_eq_zero_of_lt hnk, choose_eq_zero_of_lt hnk1]
#align nat.choose_eq_zero_of_lt Nat.choose_eq_zero_of_lt

@[simp]
theorem choose_self (n : ℕ) : choose n n = 1 := by
  induction n <;> simp [*, choose, choose_eq_zero_of_lt (lt_succ_self _)]
#align nat.choose_self Nat.choose_self

@[simp]
theorem choose_succ_self (n : ℕ) : choose n (succ n) = 0 :=
  choose_eq_zero_of_lt (lt_succ_self _)
#align nat.choose_succ_self Nat.choose_succ_self

@[simp]
theorem choose_one_right (n : ℕ) : choose n 1 = n := by induction n <;> simp [*, choose, add_comm]
#align nat.choose_one_right Nat.choose_one_right

-- The `n+1`-st triangle number is `n` more than the `n`-th triangle number
theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rw [← add_mul_div_left, mul_comm 2 n, ← mul_add, add_tsub_cancel_right, mul_comm]
  cases n <;> rfl; apply zero_lt_succ
#align nat.triangle_succ Nat.triangle_succ

/-- `choose n 2` is the `n`-th triangle number. -/
theorem choose_two_right (n : ℕ) : choose n 2 = n * (n - 1) / 2 := by
  induction' n with n ih
  · simp
  · rw [triangle_succ n, choose, ih]
    simp [add_comm]
#align nat.choose_two_right Nat.choose_two_right

theorem choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
  | 0, _, hk => by rw [Nat.eq_zero_of_le_zero hk]; decide
  | n + 1, 0, _ => by simp
  | n + 1, k + 1, hk => by
    rw [choose_succ_succ]
    exact add_pos_of_pos_of_nonneg (choose_pos (le_of_succ_le_succ hk)) (Nat.zero_le _)
#align nat.choose_pos Nat.choose_pos

theorem choose_eq_zero_iff {n k : ℕ} : n.choose k = 0 ↔ n < k :=
  ⟨fun h => lt_of_not_ge (mt Nat.choose_pos h.symm.not_lt), Nat.choose_eq_zero_of_lt⟩
#align nat.choose_eq_zero_iff Nat.choose_eq_zero_iff

theorem succ_mul_choose_eq : ∀ n k, succ n * choose n k = choose (succ n) (succ k) * succ k
  | 0, 0 => by decide
  | 0, k + 1 => by simp [choose]
  | n + 1, 0 => by simp [choose, mul_succ, succ_eq_add_one, add_comm]
  | n + 1, k + 1 => by
    rw [choose_succ_succ (succ n) (succ k), add_mul, ← succ_mul_choose_eq n, mul_succ, ←
      succ_mul_choose_eq n, add_right_comm, ← mul_add, ← choose_succ_succ, ← succ_mul]
#align nat.succ_mul_choose_eq Nat.succ_mul_choose_eq

theorem choose_mul_factorial_mul_factorial : ∀ {n k}, k ≤ n → choose n k * k ! * (n - k)! = n !
  | 0, _, hk => by simp [Nat.eq_zero_of_le_zero hk]
  | n + 1, 0, _ => by simp
  | n + 1, succ k, hk => by
    rcases lt_or_eq_of_le hk with hk₁ | hk₁
    · have h : choose n k * k.succ ! * (n - k)! = (k + 1) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk)]
        simp [factorial_succ, mul_comm, mul_left_comm, mul_assoc]
      have h₁ : (n - k)! = (n - k) * (n - k.succ)! := by
        rw [← succ_sub_succ, succ_sub (le_of_lt_succ hk₁), factorial_succ]
      have h₂ : choose n (succ k) * k.succ ! * ((n - k) * (n - k.succ)!) = (n - k) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁)]
        simp [factorial_succ, mul_comm, mul_left_comm, mul_assoc]
      have h₃ : k * n ! ≤ n * n ! := Nat.mul_le_mul_right _ (le_of_succ_le_succ hk)
      rw [choose_succ_succ, add_mul, add_mul, succ_sub_succ, h, h₁, h₂, add_mul, tsub_mul,
        factorial_succ, ← add_tsub_assoc_of_le h₃, add_assoc, ← add_mul, add_tsub_cancel_left,
        add_comm]
    · rw [hk₁]; simp [hk₁, mul_comm, choose, tsub_self]
#align nat.choose_mul_factorial_mul_factorial Nat.choose_mul_factorial_mul_factorial

theorem choose_mul {n k s : ℕ} (hkn : k ≤ n) (hsk : s ≤ k) :
    n.choose k * k.choose s = n.choose s * (n - s).choose (k - s) :=
  have h : (n - k)! * (k - s)! * s ! ≠ 0 := by apply_rules [factorial_ne_zero, mul_ne_zero]
  mul_right_cancel₀ h <|
  calc
    n.choose k * k.choose s * ((n - k)! * (k - s)! * s !) =
        n.choose k * (k.choose s * s ! * (k - s)!) * (n - k)! :=
      by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc _ s !, mul_assoc, mul_comm (n - k)!,
        mul_comm s !]
    _ = n ! :=
      by rw [choose_mul_factorial_mul_factorial hsk, choose_mul_factorial_mul_factorial hkn]
    _ = n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) :=
      by rw [choose_mul_factorial_mul_factorial (tsub_le_tsub_right hkn _),
        choose_mul_factorial_mul_factorial (hsk.trans hkn)]
    _ = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s !) :=
      by rw [tsub_tsub_tsub_cancel_right hsk, mul_assoc, mul_left_comm s !, mul_assoc,
        mul_comm (k - s)!, mul_comm s !, mul_right_comm, ← mul_assoc]
#align nat.choose_mul Nat.choose_mul

theorem choose_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
    choose n k = n ! / (k ! * (n - k)!) := by
  rw [← choose_mul_factorial_mul_factorial hk, mul_assoc]
  exact (mul_div_left _ (mul_pos (factorial_pos _) (factorial_pos _))).symm
#align nat.choose_eq_factorial_div_factorial Nat.choose_eq_factorial_div_factorial

theorem add_choose (i j : ℕ) : (i + j).choose j = (i + j)! / (i ! * j !) := by
  rw [choose_eq_factorial_div_factorial (Nat.le_add_left j i), add_tsub_cancel_right, mul_comm]
#align nat.add_choose Nat.add_choose

theorem add_choose_mul_factorial_mul_factorial (i j : ℕ) :
    (i + j).choose j * i ! * j ! = (i + j)! := by
  rw [← choose_mul_factorial_mul_factorial (Nat.le_add_left _ _), add_tsub_cancel_right,
    mul_right_comm]
#align nat.add_choose_mul_factorial_mul_factorial Nat.add_choose_mul_factorial_mul_factorial

theorem factorial_mul_factorial_dvd_factorial {n k : ℕ} (hk : k ≤ n) : k ! * (n - k)! ∣ n ! := by
  rw [← choose_mul_factorial_mul_factorial hk, mul_assoc]; exact dvd_mul_left _ _
#align nat.factorial_mul_factorial_dvd_factorial Nat.factorial_mul_factorial_dvd_factorial

theorem factorial_mul_factorial_dvd_factorial_add (i j : ℕ) : i ! * j ! ∣ (i + j)! := by
  suffices i ! * (i + j - i) ! ∣ (i + j)! by
    rwa [add_tsub_cancel_left i j] at this
  exact factorial_mul_factorial_dvd_factorial (Nat.le_add_right _ _)
#align nat.factorial_mul_factorial_dvd_factorial_add Nat.factorial_mul_factorial_dvd_factorial_add

@[simp]
theorem choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := by
  rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial (Nat.sub_le _ _),
    tsub_tsub_cancel_of_le hk, mul_comm]
#align nat.choose_symm Nat.choose_symm

theorem choose_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : Nat.choose n a = Nat.choose n b := by
  suffices choose n (n - b) = choose n b by
    rw [h, add_tsub_cancel_right] at this; rwa [h]
  exact choose_symm (h ▸ le_add_left _ _)
#align nat.choose_symm_of_eq_add Nat.choose_symm_of_eq_add

theorem choose_symm_add {a b : ℕ} : choose (a + b) a = choose (a + b) b :=
  choose_symm_of_eq_add rfl
#align nat.choose_symm_add Nat.choose_symm_add

theorem choose_symm_half (m : ℕ) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m := by
  apply choose_symm_of_eq_add
  rw [add_comm m 1, add_assoc 1 m m, add_comm (2 * m) 1, two_mul m]
#align nat.choose_symm_half Nat.choose_symm_half

theorem choose_succ_right_eq (n k : ℕ) : choose n (k + 1) * (k + 1) = choose n k * (n - k) := by
  have e : (n + 1) * choose n k = choose n k * (k + 1) + choose n (k + 1) * (k + 1) := by
    rw [← right_distrib, ← choose_succ_succ, succ_mul_choose_eq]
  rw [← tsub_eq_of_eq_add_rev e, mul_comm, ← mul_tsub, add_tsub_add_eq_tsub_right]
#align nat.choose_succ_right_eq Nat.choose_succ_right_eq

@[simp]
theorem choose_succ_self_right : ∀ n : ℕ, (n + 1).choose n = n + 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_succ_self_right n, choose_self]
#align nat.choose_succ_self_right Nat.choose_succ_self_right

theorem choose_mul_succ_eq (n k : ℕ) : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) := by
  cases k with
  | zero => simp
  | succ k =>
    obtain hk | hk := le_or_lt (k + 1) (n + 1)
    · rw [choose_succ_succ, add_mul, succ_sub_succ, ← choose_succ_right_eq, ← succ_sub_succ,
        mul_tsub, add_tsub_cancel_of_le (Nat.mul_le_mul_left _ hk)]
    · rw [choose_eq_zero_of_lt hk, choose_eq_zero_of_lt (n.lt_succ_self.trans hk), zero_mul,
        zero_mul]
#align nat.choose_mul_succ_eq Nat.choose_mul_succ_eq

theorem ascFactorial_eq_factorial_mul_choose (n k : ℕ) :
    (n + 1).ascFactorial k = k ! * (n + k).choose k := by
  rw [mul_comm]
  apply mul_right_cancel₀ (factorial_ne_zero (n + k - k))
  rw [choose_mul_factorial_mul_factorial <| Nat.le_add_left k n, add_tsub_cancel_right,
    ← factorial_mul_ascFactorial, mul_comm]
#align nat.asc_factorial_eq_factorial_mul_choose Nat.ascFactorial_eq_factorial_mul_choose

theorem ascFactorial_eq_factorial_mul_choose' (n k : ℕ) :
    n.ascFactorial k = k ! * (n + k - 1).choose k := by
  cases n
  · cases k
    · rw [ascFactorial_zero, choose_zero_right, factorial_zero, mul_one]
    · simp only [zero_ascFactorial, zero_eq, zero_add, ge_iff_le, succ_sub_succ_eq_sub,
        nonpos_iff_eq_zero, tsub_zero, choose_succ_self, mul_zero]
  rw [ascFactorial_eq_factorial_mul_choose]
  simp only [ge_iff_le, succ_add_sub_one]

theorem factorial_dvd_ascFactorial (n k : ℕ) : k ! ∣ n.ascFactorial k :=
  ⟨(n + k - 1).choose k, ascFactorial_eq_factorial_mul_choose' _ _⟩
#align nat.factorial_dvd_asc_factorial Nat.factorial_dvd_ascFactorial

theorem choose_eq_asc_factorial_div_factorial (n k : ℕ) :
    (n + k).choose k = (n + 1).ascFactorial k / k ! := by
  apply mul_left_cancel₀ (factorial_ne_zero k)
  rw [← ascFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_div_cancel' <| factorial_dvd_ascFactorial _ _).symm
#align nat.choose_eq_asc_factorial_div_factorial Nat.choose_eq_asc_factorial_div_factorial

theorem choose_eq_asc_factorial_div_factorial' (n k : ℕ) :
    (n + k - 1).choose k = n.ascFactorial k / k ! := by
  apply mul_left_cancel₀ (factorial_ne_zero k)
  rw [← ascFactorial_eq_factorial_mul_choose']
  exact (Nat.mul_div_cancel' <| factorial_dvd_ascFactorial _ _).symm

theorem descFactorial_eq_factorial_mul_choose (n k : ℕ) : n.descFactorial k = k ! * n.choose k := by
  obtain h | h := Nat.lt_or_ge n k
  · rw [descFactorial_eq_zero_iff_lt.2 h, choose_eq_zero_of_lt h, mul_zero]
  rw [mul_comm]
  apply mul_right_cancel₀ (factorial_ne_zero (n - k))
  rw [choose_mul_factorial_mul_factorial h, ← factorial_mul_descFactorial h, mul_comm]
#align nat.desc_factorial_eq_factorial_mul_choose Nat.descFactorial_eq_factorial_mul_choose

theorem factorial_dvd_descFactorial (n k : ℕ) : k ! ∣ n.descFactorial k :=
  ⟨n.choose k, descFactorial_eq_factorial_mul_choose _ _⟩
#align nat.factorial_dvd_desc_factorial Nat.factorial_dvd_descFactorial

theorem choose_eq_descFactorial_div_factorial (n k : ℕ) : n.choose k = n.descFactorial k / k ! := by
  apply mul_left_cancel₀ (factorial_ne_zero k)
  rw [← descFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_div_cancel' <| factorial_dvd_descFactorial _ _).symm
#align nat.choose_eq_desc_factorial_div_factorial Nat.choose_eq_descFactorial_div_factorial

/-- A faster implementation of `choose`, to be used during bytecode evaluation
and in compiled code. -/
def fast_choose n k := Nat.descFactorial n k / Nat.factorial k

@[csimp] lemma choose_eq_fast_choose : Nat.choose = fast_choose :=
  funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))


/-! ### Inequalities -/


/-- Show that `Nat.choose` is increasing for small values of the right argument. -/
theorem choose_le_succ_of_lt_half_left {r n : ℕ} (h : r < n / 2) :
    choose n r ≤ choose n (r + 1) := by
  refine' le_of_mul_le_mul_right _ (lt_tsub_iff_left.mpr (lt_of_lt_of_le h (n.div_le_self 2)))
  rw [← choose_succ_right_eq]
  apply Nat.mul_le_mul_left
  rw [← Nat.lt_iff_add_one_le, lt_tsub_iff_left, ← mul_two]
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h zero_lt_two) (n.div_mul_le_self 2)
#align nat.choose_le_succ_of_lt_half_left Nat.choose_le_succ_of_lt_half_left

/-- Show that for small values of the right argument, the middle value is largest. -/
private theorem choose_le_middle_of_le_half_left {n r : ℕ} (hr : r ≤ n / 2) :
    choose n r ≤ choose n (n / 2) :=
  decreasingInduction
    (fun _ k a =>
      (eq_or_lt_of_le a).elim (fun t => t.symm ▸ le_rfl) fun h =>
        (choose_le_succ_of_lt_half_left h).trans (k h))
    hr (fun _ => le_rfl) hr

/-- `choose n r` is maximised when `r` is `n/2`. -/
theorem choose_le_middle (r n : ℕ) : choose n r ≤ choose n (n / 2) := by
  cases' le_or_gt r n with b b
  · rcases le_or_lt r (n / 2) with a | h
    · apply choose_le_middle_of_le_half_left a
    · rw [← choose_symm b]
      apply choose_le_middle_of_le_half_left
      rw [div_lt_iff_lt_mul' zero_lt_two] at h
      rw [le_div_iff_mul_le' zero_lt_two, tsub_mul, tsub_le_iff_tsub_le, mul_two,
        add_tsub_cancel_right]
      exact le_of_lt h
  · rw [choose_eq_zero_of_lt b]
    apply zero_le
#align nat.choose_le_middle Nat.choose_le_middle

/-! #### Inequalities about increasing the first argument -/


theorem choose_le_succ (a c : ℕ) : choose a c ≤ choose a.succ c := by
  cases c <;> simp [Nat.choose_succ_succ]
#align nat.choose_le_succ Nat.choose_le_succ

theorem choose_le_add (a b c : ℕ) : choose a c ≤ choose (a + b) c := by
  induction' b with b_n b_ih
  · simp
  exact le_trans b_ih (choose_le_succ (a + b_n) c)
#align nat.choose_le_add Nat.choose_le_add

theorem choose_le_choose {a b : ℕ} (c : ℕ) (h : a ≤ b) : choose a c ≤ choose b c :=
  add_tsub_cancel_of_le h ▸ choose_le_add a (b - a) c
#align nat.choose_le_choose Nat.choose_le_choose

theorem choose_mono (b : ℕ) : Monotone fun a => choose a b := fun _ _ => choose_le_choose b
#align nat.choose_mono Nat.choose_mono

/-! #### Multichoose

Whereas `choose n k` is the number of subsets of cardinality `k` from a type of cardinality `n`,
`multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`.

Alternatively, whereas `choose n k` counts the number of combinations,
i.e. ways to select `k` items (up to permutation) from `n` items without replacement,
`multichoose n k` counts the number of multicombinations,
i.e. ways to select `k` items (up to permutation) from `n` items with replacement.

Note that `multichoose` is *not* the multinomial coefficient, although it can be computed
in terms of multinomial coefficients. For details see https://mathworld.wolfram.com/Multichoose.html

TODO: Prove that `choose (-n) k = (-1)^k * multichoose n k`,
where `choose` is the generalized binomial coefficient.
<https://github.com/leanprover-community/mathlib/pull/15072#issuecomment-1171415738>

-/

--Porting note: `termination_by` required here where it wasn't before
/--
`multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`. -/
def multichoose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 =>
    multichoose n (k + 1) + multichoose (n + 1) k
  termination_by a b => (a, b)
#align nat.multichoose Nat.multichoose

@[simp]
theorem multichoose_zero_right (n : ℕ) : multichoose n 0 = 1 := by cases n <;> simp [multichoose]
#align nat.multichoose_zero_right Nat.multichoose_zero_right

@[simp]
theorem multichoose_zero_succ (k : ℕ) : multichoose 0 (k + 1) = 0 := by simp [multichoose]
#align nat.multichoose_zero_succ Nat.multichoose_zero_succ

theorem multichoose_succ_succ (n k : ℕ) :
    multichoose (n + 1) (k + 1) = multichoose n (k + 1) + multichoose (n + 1) k := by
  simp [multichoose]
#align nat.multichoose_succ_succ Nat.multichoose_succ_succ

@[simp]
theorem multichoose_one (k : ℕ) : multichoose 1 k = 1 := by
  induction' k with k IH; · simp
  simp [multichoose_succ_succ 0 k, IH]
#align nat.multichoose_one Nat.multichoose_one

@[simp]
theorem multichoose_two (k : ℕ) : multichoose 2 k = k + 1 := by
  induction' k with k IH; · simp
  rw [multichoose, IH]
  simp [add_comm, succ_eq_add_one]
#align nat.multichoose_two Nat.multichoose_two

@[simp]
theorem multichoose_one_right (n : ℕ) : multichoose n 1 = n := by
  induction' n with n IH; · simp
  simp [multichoose_succ_succ n 0, IH]
#align nat.multichoose_one_right Nat.multichoose_one_right

theorem multichoose_eq : ∀ n k : ℕ, multichoose n k = (n + k - 1).choose k
  | _, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    have : n + (k + 1) < (n + 1) + (k + 1) := add_lt_add_right (Nat.lt_succ_self _) _
    have : (n + 1) + k < (n + 1) + (k + 1) := add_lt_add_left (Nat.lt_succ_self _) _
    erw [multichoose_succ_succ, add_comm, Nat.succ_add_sub_one, ← add_assoc, Nat.choose_succ_succ]
    simp [multichoose_eq n (k+1), multichoose_eq (n+1) k]
  termination_by a b => a + b
  decreasing_by all_goals assumption
#align nat.multichoose_eq Nat.multichoose_eq

end Nat
