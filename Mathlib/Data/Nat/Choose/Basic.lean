/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Stuart Presnell
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Monotone.Defs

/-!
# Binomial coefficients

This file defines binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).
For the lemma that `n.choose k` counts the `k`-element-subsets of an `n`-element set,
see `Fintype.card_powersetCard` in `Mathlib/Data/Finset/Powerset.lean`.

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

namespace Nat

/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. For the fact that this is the number of `k`-element-subsets of an `n`-element
set, see `Fintype.card_powersetCard`. -/
def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp]
theorem choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n <;> rfl

@[simp]
theorem choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 :=
  rfl

theorem choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) :=
  rfl

theorem choose_succ_succ' (n k : ℕ) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) :=
  rfl

theorem choose_succ_left (n k : ℕ) (hk : 0 < k) :
    choose (n + 1) k = choose n (k - 1) + choose n k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

theorem choose_succ_right (n k : ℕ) (hn : 0 < n) :
    choose n (k + 1) = choose (n - 1) k + choose (n - 1) (k + 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

theorem choose_eq_choose_pred_add {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    choose n k = choose (n - 1) (k - 1) + choose (n - 1) k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rw [choose_succ_right _ _ hn, Nat.add_one_sub_one]

theorem choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => choose_zero_succ _
  | n + 1, k + 1, hk => by
    have hnk : n < k := lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [choose_succ_succ, choose_eq_zero_of_lt hnk, choose_eq_zero_of_lt hnk1]

@[simp]
theorem choose_self (n : ℕ) : choose n n = 1 := by
  induction n <;> simp [*, choose, choose_eq_zero_of_lt (lt_succ_self _)]

@[simp]
theorem choose_succ_self (n : ℕ) : choose n (succ n) = 0 :=
  choose_eq_zero_of_lt (lt_succ_self _)

@[simp]
lemma choose_one_right (n : ℕ) : choose n 1 = n := by induction n <;> simp [*, choose, Nat.add_comm]

-- The `n + 1`-st triangle number is `n` more than the `n`-th triangle number
theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rw [← add_mul_div_left, Nat.mul_comm 2 n, ← Nat.mul_add, Nat.add_sub_cancel, Nat.mul_comm]
  cases n <;> rfl; apply zero_lt_succ

/-- `choose n 2` is the `n`-th triangle number. -/
theorem choose_two_right (n : ℕ) : choose n 2 = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [triangle_succ n, choose, ih]
    simp [Nat.add_comm]

theorem choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
  | 0, _, hk => by rw [Nat.eq_zero_of_le_zero hk]; decide
  | n + 1, 0, _ => by simp
  | _ + 1, _ + 1, hk => Nat.add_pos_left (choose_pos (le_of_succ_le_succ hk)) _

theorem choose_eq_zero_iff {n k : ℕ} : n.choose k = 0 ↔ n < k :=
  ⟨fun h => lt_of_not_ge (mt Nat.choose_pos h.symm.not_lt), Nat.choose_eq_zero_of_lt⟩

theorem choose_ne_zero_iff {n k : ℕ} : n.choose k ≠ 0 ↔ k ≤ n :=
  not_iff_not.1 <| by simp [choose_eq_zero_iff]

lemma choose_ne_zero {n k : ℕ} (h : k ≤ n) : n.choose k ≠ 0 :=
  (choose_pos h).ne'

theorem succ_mul_choose_eq : ∀ n k, succ n * choose n k = choose (succ n) (succ k) * succ k
  | 0, 0 => by decide
  | 0, k + 1 => by simp [choose]
  | n + 1, 0 => by simp [choose, mul_succ, Nat.add_comm]
  | n + 1, k + 1 => by
    rw [choose_succ_succ (succ n) (succ k), Nat.add_mul, ← succ_mul_choose_eq n, mul_succ, ←
      succ_mul_choose_eq n, Nat.add_right_comm, ← Nat.mul_add, ← choose_succ_succ, ← succ_mul]

theorem choose_mul_factorial_mul_factorial : ∀ {n k}, k ≤ n → choose n k * k ! * (n - k)! = n !
  | 0, _, hk => by simp [Nat.eq_zero_of_le_zero hk]
  | n + 1, 0, _ => by simp
  | n + 1, succ k, hk => by
    rcases lt_or_eq_of_le hk with hk₁ | hk₁
    · have h : choose n k * k.succ ! * (n - k)! = (k + 1) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₁ : (n - k)! = (n - k) * (n - k.succ)! := by
        rw [← succ_sub_succ, succ_sub (le_of_lt_succ hk₁), factorial_succ]
      have h₂ : choose n (succ k) * k.succ ! * ((n - k) * (n - k.succ)!) = (n - k) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₃ : k * n ! ≤ n * n ! := Nat.mul_le_mul_right _ (le_of_succ_le_succ hk)
      rw [choose_succ_succ, Nat.add_mul, Nat.add_mul, succ_sub_succ, h, h₁, h₂, Nat.add_mul,
        Nat.mul_sub_right_distrib, factorial_succ, ← Nat.add_sub_assoc h₃, Nat.add_assoc,
        ← Nat.add_mul, Nat.add_sub_cancel_left, Nat.add_comm]
    · rw [hk₁]; simp [Nat.mul_comm, choose, Nat.sub_self]

theorem choose_mul {n k s : ℕ} (hkn : k ≤ n) (hsk : s ≤ k) :
    n.choose k * k.choose s = n.choose s * (n - s).choose (k - s) :=
  have h : 0 < (n - k)! * (k - s)! * s ! := by apply_rules [factorial_pos, Nat.mul_pos]
  Nat.mul_right_cancel h <|
  calc
    n.choose k * k.choose s * ((n - k)! * (k - s)! * s !) =
        n.choose k * (k.choose s * s ! * (k - s)!) * (n - k)! := by
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc _ s !, Nat.mul_assoc,
        Nat.mul_comm (n - k)!, Nat.mul_comm s !]
    _ = n ! := by
      rw [choose_mul_factorial_mul_factorial hsk, choose_mul_factorial_mul_factorial hkn]
    _ = n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) := by
      rw [choose_mul_factorial_mul_factorial (Nat.sub_le_sub_right hkn _),
        choose_mul_factorial_mul_factorial (hsk.trans hkn)]
    _ = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s !) := by
      rw [Nat.sub_sub_sub_cancel_right hsk, Nat.mul_assoc, Nat.mul_left_comm s !, Nat.mul_assoc,
        Nat.mul_comm (k - s)!, Nat.mul_comm s !, Nat.mul_right_comm, ← Nat.mul_assoc]

theorem choose_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
    choose n k = n ! / (k ! * (n - k)!) := by
  rw [← choose_mul_factorial_mul_factorial hk, Nat.mul_assoc]
  exact (mul_div_left _ (Nat.mul_pos (factorial_pos _) (factorial_pos _))).symm

theorem add_choose (i j : ℕ) : (i + j).choose j = (i + j)! / (i ! * j !) := by
  rw [choose_eq_factorial_div_factorial (Nat.le_add_left j i), Nat.add_sub_cancel_right,
    Nat.mul_comm]

theorem add_choose_mul_factorial_mul_factorial (i j : ℕ) :
    (i + j).choose j * i ! * j ! = (i + j)! := by
  rw [← choose_mul_factorial_mul_factorial (Nat.le_add_left _ _), Nat.add_sub_cancel_right,
    Nat.mul_right_comm]

theorem factorial_mul_factorial_dvd_factorial {n k : ℕ} (hk : k ≤ n) : k ! * (n - k)! ∣ n ! := by
  rw [← choose_mul_factorial_mul_factorial hk, Nat.mul_assoc]; exact Nat.dvd_mul_left _ _

theorem factorial_mul_factorial_dvd_factorial_add (i j : ℕ) : i ! * j ! ∣ (i + j)! := by
  suffices i ! * (i + j - i)! ∣ (i + j)! by
    rwa [Nat.add_sub_cancel_left i j] at this
  exact factorial_mul_factorial_dvd_factorial (Nat.le_add_right _ _)

@[simp]
theorem choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := by
  rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial (Nat.sub_le _ _),
    Nat.sub_sub_self hk, Nat.mul_comm]

theorem choose_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : Nat.choose n a = Nat.choose n b := by
  suffices choose n (n - b) = choose n b by
    rw [h, Nat.add_sub_cancel_right] at this; rwa [h]
  exact choose_symm (h ▸ le_add_left _ _)

theorem choose_symm_add {a b : ℕ} : choose (a + b) a = choose (a + b) b :=
  choose_symm_of_eq_add rfl

theorem choose_symm_half (m : ℕ) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m := by
  apply choose_symm_of_eq_add
  rw [Nat.add_comm m 1, Nat.add_assoc 1 m m, Nat.add_comm (2 * m) 1, Nat.two_mul m]

theorem choose_succ_right_eq (n k : ℕ) : choose n (k + 1) * (k + 1) = choose n k * (n - k) := by
  have e : (n + 1) * choose n k = choose n (k + 1) * (k + 1) + choose n k * (k + 1) := by
    rw [← Nat.add_mul, Nat.add_comm (choose _ _), ← choose_succ_succ, succ_mul_choose_eq]
  rw [← Nat.sub_eq_of_eq_add e, Nat.mul_comm, ← Nat.mul_sub_left_distrib, Nat.add_sub_add_right]

@[simp]
theorem choose_succ_self_right : ∀ n : ℕ, (n + 1).choose n = n + 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_succ_self_right n, choose_self]

theorem choose_mul_succ_eq (n k : ℕ) : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) := by
  cases k with
  | zero => simp
  | succ k =>
    obtain hk | hk := le_or_gt (k + 1) (n + 1)
    · rw [choose_succ_succ, Nat.add_mul, succ_sub_succ, ← choose_succ_right_eq, ← succ_sub_succ,
        Nat.mul_sub_left_distrib, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hk)]
    · rw [choose_eq_zero_of_lt hk, choose_eq_zero_of_lt (n.lt_succ_self.trans hk), Nat.zero_mul,
        Nat.zero_mul]

theorem ascFactorial_eq_factorial_mul_choose (n k : ℕ) :
    (n + 1).ascFactorial k = k ! * (n + k).choose k := by
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n + k - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial <| Nat.le_add_left k n, Nat.add_sub_cancel_right,
    ← factorial_mul_ascFactorial, Nat.mul_comm]

theorem ascFactorial_eq_factorial_mul_choose' (n k : ℕ) :
    n.ascFactorial k = k ! * (n + k - 1).choose k := by
  cases n
  · cases k
    · rw [ascFactorial_zero, choose_zero_right, factorial_zero, Nat.mul_one]
    · simp only [zero_ascFactorial, Nat.zero_add, succ_sub_succ_eq_sub,
        Nat.sub_zero, choose_succ_self, Nat.mul_zero]
  rw [ascFactorial_eq_factorial_mul_choose]
  simp only [succ_add_sub_one]

theorem factorial_dvd_ascFactorial (n k : ℕ) : k ! ∣ n.ascFactorial k :=
  ⟨(n + k - 1).choose k, ascFactorial_eq_factorial_mul_choose' _ _⟩

theorem choose_eq_asc_factorial_div_factorial (n k : ℕ) :
    (n + k).choose k = (n + 1).ascFactorial k / k ! := by
  apply Nat.mul_left_cancel k.factorial_pos
  rw [← ascFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_div_cancel' <| factorial_dvd_ascFactorial _ _).symm

theorem choose_eq_asc_factorial_div_factorial' (n k : ℕ) :
    (n + k - 1).choose k = n.ascFactorial k / k ! :=
  Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (ascFactorial_eq_factorial_mul_choose' _ _).symm

theorem descFactorial_eq_factorial_mul_choose (n k : ℕ) : n.descFactorial k = k ! * n.choose k := by
  obtain h | h := Nat.lt_or_ge n k
  · rw [descFactorial_eq_zero_iff_lt.2 h, choose_eq_zero_of_lt h, Nat.mul_zero]
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial h, ← factorial_mul_descFactorial h, Nat.mul_comm]

theorem factorial_dvd_descFactorial (n k : ℕ) : k ! ∣ n.descFactorial k :=
  ⟨n.choose k, descFactorial_eq_factorial_mul_choose _ _⟩

theorem choose_eq_descFactorial_div_factorial (n k : ℕ) : n.choose k = n.descFactorial k / k ! :=
  Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (descFactorial_eq_factorial_mul_choose _ _).symm

/-- A faster implementation of `choose`, to be used during bytecode evaluation
and in compiled code. -/
def fast_choose n k := Nat.descFactorial n k / Nat.factorial k

@[csimp] lemma choose_eq_fast_choose : Nat.choose = fast_choose :=
  funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))


/-! ### Inequalities -/


/-- Show that `Nat.choose` is increasing for small values of the right argument. -/
theorem choose_le_succ_of_lt_half_left {r n : ℕ} (h : r < n / 2) :
    choose n r ≤ choose n (r + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt (h.trans_le (n.div_le_self 2)))
  rw [← choose_succ_right_eq]
  apply Nat.mul_le_mul_left
  rw [← Nat.lt_iff_add_one_le, Nat.lt_sub_iff_add_lt, ← Nat.mul_two]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h Nat.zero_lt_two) (n.div_mul_le_self 2)

/-- Show that for small values of the right argument, the middle value is largest. -/
private theorem choose_le_middle_of_le_half_left {n r : ℕ} (hr : r ≤ n / 2) :
    choose n r ≤ choose n (n / 2) := by
  induction hr using decreasingInduction with
  | self => rfl
  | of_succ k hk ih => exact (choose_le_succ_of_lt_half_left hk).trans ih

/-- `choose n r` is maximised when `r` is `n/2`. -/
theorem choose_le_middle (r n : ℕ) : choose n r ≤ choose n (n / 2) := by
  rcases le_or_gt r n with b | b
  · rcases le_or_gt r (n / 2) with a | h
    · apply choose_le_middle_of_le_half_left a
    · rw [← choose_symm b]
      apply choose_le_middle_of_le_half_left
      cutsat
  · rw [choose_eq_zero_of_lt b]
    apply zero_le

/-! #### Inequalities about increasing the first argument -/


theorem choose_le_succ (a c : ℕ) : choose a c ≤ choose a.succ c := by
  cases c <;> simp [Nat.choose_succ_succ]

theorem choose_le_add (a b c : ℕ) : choose a c ≤ choose (a + b) c := by
  induction b with
  | zero => simp
  | succ b_n b_ih => exact b_ih.trans (choose_le_succ (a + b_n) c)

theorem choose_le_choose {a b : ℕ} (c : ℕ) (h : a ≤ b) : choose a c ≤ choose b c :=
  Nat.add_sub_cancel' h ▸ choose_le_add a (b - a) c

theorem choose_mono (b : ℕ) : Monotone fun a => choose a b := fun _ _ => choose_le_choose b

theorem choose_eq_one_iff {n k : ℕ} : n.choose k = 1 ↔ k = 0 ∨ n = k := by
  constructor <;> intro h
  · rcases lt_trichotomy k n with hk | rfl | hk
    · rw [← add_one_le_iff] at hk
      have := choose_mono k hk
      simp_rw [choose_succ_self_right, h] at this; omega
    · tauto
    · simp [choose_eq_zero_of_lt hk] at h
  · rcases h with rfl | rfl <;> simp

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

/--
`multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`. -/
def multichoose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 =>
    multichoose n (k + 1) + multichoose (n + 1) k

@[simp]
theorem multichoose_zero_right (n : ℕ) : multichoose n 0 = 1 := by cases n <;> simp [multichoose]

@[simp]
theorem multichoose_zero_succ (k : ℕ) : multichoose 0 (k + 1) = 0 := by simp [multichoose]

theorem multichoose_succ_succ (n k : ℕ) :
    multichoose (n + 1) (k + 1) = multichoose n (k + 1) + multichoose (n + 1) k := by
  simp [multichoose]

@[simp]
theorem multichoose_one (k : ℕ) : multichoose 1 k = 1 := by
  induction k with
  | zero => simp
  | succ k IH => simp [multichoose_succ_succ 0 k, IH]

@[simp]
theorem multichoose_two (k : ℕ) : multichoose 2 k = k + 1 := by
  induction k with
  | zero => simp
  | succ k IH => rw [multichoose, IH]; simp [Nat.add_comm]

@[simp]
theorem multichoose_one_right (n : ℕ) : multichoose n 1 = n := by
  induction n with
  | zero => simp
  | succ n IH => simp [multichoose_succ_succ n 0, IH]

theorem multichoose_eq : ∀ n k : ℕ, multichoose n k = (n + k - 1).choose k
  | _, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    have : n + (k + 1) < (n + 1) + (k + 1) := Nat.add_lt_add_right (Nat.lt_succ_self _) _
    have : (n + 1) + k < (n + 1) + (k + 1) := Nat.add_lt_add_left (Nat.lt_succ_self _) _
    rw [multichoose_succ_succ, Nat.add_comm, Nat.succ_add_sub_one, ← Nat.add_assoc,
      Nat.choose_succ_succ]
    simp [multichoose_eq n (k + 1), multichoose_eq (n + 1) k]

end Nat
