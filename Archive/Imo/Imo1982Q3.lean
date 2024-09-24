/-
Copyright (c) 2024 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Data.Matrix.Basic



/-!
# IMO 1982 Q3

Consider infinite sequences $\{x_n \}$ of positive reals such that $x_0 = 0$ and
$x_0 \geq x_1 \geq x_2 \geq ...$

a) Prove that for every such sequence there is an $n \geq 1$ such that:

$\frac{x_0^2}{x_1} + \ldots + \frac{x_{n-1}^2}{x_n} \geq 3.999$

b) Find such a sequence such that for all n:

$\frac{x_0^2}{x_1} + \ldots + \frac{x_{n-1}^2}{x_n} < 4$

The solution is based on the one at the
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1982_IMO_Problems/Problem_3)
website.
-/

open Real BigOperators Finset RealInnerProductSpace Matrix

namespace Imo1982Q3

variable {ι : Type*} [Fintype ι]

lemma sum_Fin_eq_sum_Ico {x : ℕ → ℝ} {N : ℕ} : ∑ n : Fin N, x n = ∑ n ∈ Ico 0 N, x n := by
  rw [Fin.sum_univ_eq_sum_range, Nat.Ico_zero_eq_range]

/-
Specialization of Cauchy-Schwarz inequality with the sequences x n / √(y n) and √(y n)
-/
lemma Sedrakyan's_lemma {x y: EuclideanSpace ℝ ι}
    (hN : 0 < Fintype.card ι) (xi_pos : ∀ i, 0 < x i) (yi_pos : ∀ i, 0 < y i) :
  (∑ n :ι, x n)^2 / (∑ n :ι, y n) ≤ (∑ n :ι, ((x n)^2 / (y n))) := by
  let nonneg : ∀ f :ι → ℝ, (∀ i, 0 < f i) → ∀ i, 0 ≤ f i :=
    fun f h i => (lt_iff_le_and_ne.mp (h i)).left
  have xi_nonneg : ∀ i, 0 ≤ x i := nonneg x xi_pos
  have yi_nonneg : ∀ i, 0 ≤ y i := fun i => le_of_lt (yi_pos _)
  have sqrt_yi_pos : ∀ i, 0 < √(y i) := fun i => (Real.sqrt_pos_of_pos (yi_pos i))
  have sum_yi_pos : 0 < (∑ n :ι, y n) := by
    apply Finset.sum_pos (fun i _hi => yi_pos i)
    rw [← Finset.card_pos]
    apply hN
  rw [div_le_iff₀' sum_yi_pos]
  convert_to
    (∑ n :ι, √(y n) * (x n / √(y n))) ^ 2
    ≤
    (∑ n :ι, y n) * ∑ n :ι, x n ^ 2 / y n using 3
  rw [mul_div_cancel₀ (hb := sqrt_ne_zero'.mpr (yi_pos _))]
  have RHS_nonneg : 0 ≤ (∑ n :ι, y n) * (∑ n :ι, x n ^ 2 / y n):= by
    rw [mul_nonneg_iff_of_pos_left]
    apply Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (yi_nonneg i))
    apply sum_yi_pos
  have LHS_nonneg : 0 ≤ ∑ n :ι, √(y n) * (x n / √(y n)) := by
    apply Finset.sum_nonneg
    intro i _hi
    apply mul_nonneg (le_of_lt (sqrt_yi_pos i))
    apply div_nonneg (xi_nonneg _) (le_of_lt (sqrt_yi_pos _))
  rw [← Real.le_sqrt LHS_nonneg RHS_nonneg, sqrt_mul (le_of_lt sum_yi_pos)]
  convert_to
    (∑ n :ι, √(y n) * (x n / √(y n)))
    ≤
    √(∑ n :ι, √(y n) ^ 2) * √(∑ n :ι, (x n / √(y n)) ^ 2) using 4
  · rw [sq_sqrt (yi_nonneg _)]
  · rw [div_pow, sq_sqrt (yi_nonneg _)]
  convert_to
    (∑ n :ι, √(y n) * (x n / √(y n)))
    ≤
    √(∑ n :ι, ‖√(y n)‖ ^ 2) * √(∑ n :ι, ‖x n / √(y n)‖  ^ 2) using 4
  · rw [norm_eq_abs, abs_of_pos (sqrt_yi_pos _) ]
  · rw [norm_eq_abs, abs_of_pos]; apply div_pos (xi_pos _) (sqrt_yi_pos _)
  let sqrt_y : EuclideanSpace ℝ ι := fun n => √(y n)
  let x_div_sqrt_y : EuclideanSpace ℝ ι := fun n => x n / √(y n)
  convert_to (∑ n : ι, √(y n) * (x n / √(y n))) ≤ ‖sqrt_y‖ * ‖x_div_sqrt_y‖ using 3
  · rw [EuclideanSpace.norm_eq (x := sqrt_y)]
  · rw [EuclideanSpace.norm_eq (x := x_div_sqrt_y)]
  convert_to (dotProduct sqrt_y x_div_sqrt_y) ≤ ‖sqrt_y‖ * ‖x_div_sqrt_y‖ using 1
  convert_to (dotProduct (star sqrt_y) x_div_sqrt_y) ≤ ‖sqrt_y‖ * ‖x_div_sqrt_y‖ using 1
  convert_to ⟪sqrt_y, x_div_sqrt_y⟫_ℝ ≤  ‖sqrt_y‖ * ‖x_div_sqrt_y‖ using 2
  apply real_inner_le_norm

lemma ineq₁ {x : ℕ → ℝ} {N : ℕ} (hN : 1 < N) (hx : ∀ i , x (i + 1) ≤ x i) :
    x N ≤ (∑ n : Fin (N - 1), x (n + 1)) / (N - 1) := by
  have h : ∀ m n : ℕ, n ≤ m → x m ≤ x n := by
    intro m n mlen
    induction' m, mlen using Nat.le_induction with k _nlek xk_le_xn
    · exact le_refl (x n)
    · calc
      x (k + 1) ≤ x k := hx k
      _         ≤ x n := xk_le_xn
  rw [le_div_iff₀ (by aesop)]
  calc
  x N * (↑N - 1) = ((N - 1) : ℕ) * x N := by
    rw [mul_comm, Nat.cast_sub, Nat.cast_one]; linarith
  _ = ↑(range (N - 1)).card * x N := by rw [card_range]
  _ = ∑ _ ∈ range (N - 1), x N := by
    simp only [univ_eq_attach, sum_const, card_attach, Nat.card_Ioc, nsmul_eq_mul]
  _ ≤ ∑ n ∈ range (N - 1), x (n + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [mem_range, Nat.lt_sub_iff_add_lt (a := i) (b := 1) (c := N)] at hi
    apply h
    apply le_of_lt hi
  _ = ∑ n : Fin (N - 1), x (↑n + 1) := by rw [sum_range]

lemma ineq₂ {x : ℕ → ℝ} {N : ℕ}
    (hN : 1 < N) (hx : ∀ i , x (i + 1) ≤ x i) (x_pos : ∀ i, x i > (0 : ℝ)) :
  (N - 1) / N * (1 / ∑ n : Fin (N - 1), x (n + 1)) ≤ 1 / (∑ n : Fin N, x (n + 1)) := by
  have ne_zero : N - 1 ≠ 0 := by
    intro h
    rw [Nat.sub_eq_iff_eq_add (le_of_lt hN), zero_add] at h
    rw [h] at hN; apply lt_irrefl _ hN
  have ne_zero' : (N : ℝ) - 1 ≠ 0 :=  by
    rw [ne_eq]; intro h
    rw [sub_eq_iff_eq_add, zero_add] at h
    rw [@Nat.cast_eq_one] at h
    rw [h] at hN; apply lt_irrefl _ hN
  have sum_range_pos : 0 < ∑ i ∈ range (N - 1), x (i + 1) := by
    apply Finset.sum_pos
    intro i _hi
    apply x_pos _
    simp [ne_zero]
  have mul_sum_pos : 0 < ∑ i ∈ range (N - 1), x (i + 1) * ↑N / (↑N - 1) := by
    apply Finset.sum_pos
    intro i _hi
    apply div_pos
    apply mul_pos
    apply x_pos
    simp only [Nat.cast_pos]
    linarith
    rw [lt_sub_iff_add_lt, zero_add, Nat.one_lt_cast]
    apply hN
    rw [@nonempty_range_iff]
    exact ne_zero
  have sum_fin_pos : 0 < ∑ n : Fin N, x (↑n + 1) := by
    apply Finset.sum_pos; intro i _hi
    apply x_pos (i +1)
    rw [@univ_nonempty_iff, ← @Fin.pos_iff_nonempty]
    linarith
  convert_to
    (N - 1) / N * (1 / ∑ n in range (N - 1), x (n + 1)) ≤ 1 / (∑ n : Fin N, x (n + 1)) using 3
  rw [sum_range]
  convert_to 1 / (N * (∑ n in range (N - 1), x (n + 1)) / (N - 1)) ≤ 1 / (∑ n : Fin N, x (n + 1))
  field_simp
  convert_to 1 / ∑ i ∈ range (N - 1), x (i + 1) * ↑N / (↑N - 1) ≤ 1 / (∑ n : Fin N, x (n + 1))
  rw [mul_comm, sum_mul, sum_div]
  rw [div_le_div_iff (mul_sum_pos) (sum_fin_pos), one_mul, one_mul, ]
  calc ∑ n : Fin N, x (↑n + 1) = ∑ n in range N, x (n + 1) := by rw [sum_range]
  _ = ∑ n in range (N - 1 + 1), x (n + 1) := by
    rw [Nat.sub_one_add_one_eq_of_pos (by linarith [hN])]
  _ = ∑ n in range (N - 1), x (n + 1) + x N := by
    rw [sum_range_succ, Nat.sub_one_add_one_eq_of_pos (by linarith [hN])]
  _ ≤ ∑ n in range (N - 1), x (n + 1) + (∑ n ∈ range (N - 1), x (n + 1)) / (↑N - 1) := by
    apply add_le_add_left; rw [@sum_range]; apply ineq₁ hN hx;
  _ = ∑ n in range (N - 1), x (n + 1) + (∑ n ∈ range (N - 1), x (n + 1) / (↑N - 1)) :=  by
    rw [sum_div]
  _ = ∑ n in range (N - 1), (x (n + 1) + x (n + 1) / (↑N - 1)) := by rw [Finset.sum_add_distrib]
  _ = ∑ n in range (N - 1),  N * x (n + 1) / (↑N - 1) := by
    apply Finset.sum_congr (by rfl)
    intro n _hn
    nth_rewrite 1 [
      ← one_mul (x (n + 1)),
      ← div_self (a := (N - 1 : ℝ)) (ne_zero'),
      mul_comm,
      mul_div,
      div_add_div_same
      ]
    nth_rewrite 2 [← mul_one (x (n + 1))]
    rw [← mul_add, mul_comm]
    simp only [sub_add_cancel]
  _ = ∑ i ∈ range (N - 1), x (i + 1) * ↑N / (↑N - 1) := by
    apply Finset.sum_congr (by rfl); intro n _hn; rw [mul_comm]


lemma ineq₃ {x : ℕ → ℝ} {N : ℕ } (hN : 1 < N) (x_pos : ∀ i, x i > (0 : ℝ)) :
    2 * (∑ n : Fin N, x (n + 1)) ≤ 1 + (∑ n : Fin N, x (n + 1))^2 := by
  have sum_fin_pos : 0 < ∑ n : Fin N, x (↑n + 1) := by
    apply Finset.sum_pos
    intro i _hi
    apply x_pos (i +1)
    rw [@univ_nonempty_iff, ← @Fin.pos_iff_nonempty]
    linarith
  calc
  2 * (∑ n : Fin N, x (n + 1)) = 2 * (1^(1/2 : ℝ) * ((∑ n : Fin N, x (n  + 1))^2)^(1/2 : ℝ)) := by
    rw [one_rpow, one_mul, ← Real.sqrt_eq_rpow, sqrt_sq _]
    apply le_of_lt sum_fin_pos
  _ ≤ 2 * ((1/2 : ℝ) * 1 + (1/2 : ℝ) * (∑ n : Fin N, x (n  + 1))^2) := by
    rw [mul_le_mul_left (by norm_num)]
    apply Real.geom_mean_le_arith_mean2_weighted
      (by norm_num) (by norm_num) (by norm_num) (sq_nonneg _) (by norm_num)
  _ ≤ 1 + (∑ n : Fin N, x (n  + 1))^2 := by field_simp
lemma Ico_sdiff_zero_eq_Ico {N : ℕ} : Ico 0 N \ {0} = Ico 1 N := by
  rw [sdiff_singleton_eq_erase, Ico_erase_left, Nat.Ico_succ_left]


lemma eq₀ {x : ℕ → ℝ} {N : ℕ} (hN : 1 < N) (hx₀ : x 0 = (1 : ℝ)) :
    (∑ n : Fin N, (x n))^2
    = 1 + 2 * (∑ n : Fin (N - 1), x (n + 1)) + (∑ n : Fin (N - 1), x (n + 1))^2 := by
  have zero_lt_N : 0  < N := by linarith
  have two_le_N : 2 ≤ N := by linarith
  have : ∀ N, 2 ≤ N → ∑ n : Fin (N - 1), x (↑n + 1) = (∑ n ∈ Ico 1 N, x n) := by
    intro N hN
    let f : ℕ → ℝ := (fun n => x (n + 1))
    induction' N, hN using Nat.le_induction with d two_le_d hd
    case base => simp
    case succ =>
      have one_le_d : 1 ≤ d := by exact Nat.one_le_of_lt two_le_d
      rw [
        ← sum_range (n := d + 1 - 1) (f := f),
        Nat.sub_add_comm (one_le_d),
        sum_range_succ, sum_range, hd, sum_Ico_succ_top one_le_d]
      simp only [add_right_inj, f]
      congr
      rw [
        ← Nat.sub_add_comm one_le_d,
        Nat.add_sub_assoc (le_refl _),
        tsub_eq_zero_of_le (le_refl _),
        add_zero
      ]
  rw [
    sum_Fin_eq_sum_Ico, Finset.sum_eq_sum_diff_singleton_add (i := 0) (by simp [zero_lt_N]),
    Ico_sdiff_zero_eq_Ico, pow_two, hx₀
    ]
  ring_nf
  rw [this _ two_le_N]; ring


theorem Imo1982Q3_part_a {x : ℕ → ℝ} (x_pos : ∀ i, x i > (0 : ℝ)) (hx₀ : x 0 = (1 : ℝ))
    (hx : ∀ i , x (i + 1) ≤ x i) : ∃ N : ℕ, 3.999 ≤ ∑ n : Fin N, (x n)^2 / x (n + 1) := by
  have div_prev_pos : ∀ N > 1, 0 < (↑N - 1) / (N : ℝ) :=  by
    intro N hN
    apply div_pos
    linarith; linarith
  have sum_xi_pos : ∀ N > 0, 0 < (∑ n : Fin N, x n) := by
    intro N hN
    apply Finset.sum_pos
    intro i _hi
    apply x_pos i
    rw [← Finset.card_pos, card_fin]
    apply hN
  have sum_xi_pos' : ∀ N > 1, 0 < (∑ n : Fin (N - 1), x (n + 1)) := by
    intro N hN
    apply Finset.sum_pos
    intro i _hi
    apply x_pos _
    rw [← Finset.card_pos, card_fin, Nat.lt_sub_iff_add_lt, zero_add]
    apply hN
  have sedrakayan's_lemma :
    ∀ N > 0,
    ((∑ n : Fin N, (x n))^2 / (∑ n : Fin N, x (n + 1))) ≤ (∑ n : Fin N, (x n)^2 / x (n + 1)) :=
    fun N hN => Sedrakyan's_lemma (by simpa) (fun i => x_pos i) (fun i => x_pos (i + 1))
  have :
    ∃ (N : ℕ), 0 < N ∧ 1 < N ∧ 2 < N ∧  (3.999 : ℝ) ≤ 4 * ((N - 1) / N) :=  by use 4000; norm_num
  obtain ⟨N, zero_lt_N, one_lt_N, two_lt_N, ineq₀⟩ := this
  use N
  calc (3.999 : ℝ) ≤ 4 * ((N - 1) / N) := ineq₀
  _ = (2 + 2) * ((N - 1) / N) := by norm_num
  _ = ((2 * (∑ n : Fin (N - 1), x (n + 1))
    + 2 * (∑ n : Fin (N - 1), x (n + 1))) / (∑ n : Fin (N - 1), x (n + 1))) * ((N - 1) / (N)) := by
    rw [← div_add_div_same, ← mul_div, div_self, mul_one]
    symm
    apply (lt_iff_le_and_ne.mp (sum_xi_pos' _ one_lt_N)).right
  _ ≤ (1 + (∑ n : Fin (N - 1), x (n + 1))^2
    + 2 * (∑ n : Fin (N - 1), x (n + 1))) / (∑ n : Fin (N - 1), x (n + 1)) * ((N - 1) / (N)) := by
    rw [mul_le_mul_right (by apply div_prev_pos N; simp [one_lt_N])]
    apply div_le_div
    apply add_nonneg
    apply add_nonneg (by norm_num) (sq_nonneg _)
    apply mul_nonneg (by norm_num)
    apply (lt_iff_le_and_ne.mp (sum_xi_pos' _ one_lt_N)).left
    apply add_le_add_right
    apply ineq₃ _ x_pos
    rw [Nat.lt_sub_iff_add_lt, one_add_one_eq_two]
    apply two_lt_N
    apply sum_xi_pos' _ one_lt_N
    apply le_refl
  _ = ((∑ n : Fin N, (x n))^2 / (∑ n : Fin (N - 1), x (n + 1))) * ((N - 1) / (N)) := by
    rw [
      eq₀ one_lt_N hx₀,
      add_assoc,
      add_comm ((∑ n : Fin (N - 1), x (↑n + 1)) ^ 2),
      ← add_assoc
      ]
  _ = ((∑ n : Fin N, (x n))^2) * ((N - 1) / (N)) * (1 / (∑ n : Fin (N - 1), x (n + 1))) := by
    rw [← mul_one (((∑ n : Fin N, x ↑n) ^ 2)), mul_div]
    ring
  _ ≤ ((∑ n : Fin N, (x n))^2 / (∑ n : Fin N, x (n + 1))) := by
    nth_rewrite 2 [← mul_one (((∑ n : Fin N, x ↑n) ^ 2))]
    rw [← mul_div _ 1, mul_assoc, mul_le_mul_left]
    apply ineq₂ one_lt_N hx x_pos
    apply sq_pos_of_pos (sum_xi_pos _ zero_lt_N)
  _ ≤ ∑ n : Fin N, (x ↑n) ^ 2 / x (↑n + 1) := by
    apply sedrakayan's_lemma
    apply zero_lt_N


theorem Imo1982Q3_part_b :  ∃ x : ℕ → ℝ, (∀ i, x i > 0) ∧ (∀ i, x (i + 1) ≤ x i) ∧ (x 0 = 1)
    ∧ (∀ N, (∑ n ∈ range (N + 1), ((x n)^2 / (x (n + 1)))) < 4) := by
  let xₙ : ℕ → ℝ := fun n => (1/2)^n
  use xₙ
  constructor
  · intro i
    apply pow_pos (by norm_num) i
  constructor
  · intro i
    apply pow_le_pow_of_le_one (by norm_num)
    · rw [one_div_le (by norm_num) (by norm_num), div_one]; norm_num
    · apply Nat.le_succ
  constructor
  · rfl
  intro N
  dsimp [xₙ]
  rw [
    Finset.sum_eq_sum_diff_singleton_add
      (s := range (N + 1)) (i := 0) (Finset.mem_range.mpr (by linarith)),
    pow_zero, zero_add, one_pow, pow_one, one_div_one_div, add_comm
    ]
  convert_to (2 + ∑ n ∈ range (N), (1/2) ^ n : ℝ) < 4 using 2
  induction' N with k hk
  case zero =>
    simp only [
      zero_add, range_one, sdiff_self, bot_eq_empty, one_div, inv_pow, div_inv_eq_mul,
      sum_empty, range_zero
      ]
  case succ =>
    rw [
      Finset.sum_range_succ, ← hk, Finset.range_add_one
      ]
    simp only [
      one_div, inv_pow, div_inv_eq_mul, singleton_subset_iff, mem_insert, self_eq_add_left,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, mem_range, lt_add_iff_pos_left,
      add_pos_iff, zero_lt_one, or_true, sum_sdiff_eq_sub, lt_self_iff_false, not_false_eq_true,
      sum_insert, sum_singleton, pow_zero, one_pow, inv_one, zero_add, pow_one, one_mul
      ]
    rw [
      ← pow_mul, mul_comm, ← inv_pow
      ]
    nth_rewrite 1 [← inv_inv 2]
    rw [
      mul_comm, inv_pow 2⁻¹, ← pow_sub₀ (a := 2⁻¹) (ha := by norm_num) (h := by linarith), add_mul,
      one_mul, add_assoc, one_add_one_eq_two, mul_comm k 2, two_mul, add_assoc,
      Nat.add_sub_assoc (by linarith), Nat.sub_self, add_zero, inv_pow, add_sub_assoc, add_comm
    ]
  rw [
    geom_sum_eq (by norm_num), half_sub, div_neg, div_eq_inv_mul, one_div, inv_inv,
    mul_comm, ← neg_mul, neg_sub
    ]
  have h₁: (0 < (2 : ℝ)⁻¹ ^ N) := by positivity
  linarith [h₁]

end Imo1982Q3
