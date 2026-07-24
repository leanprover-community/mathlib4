/-
Copyright (c) 2026 Ravi Bajaj and Ben Burns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Bajaj, Ben Burns
-/
module

public import Mathlib.NumberTheory.ShuniaIntegerRoot.Estimates
public import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Choose.Sum

/-!
# Shunia's integer-root formula

This file proves Conjecture 6.1 from:

* J. M. Shunia, *Polynomial quotient rings and Kronecker substitution for deriving
  combinatorial identities*, arXiv:2404.00332.

The conjecture gives a fixed-length expression for `Nat.nthRoot n a` in terms of two modular
exponentiations.  Its proof uses the coefficients of `(1 + T) ^ k` reduced by the relation
`T ^ n = a`.  A roots-of-unity filter shows that adjacent leading coefficients have ratio very
close to the positive real `n`-th root of `a`; evaluation at the large base `a ^ (2 * a * n)`
then recovers that ratio from the two modular residues.
-/

@[expose] public section

open scoped BigOperators

namespace ShuniaIntegerRoot

/-- The coefficient of `T ^ i` in `(1 + T) ^ k`, reduced using `T ^ n = a`. -/
private def coeff (a n k i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1) with j % n = i, k.choose j * a ^ (j / n)

/-- Evaluation at `x` of `(1 + T) ^ k` reduced using `T ^ n = a`. -/
private def reducedEval (a n k x : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, coeff a n k i * x ^ i

private lemma coeff_pos_of_lt_of_le {a n k i : ℕ} (hin : i < n) (hik : i ≤ k) :
    0 < coeff a n k i := by
  unfold coeff
  apply Finset.sum_pos'
  · exact fun _ _ ↦ Nat.zero_le _
  · refine ⟨i, ?_, ?_⟩
    · simp [hik, Nat.mod_eq_of_lt hin]
    · simpa [Nat.div_eq_of_lt hin] using Nat.choose_pos hik

private lemma reducedEval_eq_sum_mod (a n k x : ℕ) (hn : 0 < n) :
    reducedEval a n k x =
      ∑ j ∈ Finset.range (k + 1), k.choose j * a ^ (j / n) * x ^ (j % n) := by
  classical
  simp only [reducedEval, coeff, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Nat.mod_lt j hn, mul_assoc]

private lemma sum_coeff_eq (a n k : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, coeff a n k i) =
      ∑ j ∈ Finset.range (k + 1), k.choose j * a ^ (j / n) := by
  simpa [reducedEval] using reducedEval_eq_sum_mod a n k 1 hn

private lemma reducedEval_le_top_pow_mul_sum {a n k x : ℕ} (hn : 0 < n) (hx : 0 < x) :
    reducedEval a n k x ≤
      x ^ (n - 1) * ∑ i ∈ Finset.range n, coeff a n k i := by
  unfold reducedEval
  calc
    (∑ i ∈ Finset.range n, coeff a n k i * x ^ i) ≤
        ∑ i ∈ Finset.range n, coeff a n k i * x ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right hx (by
        have := Finset.mem_range.mp hi
        omega)
    _ = x ^ (n - 1) * ∑ i ∈ Finset.range n, coeff a n k i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _

private def lowerEval (c : ℕ → ℕ) (n x : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n - 1), c i * x ^ i

private lemma lowerEval_cast_le
    {a n x : ℕ} {α : ℝ} {c : ℕ → ℕ}
    (hn : 1 < n) (hx : 0 < x) (hα : 1 ≤ α) (hαpow : α ^ n = a)
    (hC : 0 < c (n - 1))
    (hrel : ∀ i < n - 1,
      (c i : ℝ) / (c (n - 1) : ℝ) < 2 * α ^ (n - 1 - i)) :
    (lowerEval c n x : ℝ) ≤ 2 * n * a * c (n - 1) * x ^ (n - 2) := by
  have hC' : (0 : ℝ) < c (n - 1) := by exact_mod_cast hC
  rw [lowerEval]
  push_cast
  calc
    (∑ i ∈ Finset.range (n - 1), (c i : ℝ) * (x : ℝ) ^ i) ≤
        ∑ _i ∈ Finset.range (n - 1),
          (2 * (a : ℝ) * c (n - 1) * (x : ℝ) ^ (n - 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hci : (c i : ℝ) ≤ 2 * α ^ (n - 1 - i) * c (n - 1) :=
        ((div_lt_iff₀ hC').mp (hrel i hi')).le
      have hαi : α ^ (n - 1 - i) ≤ (a : ℝ) := by
        calc
          α ^ (n - 1 - i) ≤ α ^ n := pow_le_pow_right₀ hα (by omega)
          _ = a := hαpow
      have hxi : (x : ℝ) ^ i ≤ (x : ℝ) ^ (n - 2) :=
        pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ x by omega)) (by omega)
      calc
        (c i : ℝ) * x ^ i ≤ (2 * α ^ (n - 1 - i) * c (n - 1)) * x ^ i := by
          gcongr
        _ ≤ (2 * (a : ℝ) * c (n - 1)) * x ^ (n - 2) := by gcongr
    _ = (n - 1 : ℕ) * (2 * (a : ℝ) * c (n - 1) * x ^ (n - 2)) := by simp
    _ ≤ n * (2 * (a : ℝ) * c (n - 1) * x ^ (n - 2)) := by gcongr; omega
    _ = 2 * n * a * c (n - 1) * x ^ (n - 2) := by ring

private lemma lowerEval_error_le
    {a n x : ℕ} {α : ℝ} {c : ℕ → ℕ}
    (hn : 1 < n) (hx : 0 < x) (hα : 1 ≤ α) (hαpow : α ^ n = a)
    (hC : 0 < c (n - 1))
    (hrel : ∀ i < n - 1,
      (c i : ℝ) / (c (n - 1) : ℝ) < 2 * α ^ (n - 1 - i)) :
    (lowerEval c n x : ℝ) / ((c (n - 1) : ℝ) * x ^ (n - 1)) ≤ 2 * n * a / x := by
  have hC' : (0 : ℝ) < c (n - 1) := by exact_mod_cast hC
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  rw [div_le_iff₀ (mul_pos hC' (pow_pos hx' _))]
  calc
    (lowerEval c n x : ℝ) ≤ 2 * n * a * c (n - 1) * x ^ (n - 2) :=
      lowerEval_cast_le hn hx hα hαpow hC hrel
    _ = (2 * n * a / x) * ((c (n - 1) : ℝ) * x ^ (n - 1)) := by
      rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
      field_simp

private lemma ratio_leading_error
    {U C Y L L' B Q : ℝ}
    (hU : 0 < U) (hC : 0 < C) (hY : 0 < Y)
    (hL : 0 ≤ L) (hL' : 0 ≤ L') (hB : 0 ≤ B)
    (heD : L / (U * Y) ≤ B) (heN : L' / (C * Y) ≤ B)
    (hCU : C / U ≤ Q) :
    |(C * Y + L') / (U * Y + L) - C / U| ≤ Q * B := by
  let eD := L / (U * Y)
  let eN := L' / (C * Y)
  have heD0 : 0 ≤ eD := div_nonneg hL (mul_pos hU hY).le
  have heN0 : 0 ≤ eN := div_nonneg hL' (mul_pos hC hY).le
  have heDB : eD ≤ B := heD
  have heNB : eN ≤ B := heN
  have hden : 0 < 1 + eD := by linarith
  have hDY : U * Y + L = U * Y * (1 + eD) := by
    dsimp [eD]
    field_simp
  have hNY : C * Y + L' = C * Y * (1 + eN) := by
    dsimp [eN]
    field_simp
  have hratio :
      (C * Y + L') / (U * Y + L) - C / U =
        (C / U) * ((eN - eD) / (1 + eD)) := by
    rw [hDY, hNY]
    field_simp [ne_of_gt hU, ne_of_gt hC, ne_of_gt hY, ne_of_gt hden]
    ring
  have hdiff : |eN - eD| ≤ B := by rw [abs_le]; constructor <;> linarith
  have hfrac : |(eN - eD) / (1 + eD)| ≤ B := by
    rw [abs_div, abs_of_pos hden]
    exact (div_le_div_of_nonneg_right hdiff hden.le).trans
      (div_le_self hB (by linarith))
  rw [hratio, abs_mul, abs_of_pos (div_pos hC hU)]
  exact (mul_le_mul_of_nonneg_left hfrac (div_pos hC hU).le).trans
    (mul_le_mul_of_nonneg_right hCU hB)

private lemma sixteen_mul_sq_mul_pow_four_lt_pow
    {a n K : ℕ} (ha : 4 ≤ a) (hna : n ≤ a) (hK : 16 ≤ K) :
    16 * n ^ 2 * a ^ 4 < a ^ K := by
  have ha0 : 0 < a := by omega
  have hpoly : 16 * n ^ 2 * a ^ 4 ≤ 16 * a ^ 6 := by
    calc
      16 * n ^ 2 * a ^ 4 ≤ 16 * a ^ 2 * a ^ 4 := by
        gcongr
      _ = 16 * a ^ 6 := by ring
  have hp10 : 16 < a ^ 10 :=
    (by norm_num : 16 < 4 ^ 10).trans_le (Nat.pow_le_pow_left ha 10)
  have hp16 : 16 * a ^ 6 < a ^ 16 := by
    calc
      16 * a ^ 6 < a ^ 10 * a ^ 6 := Nat.mul_lt_mul_of_pos_right hp10 (pow_pos ha0 _)
      _ = a ^ 16 := by ring
  exact hpoly.trans_lt <| hp16.trans_le (Nat.pow_le_pow_right ha0 hK)

private lemma leading_recovery_of_decomposition
    {a n x : ℕ} {α : ℝ} {c d : ℕ → ℕ}
    (ha : 4 ≤ a) (hn : 1 < n) (hna : n ≤ a)
    (hα : 1 < α) (hαpow : α ^ n = a)
    (hU : 0 < c (n - 1)) (hC : 0 < d (n - 1))
    (hrelc : ∀ i < n - 1,
      (c i : ℝ) / (c (n - 1) : ℝ) < 2 * α ^ (n - 1 - i))
    (hreld : ∀ i < n - 1,
      (d i : ℝ) / (d (n - 1) : ℝ) < 2 * α ^ (n - 1 - i))
    (hCU : (d (n - 1) : ℝ) / c (n - 1) < 2 * a)
    (hx : x = a ^ (2 * a * n)) :
    |((d (n - 1) * x ^ (n - 1) + lowerEval d n x : ℕ) : ℝ) /
          ((c (n - 1) * x ^ (n - 1) + lowerEval c n x : ℕ) : ℝ) -
        (d (n - 1) : ℝ) / c (n - 1)| < α / (4 * n * a ^ 2) := by
  have hx0 : 0 < x := by simp [hx, show 0 < a by omega]
  have hxbigNat : 16 * n ^ 2 * a ^ 4 < x := by
    rw [hx]
    exact sixteen_mul_sq_mul_pow_four_lt_pow ha hna (by nlinarith)
  have hxbig : (16 : ℝ) * n ^ 2 * a ^ 4 < x := by exact_mod_cast hxbigNat
  have hec := lowerEval_error_le hn hx0 hα.le hαpow hU hrelc
  have hed := lowerEval_error_le hn hx0 hα.le hαpow hC hreld
  have hratio := ratio_leading_error
    (U := (c (n - 1) : ℝ)) (C := (d (n - 1) : ℝ)) (Y := (x : ℝ) ^ (n - 1))
    (L := (lowerEval c n x : ℝ)) (L' := (lowerEval d n x : ℝ))
    (B := 2 * n * a / x) (Q := 2 * a)
    (by exact_mod_cast hU) (by exact_mod_cast hC) (by positivity)
    (by positivity) (by positivity) (by positivity) hec hed hCU.le
  push_cast at hratio ⊢
  have hcoarse : (2 * (a : ℝ)) * (2 * n * a / x) < α / (4 * n * a ^ 2) := by
    have hxR : (0 : ℝ) < x := by positivity
    rw [show (2 * (a : ℝ)) * (2 * n * a / x) = (4 * n * a ^ 2) / x by ring,
      div_lt_div_iff₀ hxR (by positivity)]
    have : (16 : ℝ) * n ^ 2 * a ^ 4 < α * x :=
      hxbig.trans_le (by nlinarith)
    nlinarith
  exact hratio.trans_lt hcoarse

private theorem eval_ratio_close_leading_ratio
    {a n : ℕ} {α : ℝ} (c d : ℕ → ℕ)
    (ha : 4 ≤ a) (hn : 1 < n) (hna : n ≤ a)
    (hα : 1 < α) (hαpow : α ^ n = a)
    (hU : 0 < c (n - 1)) (hC : 0 < d (n - 1))
    (hrelc : ∀ i < n - 1,
      (c i : ℝ) / (c (n - 1) : ℝ) < 2 * α ^ (n - 1 - i))
    (hreld : ∀ i < n - 1,
      (d i : ℝ) / (d (n - 1) : ℝ) < 2 * α ^ (n - 1 - i))
    (hCU : (d (n - 1) : ℝ) / c (n - 1) < 2 * a) :
    let x := a ^ (2 * a * n)
    |((∑ i ∈ Finset.range n, d i * x ^ i : ℕ) : ℝ) /
          ((∑ i ∈ Finset.range n, c i * x ^ i : ℕ) : ℝ) -
        (d (n - 1) : ℝ) / c (n - 1)| < α / (4 * n * a ^ 2) := by
  dsimp only
  let x := a ^ (2 * a * n)
  change
    |((∑ i ∈ Finset.range n, d i * x ^ i : ℕ) : ℝ) /
          ((∑ i ∈ Finset.range n, c i * x ^ i : ℕ) : ℝ) -
        (d (n - 1) : ℝ) / c (n - 1)| < α / (4 * n * a ^ 2)
  have hsplit (f : ℕ → ℕ) :
      (∑ i ∈ Finset.range n, f i * x ^ i) =
        f (n - 1) * x ^ (n - 1) + lowerEval f n x := by
    rw [show n = n - 1 + 1 by omega, Finset.sum_range_succ, add_comm]
    rfl
  rw [hsplit d, hsplit c]
  exact leading_recovery_of_decomposition ha hn hna hα hαpow hU hC
    hrelc hreld hCU rfl

private lemma pow_modEq_reduced_term {a n x m j : ℕ}
    (hax : x ^ n ≡ a [MOD m]) :
    x ^ j ≡ a ^ (j / n) * x ^ (j % n) [MOD m] := by
  have hpow : (x ^ n) ^ (j / n) ≡ a ^ (j / n) [MOD m] := hax.pow _
  have hmul := hpow.mul (Nat.ModEq.refl (x ^ (j % n)))
  rw [← pow_mul, ← pow_add] at hmul
  simpa [Nat.div_add_mod j n] using hmul

private lemma add_one_pow_modEq_reducedEval {a n k x m : ℕ} (hn : 0 < n)
    (hax : x ^ n ≡ a [MOD m]) :
    (x + 1) ^ k ≡ reducedEval a n k x [MOD m] := by
  rw [add_pow, reducedEval_eq_sum_mod a n k x hn]
  apply Nat.ModEq.sum
  intro j hj
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (pow_modEq_reduced_term (j := j) hax).mul_left (k.choose j)

private lemma add_one_pow_mod_eq_reducedEval {a n k x : ℕ} (hn : 0 < n)
    (ha : a ≤ x ^ n) (hsmall : reducedEval a n k x < x ^ n - a) :
    (x + 1) ^ k % (x ^ n - a) = reducedEval a n k x := by
  exact ((Nat.mod_modEq _ _).trans
    (add_one_pow_modEq_reducedEval (k := k) hn (Nat.modEq_sub ha))).eq_of_lt_of_lt
      (Nat.mod_lt _ (Nat.zero_lt_of_lt hsmall)) hsmall

private def weight (a n i j : ℕ) : ℕ :=
  if j % n = i then a ^ (j / n) else 0

private lemma coeff_eq_sum_weight (a n k i : ℕ) :
    coeff a n k i =
      ∑ j ∈ Finset.range (k + 1), k.choose j * weight a n i j := by
  simp only [coeff, weight]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp_all

private lemma coeff_succ (a n k i : ℕ) :
    coeff a n (k + 1) i =
      coeff a n k i +
        ∑ j ∈ Finset.range (k + 1), k.choose j * weight a n i (j + 1) := by
  rw [coeff_eq_sum_weight, coeff_eq_sum_weight]
  simpa using Finset.sum_choose_succ_mul (R := ℕ) (fun j _ ↦ weight a n i j) k

private lemma weight_top_succ {a n j : ℕ} (hn : 1 < n) :
    weight a n (n - 1) (j + 1) = weight a n (n - 2) j := by
  unfold weight
  have hn0 : 0 < n := by omega
  have hmod : (j + 1) % n = n - 1 ↔ j % n = n - 2 := by
    rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt hn]
    have hjmod : j % n < n := Nat.mod_lt _ hn0
    by_cases hlt : j % n + 1 < n
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have heq : j % n + 1 = n := by omega
      rw [heq, Nat.mod_self]
      omega
  by_cases h : j % n = n - 2
  · rw [if_pos h, if_pos (hmod.mpr h)]
    congr 1
    have hlt : j % n + 1 < n := by omega
    have hdiv := Nat.add_div_eq_of_add_mod_lt
      (a := j) (b := 1) (c := n) (by simpa [Nat.mod_eq_of_lt hn] using hlt)
    simpa [Nat.div_eq_of_lt hn] using hdiv
  · rw [if_neg h, if_neg (hmod.not.mpr h)]

private lemma coeff_succ_top {a n k : ℕ} (hn : 1 < n) :
    coeff a n (k + 1) (n - 1) =
      coeff a n k (n - 1) + coeff a n k (n - 2) := by
  rw [coeff_succ, coeff_eq_sum_weight]
  congr 1
  rw [coeff_eq_sum_weight]
  apply Finset.sum_congr rfl
  intro j hj
  rw [weight_top_succ hn]

private lemma four_mul_le_two_pow {a : ℕ} (ha : 4 ≤ a) : 4 * a ≤ 2 ^ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  induction d with
  | zero => norm_num
  | succ d ih =>
      rw [show 4 + (d + 1) = (4 + d) + 1 by omega, pow_succ]
      have hpos : 1 ≤ 4 + d := by omega
      omega

/-- The positive real `n`-th root used in the spectral argument. -/
private noncomputable def root (a n : ℕ) : ℝ := (a : ℝ) ^ (n : ℝ)⁻¹

private lemma root_pos {a n : ℕ} (ha : 0 < a) : 0 < root a n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast ha) _

private lemma root_pow {a n : ℕ} (ha : 0 < a) (hn : n ≠ 0) :
    root a n ^ n = a := by
  exact Real.rpow_inv_natCast_pow (by positivity : (0 : ℝ) ≤ a) hn

private lemma weighted_stdAddChar_sum {n i j : ℕ} [NeZero n] (hi : i < n) :
    ∑ l : ZMod n,
        ZMod.stdAddChar (-((i : ZMod n) * l)) * ZMod.stdAddChar l ^ j =
      if j % n = i then (n : ℂ) else 0 := by
  calc
    _ = ∑ l : ZMod n,
        ZMod.stdAddChar (((j : ZMod n) - (i : ZMod n)) * l) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = if (j : ZMod n) - (i : ZMod n) = 0 then (n : ℂ) else 0 := by
      simpa [mul_comm, ZMod.card] using
        AddChar.sum_mulShift ((j : ZMod n) - (i : ZMod n))
          (ZMod.isPrimitive_stdAddChar n)
    _ = if j % n = i then (n : ℂ) else 0 := by
      split_ifs <;>
        simp_all [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi]

private lemma spectral_sum_eq_filtered
    (_a n k i : ℕ) (α : ℝ) [NeZero n] (hi : i < n) :
    ∑ l : ZMod n,
        ZMod.stdAddChar (-((i : ZMod n) * l)) *
          (1 + (α : ℂ) * ZMod.stdAddChar l) ^ k =
      (n : ℂ) *
        ∑ j ∈ Finset.range (k + 1) with j % n = i,
          (k.choose j : ℂ) * (α : ℂ) ^ j := by
  have hbin (z : ℂ) :
      (1 + z) ^ k = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * z ^ j := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    simp [mul_comm]
  calc
    _ = ∑ l : ZMod n,
        ZMod.stdAddChar (-((i : ZMod n) * l)) *
          ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℂ) * ((α : ℂ) * ZMod.stdAddChar l) ^ j := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hbin]
    _ = ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℂ) * (α : ℂ) ^ j) *
          ∑ l : ZMod n,
            ZMod.stdAddChar (-((i : ZMod n) * l)) * ZMod.stdAddChar l ^ j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_pow]
      ring
    _ = ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℂ) * (α : ℂ) ^ j) *
          (if j % n = i then (n : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [weighted_stdAddChar_sum hi]
    _ = _ := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring

private lemma filtered_sum_eq_coeff_mul
    (a n k i : ℕ) (α : ℝ) (hα : α ^ n = (a : ℝ)) :
    ∑ j ∈ Finset.range (k + 1) with j % n = i,
        (k.choose j : ℂ) * (α : ℂ) ^ j =
      (coeff a n k i : ℂ) * (α : ℂ) ^ i := by
  rw [coeff, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjmod : j % n = i := (Finset.mem_filter.mp hj).2
  have hjdiv : n * (j / n) + i = j := by
    rw [← hjmod, Nat.div_add_mod]
  have hαc : (α : ℂ) ^ n = (a : ℂ) := by exact_mod_cast hα
  have hpow : (α : ℂ) ^ j = (a : ℂ) ^ (j / n) * (α : ℂ) ^ i := by
    calc
      (α : ℂ) ^ j = (α : ℂ) ^ (n * (j / n) + i) := by rw [hjdiv]
      _ = ((α : ℂ) ^ n) ^ (j / n) * (α : ℂ) ^ i := by rw [pow_add, pow_mul]
      _ = _ := by rw [hαc]
  rw [hpow]
  push_cast
  ring

private lemma coeff_spectral_identity
    (a n k i : ℕ) (α : ℝ) [NeZero n] (hi : i < n)
    (hα : α ^ n = (a : ℝ)) :
    (n : ℂ) * (coeff a n k i : ℂ) * (α : ℂ) ^ i =
      ∑ l : ZMod n,
        ZMod.stdAddChar (-((i : ZMod n) * l)) *
          (1 + (α : ℂ) * ZMod.stdAddChar l) ^ k := by
  rw [spectral_sum_eq_filtered a n k i α hi, filtered_sum_eq_coeff_mul a n k i α hα]
  ring

private lemma sin_pi_div_le_sin_mul {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hrhalf : 2 * r ≤ n) :
    Real.sin (Real.pi / n) ≤ Real.sin (Real.pi * r / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have : 0 ≤ Real.pi / (n : ℝ) := by positivity
    linarith [Real.pi_pos]
  · have hrhalf' : (2 : ℝ) * r ≤ n := by exact_mod_cast hrhalf
    apply (div_le_iff₀ hn0).2
    nlinarith [Real.pi_pos]
  · apply (div_le_div_iff_of_pos_right hn0).2
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [Real.pi_pos]

private lemma norm_one_sub_stdAddChar {n : ℕ} [NeZero n] (l : ZMod n) :
    ‖(1 : ℂ) - ZMod.stdAddChar l‖ =
      2 * |Real.sin (Real.pi * (l.val : ℝ) / n)| := by
  rw [norm_sub_rev, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have harg :
      (2 : ℂ) * Real.pi * Complex.I * (l.val : ℂ) / (n : ℂ) =
        Complex.I * ((2 * Real.pi * (l.val : ℝ) / n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  rw [show (2 * Real.pi * (l.val : ℝ) / n : ℝ) / 2 =
      Real.pi * (l.val : ℝ) / n by ring]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

private lemma norm_one_add_mul_sq (α : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(1 : ℂ) + (α : ℂ) * z‖ ^ 2 =
      (1 + α) ^ 2 - α * ‖(1 : ℂ) - z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  have hzsq := Complex.sq_norm z
  rw [hz, one_pow, Complex.normSq_apply] at hzsq
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im,
    zero_add, Complex.sub_re, Complex.sub_im, Complex.mul_im, zero_add]
  linear_combination -(α + α ^ 2) * hzsq

private lemma sin_pi_div_le_abs_sin_val_of_two_le {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (l : ZMod n) (hl : l ≠ 0) :
    Real.sin (Real.pi / n) ≤
      |Real.sin (Real.pi * (l.val : ℝ) / n)| := by
  have hn0 : 0 < n := by omega
  have hv0 : 0 < l.val := ZMod.val_pos.mpr hl
  have hvn : l.val < n := ZMod.val_lt l
  by_cases hvhalf : 2 * l.val ≤ n
  · exact (sin_pi_div_le_sin_mul hn0 hv0 hvhalf).trans (le_abs_self _)
  · have hr0 : 0 < n - l.val := Nat.sub_pos_of_lt hvn
    have hrhalf : 2 * (n - l.val) ≤ n := by omega
    have hs := sin_pi_div_le_sin_mul hn0 hr0 hrhalf
    have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
    have hang :
        Real.pi * ((n - l.val : ℕ) : ℝ) / n =
          Real.pi - Real.pi * (l.val : ℝ) / n := by
      rw [Nat.cast_sub hvn.le]
      field_simp
    rw [hang, Real.sin_pi_sub] at hs
    exact hs.trans (le_abs_self _)

private lemma norm_one_add_stdAddChar_le_spectralRatio {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α) (l : ZMod n) (hl : l ≠ 0) :
    ‖(1 : ℂ) + (α : ℂ) * ZMod.stdAddChar l‖ ≤
      (Real.sqrt (1 + α ^ 2 + 2 * α * Real.cos (2 * Real.pi / n)) /
          (1 + α)) * (1 + α) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hangle0 : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hanglePi : Real.pi / (n : ℝ) < Real.pi := by
    apply (div_lt_iff₀ hnR).2
    have hnOne : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    nlinarith [Real.pi_pos]
  have hsin0 : 0 ≤ Real.sin (Real.pi / n) :=
    (Real.sin_pos_of_pos_of_lt_pi hangle0 hanglePi).le
  have hdist :
      2 * Real.sin (Real.pi / n) ≤
        ‖(1 : ℂ) - ZMod.stdAddChar l‖ := by
    rw [norm_one_sub_stdAddChar]
    exact mul_le_mul_of_nonneg_left
      (sin_pi_div_le_abs_sin_val_of_two_le hn l hl) (by norm_num)
  have hdistsq :
      (2 * Real.sin (Real.pi / n)) ^ 2 ≤
        ‖(1 : ℂ) - ZMod.stdAddChar l‖ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hsin0) hdist 2
  let R : ℝ := 1 + α ^ 2 + 2 * α * Real.cos (2 * Real.pi / n)
  have hnormsq :
      ‖(1 : ℂ) + (α : ℂ) * ZMod.stdAddChar l‖ ^ 2 ≤ R := by
    rw [norm_one_add_mul_sq α _ (AddChar.norm_apply ZMod.stdAddChar l)]
    have hmul := mul_le_mul_of_nonneg_left hdistsq hα
    have htrig :
        (1 + α) ^ 2 - α * (2 * Real.sin (Real.pi / n)) ^ 2 = R := by
      dsimp [R]
      rw [show 2 * Real.pi / (n : ℝ) = 2 * (Real.pi / n) by ring,
        mul_pow, Real.sin_sq_eq_half_sub]
      ring
    rw [← htrig]
    linarith
  have hR0 : 0 ≤ R := (sq_nonneg _).trans hnormsq
  have hsqrt :
      ‖(1 : ℂ) + (α : ℂ) * ZMod.stdAddChar l‖ ≤ Real.sqrt R := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt hR0]
  have hden : 0 < 1 + α := by linarith
  calc
    ‖(1 : ℂ) + (α : ℂ) * ZMod.stdAddChar l‖ ≤ Real.sqrt R := hsqrt
    _ = (Real.sqrt R / (1 + α)) * (1 + α) := by field_simp
    _ = _ := by rfl

private noncomputable def spectralRatio (a n : ℕ) : ℝ :=
  Real.sqrt
      (1 + root a n ^ 2 +
        2 * root a n * Real.cos (2 * Real.pi / n)) /
    (1 + root a n)

private lemma spectralRatio_mem_Icc {a n : ℕ} (ha : 0 < a) :
    spectralRatio a n ∈ Set.Icc 0 1 := by
  constructor
  · unfold spectralRatio
    exact div_nonneg (Real.sqrt_nonneg _) (by nlinarith [root_pos (n := n) ha])
  · let α := root a n
    let R := 1 + α ^ 2 + 2 * α * Real.cos (2 * Real.pi / n)
    have hα : 0 ≤ α := (root_pos (n := n) ha).le
    have hden : 0 < 1 + α := by linarith
    have hRle : R ≤ (1 + α) ^ 2 := by
      have hc := Real.cos_le_one (2 * Real.pi / (n : ℝ))
      dsimp [R]
      nlinarith
    have hsqrt : Real.sqrt R ≤ 1 + α :=
      (Real.sqrt_le_iff.mpr ⟨hden.le, hRle⟩)
    unfold spectralRatio
    change Real.sqrt R / (1 + α) ≤ 1
    exact (div_le_one hden).2 hsqrt

private lemma one_lt_root {a n : ℕ} (ha : 1 < a) (hn : 0 < n) : 1 < root a n := by
  exact Real.one_lt_rpow (by exact_mod_cast ha) (by positivity)

private lemma root_le_sqrt {a n : ℕ} (ha : 1 ≤ a) (hn : 2 ≤ n) :
    root a n ≤ √a := by
  rw [root, Real.sqrt_eq_rpow, one_div]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ha)
  exact inv_anti₀ (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn)

private lemma nthRoot_lt_root {a n : ℕ} (ha : 0 < a) (hn : n ≠ 0)
    (hnotpow : ¬ ∃ b : ℕ, b ^ n = a) :
    (n.nthRoot a : ℝ) < root a n := by
  have hle : n.nthRoot a ^ n ≤ a := Nat.pow_nthRoot_le (.inl hn)
  have hne : n.nthRoot a ^ n ≠ a := fun h ↦ hnotpow ⟨n.nthRoot a, h⟩
  have hlt : n.nthRoot a ^ n < a := lt_of_le_of_ne hle hne
  have hlt' : (n.nthRoot a : ℝ) ^ n < (a : ℝ) := by exact_mod_cast hlt
  rw [← root_pow ha hn] at hlt'
  exact (pow_lt_pow_iff_left₀ (by positivity) (root_pos ha).le hn).mp hlt'

private lemma root_lt_nthRoot_add_one {a n : ℕ} (ha : 0 < a) (hn : n ≠ 0) :
    root a n < n.nthRoot a + 1 := by
  have hlt := Nat.lt_pow_nthRoot_add_one hn a
  have hlt' : (a : ℝ) < ((n.nthRoot a + 1 : ℕ) : ℝ) ^ n := by exact_mod_cast hlt
  rw [← root_pow ha hn] at hlt'
  push_cast at hlt'
  exact (pow_lt_pow_iff_left₀ (root_pos ha).le (by positivity) hn).mp hlt'

private lemma root_le_nat {a n : ℕ} (ha : 1 < a) (hn : 0 < n) :
    root a n ≤ a := by
  calc
    root a n = root a n ^ 1 := by simp
    _ ≤ root a n ^ n := pow_le_pow_right₀ (one_lt_root ha hn).le hn
    _ = a := root_pow (by omega) hn.ne'

private lemma cast_sum_coeff_le {a n k : ℕ} (ha : 1 < a) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, coeff a n k i : ℕ) ≤ (1 + root a n) ^ k := by
  rw [sum_coeff_eq a n k hn,
    show (1 + root a n) ^ k = (root a n + 1) ^ k by rw [add_comm], add_pow]
  push_cast
  apply Finset.sum_le_sum
  intro j hj
  simp only [one_pow, mul_one]
  ring_nf
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ((a : ℝ) ^ (j / n)) = (root a n ^ n) ^ (j / n) := by
      rw [root_pow (by omega) hn.ne']
    _ = root a n ^ (n * (j / n)) := by rw [pow_mul]
    _ ≤ root a n ^ j :=
      pow_le_pow_right₀ (one_lt_root ha hn).le (Nat.mul_div_le j n)

private lemma coeff_normalized_close {a n k i : ℕ}
    (ha : 4 ≤ a) (hn : 1 < n) (hpow : 2 ^ (n - 1) ≤ a)
    (hi : i < n) (hk : 2 * a * n ≤ k) :
    |((n : ℝ) * coeff a n k i * root a n ^ i) / (1 + root a n) ^ k - 1| <
      1 / (16 * (n : ℝ) * a ^ 2) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let α := root a n
  let q := spectralRatio a n
  let f : ZMod n → ℂ := fun l ↦
    ZMod.stdAddChar (-((i : ZMod n) * l)) *
      (1 + (α : ℂ) * ZMod.stdAddChar l) ^ k
  have ha0 : 0 < a := by omega
  have hα0 : 0 < α := root_pos (n := n) ha0
  have hroot : α ^ n = (a : ℝ) := root_pow ha0 (by omega)
  have hid := coeff_spectral_identity a n k i α hi hroot
  have hf0 : f 0 = ((1 + α) ^ k : ℝ) := by
    simp [f]
  have hsum :
      ∑ l ∈ (Finset.univ.erase (0 : ZMod n)), f l =
        ((n : ℝ) * coeff a n k i * α ^ i - (1 + α) ^ k : ℝ) := by
    calc
      ∑ l ∈ (Finset.univ.erase (0 : ZMod n)), f l =
          (∑ l : ZMod n, f l) - f 0 := by
        rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ 0)]
        ring
      _ = ((n : ℂ) * (coeff a n k i : ℂ) * (α : ℂ) ^ i) -
          ((1 + α) ^ k : ℝ) := by rw [← hid, hf0]
      _ = ((n : ℝ) * coeff a n k i * α ^ i - (1 + α) ^ k : ℝ) := by
        push_cast
        ring
  have hterm (l : ZMod n) (hl : l ≠ 0) :
      ‖f l‖ ≤ q ^ k * (1 + α) ^ k := by
    have hnorm :
        ‖(1 : ℂ) + (α : ℂ) * ZMod.stdAddChar l‖ ≤ q * (1 + α) := by
      simpa [q, spectralRatio, α] using
        norm_one_add_stdAddChar_le_spectralRatio
          (n := n) (by omega : 2 ≤ n) α hα0.le l hl
    calc
      ‖f l‖ = ‖(1 : ℂ) + (α : ℂ) * ZMod.stdAddChar l‖ ^ k := by
        simp [f]
      _ ≤ (q * (1 + α)) ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm k
      _ = q ^ k * (1 + α) ^ k := by rw [mul_pow]
  have hnormSum :
      ‖∑ l ∈ (Finset.univ.erase (0 : ZMod n)), f l‖ ≤
        (n - 1 : ℕ) * (q ^ k * (1 + α) ^ k) := by
    have h := norm_sum_le_of_le (Finset.univ.erase (0 : ZMod n))
      (fun l hl ↦ hterm l (Finset.ne_of_mem_erase hl))
    simpa [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod n)), ZMod.card] using h
  have hqBounds := spectralRatio_mem_Icc (n := n) ha0
  have hqPow : q ^ k ≤ q ^ (2 * a * n) :=
    pow_le_pow_of_le_one hqBounds.1 hqBounds.2 hk
  have hcentral0 : 0 < (1 + α) ^ k := pow_pos (by linarith) _
  have hnormBound :
      ‖∑ l ∈ (Finset.univ.erase (0 : ZMod n)), f l‖ ≤
        (n - 1 : ℕ) * q ^ (2 * a * n) * (1 + α) ^ k := by
    calc
      ‖∑ l ∈ (Finset.univ.erase (0 : ZMod n)), f l‖ ≤
          (n - 1 : ℕ) * (q ^ k * (1 + α) ^ k) := hnormSum
      _ = ((n - 1 : ℕ) * q ^ k) * (1 + α) ^ k := by ring
      _ ≤ ((n - 1 : ℕ) * q ^ (2 * a * n)) * (1 + α) ^ k := by
        apply mul_le_mul_of_nonneg_right _ hcentral0.le
        exact mul_le_mul_of_nonneg_left hqPow (by positivity)
      _ = (n - 1 : ℕ) * q ^ (2 * a * n) * (1 + α) ^ k := by ring
  have herror :
      (n - 1 : ℕ) * q ^ (2 * a * n) <
        1 / (16 * (n : ℝ) * (a : ℝ) ^ 2) := by
    simpa [q, spectralRatio, α, root] using
      spectral_error_bound ha hn hpow
  have hstrict :
      ‖∑ l ∈ (Finset.univ.erase (0 : ZMod n)), f l‖ <
        (1 / (16 * (n : ℝ) * (a : ℝ) ^ 2)) * (1 + α) ^ k :=
    hnormBound.trans_lt (mul_lt_mul_of_pos_right herror hcentral0)
  rw [hsum] at hstrict
  change
    ‖(((n : ℝ) * coeff a n k i * α ^ i - (1 + α) ^ k : ℝ) : ℂ)‖ <
      (1 / (16 * (n : ℝ) * (a : ℝ) ^ 2)) * (1 + α) ^ k at hstrict
  rw [Complex.norm_real, Real.norm_eq_abs] at hstrict
  change
    |((n : ℝ) * coeff a n k i * α ^ i) / (1 + α) ^ k - 1| <
      1 / (16 * (n : ℝ) * a ^ 2)
  rw [div_sub_one hcentral0.ne', abs_div, abs_of_pos hcentral0,
    div_lt_iff₀ hcentral0]
  exact hstrict

private lemma normalized_ratio_close {x y ε : ℝ}
    (hε : 0 < ε) (hεsmall : 4 * ε < 1)
    (hx : |x - 1| < ε) (hy : |y - 1| < ε) :
    |x / y - 1| < 4 * ε ∧ x / y < 2 := by
  have hyBounds := abs_lt.mp hy
  have hyPos : 0 < y := by nlinarith
  have hxy : |x - y| < 2 * ε := by
    calc
      |x - y| ≤ |x - 1| + |1 - y| := abs_sub_le x 1 y
      _ = |x - 1| + |y - 1| := by rw [abs_sub_comm 1 y]
      _ < ε + ε := add_lt_add hx hy
      _ = 2 * ε := by ring
  have hdenLarge : 2 * ε < 4 * ε * y := by
    have hyHalf : 1 / 2 < y := by nlinarith
    nlinarith [mul_pos (show 0 < 4 * ε by positivity) (sub_pos.mpr hyHalf)]
  have hratio : |x / y - 1| < 4 * ε := by
    rw [div_sub_one hyPos.ne', abs_div, abs_of_pos hyPos]
    exact (div_lt_iff₀ hyPos).2 (hxy.trans hdenLarge)
  exact ⟨hratio, by
    have := (abs_lt.mp hratio).2
    nlinarith⟩

private lemma coeff_ratio_close {a n k i j : ℕ}
    (ha : 4 ≤ a) (hn : 1 < n) (hpow : 2 ^ (n - 1) ≤ a)
    (hij : i ≤ j) (hj : j < n) (hk : 2 * a * n ≤ k) :
    |(coeff a n k i : ℝ) / coeff a n k j - root a n ^ (j - i)| <
        root a n ^ (j - i) / (4 * n * a ^ 2) ∧
      (coeff a n k i : ℝ) / coeff a n k j <
        2 * root a n ^ (j - i) := by
  let α := root a n
  let B := (1 + α) ^ k
  let ε := 1 / (16 * (n : ℝ) * (a : ℝ) ^ 2)
  let si := ((n : ℝ) * coeff a n k i * α ^ i) / B
  let sj := ((n : ℝ) * coeff a n k j * α ^ j) / B
  have ha0 : 0 < a := by omega
  have hα0 : 0 < α := root_pos (n := n) ha0
  have hB0 : 0 < B := pow_pos (by linarith) _
  have hnR : (0 : ℝ) < n := by positivity
  have hjk : j ≤ k := by
    calc
      j ≤ n := hj.le
      _ = 1 * n := by simp
      _ ≤ (2 * a) * n := Nat.mul_le_mul_right n (by omega)
      _ = 2 * a * n := by ring
      _ ≤ k := hk
  have hcj : 0 < coeff a n k j := coeff_pos_of_lt_of_le hj hjk
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεsmall : 4 * ε < 1 := by
    dsimp [ε]
    rw [show 4 * (1 / (16 * (n : ℝ) * (a : ℝ) ^ 2)) =
      4 / (16 * (n : ℝ) * (a : ℝ) ^ 2) by ring]
    apply (div_lt_one (by positivity)).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have ha4 : (4 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [sq_nonneg ((a : ℝ) - 4)]
  have hsi : |si - 1| < ε := by
    simpa [si, α, B, ε] using
      coeff_normalized_close ha hn hpow (by omega : i < n) hk
  have hsj : |sj - 1| < ε := by
    simpa [sj, α, B, ε] using
      coeff_normalized_close ha hn hpow hj hk
  have hratio := normalized_ratio_close hε hεsmall hsi hsj
  have hpowSplit : α ^ j = α ^ i * α ^ (j - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hrelation :
      (coeff a n k i : ℝ) / coeff a n k j =
        α ^ (j - i) * (si / sj) := by
    dsimp [si, sj]
    rw [hpowSplit]
    field_simp [hnR.ne', hB0.ne', hα0.ne',
      (show (coeff a n k j : ℝ) ≠ 0 by exact_mod_cast hcj.ne')]
  change
    |(coeff a n k i : ℝ) / coeff a n k j - α ^ (j - i)| <
        α ^ (j - i) / (4 * n * a ^ 2) ∧
      (coeff a n k i : ℝ) / coeff a n k j < 2 * α ^ (j - i)
  rw [hrelation]
  constructor
  · rw [show α ^ (j - i) * (si / sj) - α ^ (j - i) =
        α ^ (j - i) * (si / sj - 1) by ring,
      abs_mul, abs_of_pos (pow_pos hα0 _)]
    calc
      α ^ (j - i) * |si / sj - 1| < α ^ (j - i) * (4 * ε) :=
        mul_lt_mul_of_pos_left hratio.1 (pow_pos hα0 _)
      _ = α ^ (j - i) / (4 * n * a ^ 2) := by
        dsimp [ε]
        field_simp
        ring
  · exact (mul_lt_mul_of_pos_left hratio.2 (pow_pos hα0 _)).trans_eq (by ring)

private lemma one_add_root_le_three_quarters {a n : ℕ} (ha : 4 ≤ a) (hn : 2 ≤ n) :
    1 + root a n ≤ (3 / 4 : ℝ) * a := by
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ a by positivity)
  have hsqrt0 := Real.sqrt_nonneg (a : ℝ)
  have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hsqrt_bound : √(a : ℝ) ≤ (a : ℝ) / 2 := by
    nlinarith [sq_nonneg (√(a : ℝ) - 2)]
  have hroot := root_le_sqrt (show 1 ≤ a by omega) hn
  nlinarith

private lemma mul_three_quarters_pow_four_mul_lt_half {a : ℕ} (ha : 4 ≤ a) :
    (a : ℝ) * (3 / 4 : ℝ) ^ (4 * a) < 1 / 2 := by
  have ha0 : 0 < a := by omega
  have hbase : (3 / 4 : ℝ) ^ 4 < (1 / 2 : ℝ) := by norm_num
  have hpow : ((3 / 4 : ℝ) ^ 4) ^ a < ((1 / 2 : ℝ)) ^ a :=
    pow_lt_pow_left₀ hbase (by positivity) ha0.ne'
  have hfour : 4 * a ≤ 2 ^ a := four_mul_le_two_pow ha
  have hfourR : (4 : ℝ) * a ≤ (2 : ℝ) ^ a := by exact_mod_cast hfour
  have hquarter : (a : ℝ) / 2 ^ a ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [← pow_mul] at hpow
  have hrewrite : (a : ℝ) * (1 / 2 : ℝ) ^ a = (a : ℝ) / 2 ^ a := by
    rw [div_pow]
    simp [div_eq_mul_inv]
  calc
    (a : ℝ) * (3 / 4 : ℝ) ^ (4 * a) <
        (a : ℝ) * (1 / 2 : ℝ) ^ a := mul_lt_mul_of_pos_left hpow (by positivity)
    _ = (a : ℝ) / 2 ^ a := hrewrite
    _ ≤ 1 / 4 := hquarter
    _ < 1 / 2 := by norm_num

private lemma reducedEval_lt_modulus {a n k : ℕ} (ha : 4 ≤ a) (hn : 1 < n)
    (hk : k ≤ 2 * a * n + 1) :
    let K := 2 * a * n
    let x := a ^ K
    reducedEval a n k x < x ^ n - a := by
  let K := 2 * a * n
  let x := a ^ K
  have ha0 : 0 < a := by omega
  have hn0 : 0 < n := by omega
  have hK4a : 4 * a ≤ K := by
    calc
      4 * a ≤ (2 * n) * a := Nat.mul_le_mul_right a (by omega)
      _ = K := by simp [K]; ring
  have hK2 : 2 ≤ K := le_trans (by omega : 2 ≤ 4 * a) hK4a
  have hx0 : 0 < x := by
    exact pow_pos ha0 _
  have hbase0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hbase1 : (3 / 4 : ℝ) ≤ 1 := by norm_num
  have hbasePow :
      (3 / 4 : ℝ) ^ K ≤ (3 / 4 : ℝ) ^ (4 * a) :=
    pow_le_pow_of_le_one hbase0 hbase1 hK4a
  have hnumeric := mul_three_quarters_pow_four_mul_lt_half ha
  have hnumericK :
      (a : ℝ) * (3 / 4 : ℝ) ^ K < 1 / 2 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hbasePow (by positivity)) hnumeric
  have hcoef : 2 * (a : ℝ) * (3 / 4 : ℝ) ^ K < 1 := by
    nlinarith
  have hrootThree := one_add_root_le_three_quarters ha (by omega : 2 ≤ n)
  have hrootA : 1 + root a n ≤ (a : ℝ) := by
    calc
      1 + root a n ≤ (3 / 4 : ℝ) * a := hrootThree
      _ ≤ a := by nlinarith [show (0 : ℝ) ≤ a by positivity]
  have hrootPow :
      (1 + root a n) ^ K ≤ ((3 / 4 : ℝ) * a) ^ K :=
    pow_le_pow_left₀ (by nlinarith [root_pos (n := n) ha0]) hrootThree K
  have hleading : 2 * (1 + root a n) ^ (K + 1) < (x : ℝ) := by
    calc
      2 * (1 + root a n) ^ (K + 1) =
          2 * (1 + root a n) * (1 + root a n) ^ K := by
            rw [pow_succ]
            ring
      _ ≤ 2 * (a : ℝ) * (((3 / 4 : ℝ) * a) ^ K) := by
        apply mul_le_mul
        · nlinarith
        · exact hrootPow
        · exact pow_nonneg (by nlinarith [root_pos (n := n) ha0]) _
        · positivity
      _ = (2 * (a : ℝ) * (3 / 4 : ℝ) ^ K) * (a : ℝ) ^ K := by
        rw [mul_pow]
        ring
      _ < 1 * (a : ℝ) ^ K :=
        mul_lt_mul_of_pos_right hcoef (by positivity)
      _ = (x : ℝ) := by simp [x, K]
  have hEvalNat := reducedEval_le_top_pow_mul_sum
    (a := a) (n := n) (k := k) (x := x) hn0 hx0
  have hEvalCast :
      (reducedEval a n k x : ℝ) ≤
        (x : ℝ) ^ (n - 1) *
          (∑ i ∈ Finset.range n, coeff a n k i : ℕ) := by
    exact_mod_cast hEvalNat
  have hCoeff := cast_sum_coeff_le (a := a) (n := n) (k := k)
    (by omega : 1 < a) hn0
  have hEval :
      (reducedEval a n k x : ℝ) ≤
        (x : ℝ) ^ (n - 1) * (1 + root a n) ^ k := by
    exact hEvalCast.trans
      (mul_le_mul_of_nonneg_left hCoeff (by positivity))
  have hPowerK :
      (1 + root a n) ^ k ≤ (1 + root a n) ^ (K + 1) := by
    apply pow_le_pow_right₀
    · nlinarith [root_pos (n := n) ha0]
    · simpa [K] using hk
  have hdoubleReal :
      2 * (reducedEval a n k x : ℝ) < (x : ℝ) ^ n := by
    calc
      2 * (reducedEval a n k x : ℝ) ≤
          2 * ((x : ℝ) ^ (n - 1) * (1 + root a n) ^ k) :=
        mul_le_mul_of_nonneg_left hEval (by norm_num)
      _ ≤ (x : ℝ) ^ (n - 1) *
          (2 * (1 + root a n) ^ (K + 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hPowerK
          (show (0 : ℝ) ≤ 2 * (x : ℝ) ^ (n - 1) by positivity)]
      _ < (x : ℝ) ^ (n - 1) * x :=
        mul_lt_mul_of_pos_left hleading (by positivity)
      _ = (x : ℝ) ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel hn0]
  have hdouble : 2 * reducedEval a n k x < x ^ n := by
    exact_mod_cast hdoubleReal
  have ha2 : 2 * a < a ^ 2 := by nlinarith
  have hax : a ^ 2 ≤ x := by
    exact Nat.pow_le_pow_right ha0 hK2
  have hxn : x ≤ x ^ n := by
    simpa using Nat.pow_le_pow_right hx0 (show 1 ≤ n by omega)
  have haSmall : 2 * a < x ^ n := lt_of_lt_of_le ha2 (hax.trans hxn)
  change reducedEval a n k x < x ^ n - a
  omega

private lemma root_separation {a n : ℕ} (ha : 2 < a) (hn : 1 < n)
    (hpow : 2 ^ (n - 1) ≤ a) (hnotpow : ¬ ∃ b : ℕ, b ^ n = a) :
    root a n - n.nthRoot a ≥ root a n / (n * a ^ 2) ∧
      (n.nthRoot a + 1 : ℕ) - root a n ≥ root a n / (n * a ^ 2) := by
  let α := root a n
  let r := n.nthRoot a
  have ha0 : 0 < a := by omega
  have hn0 : n ≠ 0 := by omega
  have hα0 : 0 < α := root_pos ha0
  have hα1 : 1 < α := one_lt_root (by omega) (by omega)
  have hrα : (r : ℝ) < α := nthRoot_lt_root ha0 hn0 hnotpow
  have hαr : α < (r : ℝ) + 1 := root_lt_nthRoot_add_one ha0 hn0
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hrootpow : α ^ n = (a : ℝ) := root_pow ha0 hn0
  have hrootpowpred : α * α ^ (n - 1) = (a : ℝ) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega), hrootpow]
  have hden : (0 : ℝ) < n * a ^ 2 := by positivity
  constructor
  · have hltNat : r ^ n < a := by
      have hle : r ^ n ≤ a := Nat.pow_nthRoot_le (.inl hn0)
      exact lt_of_le_of_ne hle (fun h ↦ hnotpow ⟨r, h⟩)
    have hgapNat : 1 ≤ a - r ^ n := by omega
    have hgap : (1 : ℝ) ≤ α ^ n - (r : ℝ) ^ n := by
      have hcast : (1 : ℝ) ≤ ((a - r ^ n : ℕ) : ℝ) := by exact_mod_cast hgapNat
      rw [Nat.cast_sub hltNat.le, Nat.cast_pow] at hcast
      simpa [hrootpow] using hcast
    have habs := abs_pow_sub_pow_le (a := α) (b := (r : ℝ)) n
    have hpowdiff : 0 ≤ α ^ n - (r : ℝ) ^ n := sub_nonneg.mpr <| by
      exact pow_le_pow_left₀ hr0 hrα.le n
    rw [abs_of_nonneg hpowdiff, abs_of_nonneg hα0.le, abs_of_nonneg hr0,
      max_eq_left hrα.le, abs_of_nonneg (sub_nonneg.mpr hrα.le)] at habs
    have hone : (1 : ℝ) ≤ (α - r) * n * α ^ (n - 1) := hgap.trans habs
    have hαB : α * α ^ (n - 1) ≤ (a : ℝ) ^ 2 := by
      rw [hrootpowpred]
      exact_mod_cast (show a ≤ a ^ 2 by nlinarith)
    have hmul : α ≤ (α - r) * n * (a : ℝ) ^ 2 := by
      calc
        α = α * 1 := by ring
        _ ≤ α * ((α - r) * n * α ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left hone hα0.le
        _ = ((α - r) * n) * (α * α ^ (n - 1)) := by ring
        _ ≤ ((α - r) * n) * (a : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hαB (mul_nonneg (sub_nonneg.mpr hrα.le) (by positivity))
    rw [ge_iff_le, div_le_iff₀ hden]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  · have hgapNat : 1 ≤ (r + 1) ^ n - a := by
      have hlt : a < (r + 1) ^ n := by simpa [r] using Nat.lt_pow_nthRoot_add_one hn0 a
      omega
    have hgap : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ n - α ^ n := by
      have hlt : a ≤ (r + 1) ^ n := by
        simpa [r] using (Nat.lt_pow_nthRoot_add_one hn0 a).le
      have hcast : (1 : ℝ) ≤ ((((r + 1) ^ n - a : ℕ)) : ℝ) := by exact_mod_cast hgapNat
      rw [Nat.cast_sub hlt, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hcast
      simpa [hrootpow] using hcast
    have habs := abs_pow_sub_pow_le (a := (r : ℝ) + 1) (b := α) n
    have hpowdiff : 0 ≤ ((r : ℝ) + 1) ^ n - α ^ n := sub_nonneg.mpr <| by
      exact pow_le_pow_left₀ hα0.le hαr.le n
    rw [abs_of_nonneg hpowdiff, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r + 1),
      abs_of_nonneg hα0.le, max_eq_left hαr.le,
      abs_of_nonneg (sub_nonneg.mpr hαr.le)] at habs
    have hone : (1 : ℝ) ≤ ((r : ℝ) + 1 - α) * n * ((r : ℝ) + 1) ^ (n - 1) :=
      hgap.trans habs
    have hr_two : (r : ℝ) + 1 ≤ 2 * α := by linarith
    have hαB : α * ((r : ℝ) + 1) ^ (n - 1) ≤ (a : ℝ) ^ 2 := by
      calc
        α * ((r : ℝ) + 1) ^ (n - 1) ≤ α * (2 * α) ^ (n - 1) := by gcongr
        _ = (2 : ℝ) ^ (n - 1) * (α * α ^ (n - 1)) := by
          rw [mul_pow]
          ring
        _ = (2 : ℝ) ^ (n - 1) * a := by rw [hrootpowpred]
        _ ≤ (a : ℝ) * a := by gcongr; exact_mod_cast hpow
        _ = (a : ℝ) ^ 2 := by ring
    have hmul : α ≤ ((r : ℝ) + 1 - α) * n * (a : ℝ) ^ 2 := by
      calc
        α = α * 1 := by ring
        _ ≤ α * (((r : ℝ) + 1 - α) * n * ((r : ℝ) + 1) ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left hone hα0.le
        _ = (((r : ℝ) + 1 - α) * n) * (α * ((r : ℝ) + 1) ^ (n - 1)) := by
          ring
        _ ≤ (((r : ℝ) + 1 - α) * n) * (a : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hαB (mul_nonneg (sub_nonneg.mpr hαr.le) (by positivity))
    rw [ge_iff_le, div_le_iff₀ hden]
    push_cast
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

private lemma div_sub_one_eq_nthRoot_of_approx {a n N D : ℕ}
    (ha : 2 < a) (hn : 1 < n) (hpow : 2 ^ (n - 1) ≤ a)
    (hnotpow : ¬ ∃ b : ℕ, b ^ n = a)
    (happrox :
      |(N : ℝ) / (D : ℝ) - 1 - root a n| <
        root a n / (2 * n * a ^ 2)) :
    N / D - 1 = n.nthRoot a := by
  have hsep := root_separation ha hn hpow hnotpow
  have hα0 : 0 < root a n := root_pos (by omega)
  have hhalf :
      root a n / (2 * n * a ^ 2) < root a n / (n * a ^ 2) := by
    apply div_lt_div_of_pos_left hα0
    · positivity
    · nlinarith [show (0 : ℝ) < n * a ^ 2 by positivity]
  have habs := abs_lt.mp happrox
  have hlo : (n.nthRoot a : ℝ) < (N : ℝ) / (D : ℝ) - 1 := by
    have := hsep.1
    linarith
  have hhi : (N : ℝ) / (D : ℝ) - 1 < (n.nthRoot a : ℝ) + 1 := by
    have := hsep.2
    push_cast at this
    linarith
  have hf : ⌊(N : ℝ) / (D : ℝ)⌋₊ = n.nthRoot a + 1 :=
    Nat.floor_eq_on_Ico (n.nthRoot a + 1) _
      ⟨by push_cast; linarith, by push_cast; linarith⟩
  rw [Nat.floor_div_eq_div] at hf
  omega

private lemma shunia_integer_root_three_two :
    let k := 2 * 3 * 2
    let x := 3 ^ k
    let m := x ^ 2 - 3
    Nat.nthRoot 2 3 =
      ((x + 1) ^ (k + 1) % m) / ((x + 1) ^ k % m) - 1 := by
  have hroot : Nat.nthRoot 2 3 = 1 := by decide
  rw [hroot]
  norm_num [Nat.pow_mod]

private lemma shunia_integer_root_of_four_le
    (a n : ℕ) (ha : 4 ≤ a) (hn : 1 < n)
    (hlog : n ≤ Nat.log2 a + 1)
    (hnotpow : ¬ ∃ b : ℕ, b ^ n = a) :
    let k := 2 * a * n
    let x := a ^ k
    let m := x ^ n - a
    n.nthRoot a =
      ((x + 1) ^ (k + 1) % m) / ((x + 1) ^ k % m) - 1 := by
  let K := 2 * a * n
  let X := a ^ K
  let M := X ^ n - a
  let U := coeff a n K (n - 1)
  let V := coeff a n K (n - 2)
  let C := coeff a n (K + 1) (n - 1)
  let D := reducedEval a n K X
  let N := reducedEval a n (K + 1) X
  change n.nthRoot a = ((X + 1) ^ (K + 1) % M) / ((X + 1) ^ K % M) - 1
  have ha0 : 0 < a := by omega
  have hn0 : 0 < n := by omega
  have hpow : 2 ^ (n - 1) ≤ a := by
    rw [← Nat.le_log2 ha0.ne']
    omega
  have hna : n ≤ a := by
    have := (n - 1).lt_two_pow_self
    omega
  have hKtop : n - 1 ≤ K := by
    calc
      n - 1 ≤ n := Nat.sub_le n 1
      _ = 1 * n := by simp
      _ ≤ (2 * a) * n := Nat.mul_le_mul_right n (by omega)
      _ = K := by simp [K]
  have hKpos : 1 ≤ K := by
    dsimp [K]
    nlinarith
  have hX0 : 0 < X := by simp [X, ha0]
  have haX : a ≤ X := by
    dsimp [X]
    simpa using Nat.pow_le_pow_right ha0 hKpos
  have hXXn : X ≤ X ^ n := by
    simpa using Nat.pow_le_pow_right hX0 (show 1 ≤ n by omega)
  have haXn : a ≤ X ^ n := haX.trans hXXn
  have hsmallK : reducedEval a n K X < M := by
    simpa [K, X, M] using
      (reducedEval_lt_modulus (a := a) (n := n) (k := 2 * a * n)
        ha hn (by omega))
  have hsmallSucc : reducedEval a n (K + 1) X < M := by
    simpa [K, X, M] using
      (reducedEval_lt_modulus (a := a) (n := n) (k := 2 * a * n + 1)
        ha hn (by omega))
  have hresK : (X + 1) ^ K % M = D := by
    simpa [D, M] using
      add_one_pow_mod_eq_reducedEval (a := a) (n := n) (k := K) (x := X)
        hn0 haXn hsmallK
  have hresSucc : (X + 1) ^ (K + 1) % M = N := by
    simpa [N, M] using
      add_one_pow_mod_eq_reducedEval (a := a) (n := n) (k := K + 1) (x := X)
        hn0 haXn hsmallSucc
  have hU : 0 < U := by
    exact coeff_pos_of_lt_of_le (by omega) hKtop
  have hC : 0 < C := by
    exact coeff_pos_of_lt_of_le (by omega) (by omega)
  have hα : 1 < root a n := one_lt_root (by omega) hn0
  have hαpow : root a n ^ n = (a : ℝ) := root_pow ha0 (by omega)
  have hrelK : ∀ i < n - 1,
      (coeff a n K i : ℝ) / coeff a n K (n - 1) <
        2 * root a n ^ (n - 1 - i) := by
    intro i hi
    exact (coeff_ratio_close ha hn hpow (by omega) (by omega) (by simp [K])).2
  have hrelSucc : ∀ i < n - 1,
      (coeff a n (K + 1) i : ℝ) / coeff a n (K + 1) (n - 1) <
        2 * root a n ^ (n - 1 - i) := by
    intro i hi
    exact (coeff_ratio_close ha hn hpow (by omega) (by omega) (by simp [K])).2
  have hcoeff :
      |(V : ℝ) / U - root a n| < root a n / (4 * n * a ^ 2) := by
    simpa [U, V, show n - 1 - (n - 2) = 1 by omega] using
      (coeff_ratio_close (a := a) (n := n) (k := K) (i := n - 2) (j := n - 1)
        ha hn hpow (by omega) (by omega) (by simp [K])).1
  have hrec : C = U + V := by
    simpa [C, U, V] using coeff_succ_top (a := a) (n := n) (k := K) hn
  have hCUeq : (C : ℝ) / U = 1 + (V : ℝ) / U := by
    rw [hrec]
    push_cast
    field_simp [show (U : ℝ) ≠ 0 by exact_mod_cast hU.ne']
  have herrorOne : root a n / (4 * n * a ^ 2) < 1 := by
    apply (div_lt_one (by positivity)).2
    have hrootA := root_le_nat (a := a) (n := n) (by omega) hn0
    have hlarge : (a : ℝ) < 4 * n * (a : ℝ) ^ 2 := by
      have hfactor : (1 : ℝ) < 4 * n * a := by
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
        have ha4 : (4 : ℝ) ≤ a := by exact_mod_cast ha
        nlinarith
      nlinarith [mul_pos (show (0 : ℝ) < a by positivity)
        (sub_pos.mpr hfactor)]
    exact hrootA.trans_lt hlarge
  have hCU : (C : ℝ) / U < 2 * a := by
    have hVU : (V : ℝ) / U < root a n + 1 := by
      have := (abs_lt.mp hcoeff).2
      linarith
    rw [hCUeq]
    have hrootA := root_le_nat (a := a) (n := n) (by omega) hn0
    have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith
  have heval :
      |(N : ℝ) / D - (C : ℝ) / U| < root a n / (4 * n * a ^ 2) := by
    simpa [N, D, C, U, reducedEval, X, K] using
      (eval_ratio_close_leading_ratio
        (α := root a n)
        (fun i ↦ coeff a n K i)
        (fun i ↦ coeff a n (K + 1) i)
        ha hn hna hα hαpow hU hC hrelK hrelSucc hCU)
  have htotal :
      |(N : ℝ) / D - 1 - root a n| <
        root a n / (2 * n * a ^ 2) := by
    calc
      |(N : ℝ) / D - 1 - root a n| =
          |((N : ℝ) / D - (C : ℝ) / U) +
            ((V : ℝ) / U - root a n)| := by
        rw [hCUeq]
        congr 1
        ring
      _ ≤ |(N : ℝ) / D - (C : ℝ) / U| +
          |(V : ℝ) / U - root a n| := abs_add_le _ _
      _ < root a n / (4 * n * a ^ 2) +
          root a n / (4 * n * a ^ 2) := add_lt_add heval hcoeff
      _ = root a n / (2 * n * a ^ 2) := by ring
  have hrootResult :=
    div_sub_one_eq_nthRoot_of_approx
      (a := a) (n := n) (N := N) (D := D)
      (by omega) hn hpow hnotpow htotal
  rw [hresSucc, hresK]
  exact hrootResult.symm

/-- Shunia's integer-root formula, formerly Conjecture 6.1. -/
theorem shunia_integer_root
    (a n : ℕ) (ha : 2 < a) (hn : 1 < n)
    (hlog : n ≤ Nat.log2 a + 1)
    (hnotpow : ¬ ∃ b : ℕ, b ^ n = a) :
    let k := 2 * a * n
    let x := a ^ k
    let m := x ^ n - a
    n.nthRoot a =
      ((x + 1) ^ (k + 1) % m) / ((x + 1) ^ k % m) - 1 := by
  by_cases ha4 : 4 ≤ a
  · exact shunia_integer_root_of_four_le a n ha4 hn hlog hnotpow
  · have ha3 : a = 3 := by omega
    subst a
    have hn2 : n = 2 := by
      have hlog3 : Nat.log2 3 = 1 := by decide
      rw [hlog3] at hlog
      omega
    subst n
    exact shunia_integer_root_three_two

end ShuniaIntegerRoot
