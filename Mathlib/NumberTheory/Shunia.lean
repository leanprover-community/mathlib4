/-
Copyright (c) 2026 rbajaj5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rbajaj5
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic

/-!
# Shunia's integer-root formula

This file develops the coefficient and Fourier estimates needed to formalize Conjecture 6.1
from Joseph M. Shunia,
*Polynomial quotient rings and Kronecker substitution for deriving combinatorial identities*.

The intended public statement will be phrased using `Nat.nthRoot`: the quotient of the two least
nonnegative residues is one more than the integer `n`-th root.
-/

public section

namespace Nat

open scoped BigOperators

/-- The base used for the Kronecker substitution in Shunia's formula. -/
def shuniaBase (a n : ℕ) : ℕ := a ^ (2 * a * n)

/-- The modulus used in Shunia's formula. -/
def shuniaModulus (a n : ℕ) : ℕ := shuniaBase a n ^ n - a

/-- The denominator residue in Shunia's formula. -/
def shuniaDenominator (a n : ℕ) : ℕ :=
  (shuniaBase a n + 1) ^ (2 * a * n) % shuniaModulus a n

/-- The numerator residue in Shunia's formula. -/
def shuniaNumerator (a n : ℕ) : ℕ :=
  (shuniaBase a n + 1) ^ (2 * a * n + 1) % shuniaModulus a n

/-- The coefficient of residue class `i` in the reduction of `(1 + T) ^ k` modulo `T ^ n - a`. -/
def shuniaCoeff (a n k : ℕ) (i : ZMod n) : ℕ :=
  ∑ j ∈ Finset.range (k + 1),
    if (j : ZMod n) = i then k.choose j * a ^ (j / n) else 0

/-- Evaluation at `X` of the reduced coefficient vector for `(1 + T) ^ k`. -/
def shuniaCoeffEval (a n k X : ℕ) [NeZero n] : ℕ :=
  ∑ i : ZMod n, shuniaCoeff a n k i * X ^ i.val

private lemma shuniaCoeffEval_eq_sum (a n k X : ℕ) [NeZero n] :
    shuniaCoeffEval a n k X =
      ∑ j ∈ Finset.range (k + 1), k.choose j * a ^ (j / n) * X ^ (j % n) := by
  classical
  simp only [shuniaCoeffEval, shuniaCoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [eq_comm, ZMod.val_natCast]

private lemma pow_modEq_div_mod (a n X j : ℕ) (haX : a ≤ X ^ n) :
    X ^ j ≡ a ^ (j / n) * X ^ (j % n) [MOD X ^ n - a] := by
  have hbase : X ^ n ≡ a [MOD X ^ n - a] :=
    ((Nat.modEq_iff_dvd' haX).2 dvd_rfl).symm
  calc
    X ^ j = X ^ (n * (j / n) + j % n) := by
      congr 1
      simpa [mul_comm] using (Nat.div_add_mod' j n).symm
    _ = (X ^ n) ^ (j / n) * X ^ (j % n) := by rw [pow_add, pow_mul]
    _ ≡ a ^ (j / n) * X ^ (j % n) [MOD X ^ n - a] :=
      (hbase.pow (j / n)).mul_right _

private lemma pow_add_one_modEq_coeffEval (a n k X : ℕ) [NeZero n] (haX : a ≤ X ^ n) :
    (X + 1) ^ k ≡ shuniaCoeffEval a n k X [MOD X ^ n - a] := by
  rw [shuniaCoeffEval_eq_sum]
  have hsum := Nat.ModEq.sum (s := Finset.range (k + 1)) fun j _ ↦
    (pow_modEq_div_mod a n X j haX).mul_left (k.choose j)
  simpa [add_pow, mul_assoc, mul_comm, mul_left_comm] using hsum

private noncomputable def shuniaScaledCoeff (a n k : ℕ) (α : ℝ) (i : ZMod n) : ℂ :=
  shuniaCoeff a n k i * (α : ℂ) ^ i.val

private lemma cast_pow_div_mul_pow_mod {a n j : ℕ} {α : ℝ} (hα : α ^ n = a) :
    ((a ^ (j / n) : ℕ) : ℂ) * (α : ℂ) ^ (j % n) = (α : ℂ) ^ j := by
  have hαc : (α : ℂ) ^ n = (a : ℂ) := by exact_mod_cast hα
  rw [Nat.cast_pow, ← hαc, ← pow_mul, ← pow_add]
  congr 1
  simpa [mul_comm] using Nat.div_add_mod' j n

private lemma stdAddChar_neg_natCast_mul (n j : ℕ) [NeZero n] (t : ZMod n) :
    ZMod.stdAddChar (-((j : ZMod n) * t)) = ZMod.stdAddChar (-t) ^ j := by
  rw [show -((j : ZMod n) * t) = j • (-t) by simp [nsmul_eq_mul]]
  exact AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := n)) j (-t)

private lemma dft_shuniaScaledCoeff (a n k : ℕ) [NeZero n] (α : ℝ) (hα : α ^ n = a)
    (t : ZMod n) :
    ZMod.dft (shuniaScaledCoeff a n k α) t =
      (1 + (α : ℂ) * ZMod.stdAddChar (-t)) ^ k := by
  classical
  rw [ZMod.dft_apply]
  simp only [shuniaScaledCoeff, shuniaCoeff, smul_eq_mul, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_zero]
  conv_lhs =>
    enter [2, i]
    rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℂ) * ((α : ℂ) * ZMod.stdAddChar (-t)) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [mul_ite, ite_mul, mul_zero, zero_mul, eq_comm, Fintype.sum_ite_eq']
      rw [ZMod.val_natCast, stdAddChar_neg_natCast_mul]
      have hpower :
          (a : ℂ) ^ (j / n) * (α : ℂ) ^ (j % n) = (α : ℂ) ^ j := by
        simpa only [Nat.cast_pow] using
          (cast_pow_div_mul_pow_mod (a := a) (n := n) (j := j) hα)
      rw [show ZMod.stdAddChar (-t) ^ j *
            ((k.choose j : ℂ) * (a : ℂ) ^ (j / n)) * (α : ℂ) ^ (j % n) =
          (k.choose j : ℂ) * ZMod.stdAddChar (-t) ^ j *
            ((a : ℂ) ^ (j / n) * (α : ℂ) ^ (j % n)) by ring,
        hpower, mul_pow]
      ring
    _ = (1 + (α : ℂ) * ZMod.stdAddChar (-t)) ^ k := by
      simpa [mul_comm, add_comm] using
        (add_pow ((α : ℂ) * ZMod.stdAddChar (-t)) 1 k).symm

private lemma shuniaScaledCoeff_eq_fourierSum
    (a n k : ℕ) [NeZero n] (α : ℝ) (hα : α ^ n = a) (i : ZMod n) :
    shuniaScaledCoeff a n k α i =
      (n : ℂ)⁻¹ * ∑ t : ZMod n,
        ZMod.stdAddChar (t * i) * (1 + (α : ℂ) * ZMod.stdAddChar (-t)) ^ k := by
  have hinv :=
    congrFun ((ZMod.dft (N := n) (E := ℂ)).symm_apply_apply
      (shuniaScaledCoeff a n k α)) i
  rw [ZMod.invDFT_apply] at hinv
  simpa only [smul_eq_mul, dft_shuniaScaledCoeff a n k α hα] using hinv.symm

/-- The positive real contribution of the trivial character in the Fourier formula. -/
private noncomputable def shuniaMainTerm (n k : ℕ) (α : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * (1 + (α : ℂ)) ^ k

private lemma shuniaScaledCoeff_sub_mainTerm
    (a n k : ℕ) [NeZero n] (α : ℝ) (hα : α ^ n = a) (i : ZMod n) :
    shuniaScaledCoeff a n k α i - shuniaMainTerm n k α =
      (n : ℂ)⁻¹ * ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
        ZMod.stdAddChar (t * i) * (1 + (α : ℂ) * ZMod.stdAddChar (-t)) ^ k := by
  rw [shuniaScaledCoeff_eq_fourierSum a n k α hα, shuniaMainTerm]
  rw [← Finset.add_sum_erase Finset.univ
    (fun t : ZMod n ↦
      ZMod.stdAddChar (t * i) * (1 + (α : ℂ) * ZMod.stdAddChar (-t)) ^ k)
    (Finset.mem_univ (0 : ZMod n))]
  simp
  ring

private lemma norm_shuniaScaledCoeff_sub_mainTerm_le_sum
    (a n k : ℕ) [NeZero n] (α : ℝ) (hα : α ^ n = a) (i : ZMod n) :
    ‖shuniaScaledCoeff a n k α i - shuniaMainTerm n k α‖ ≤
      ‖(n : ℂ)⁻¹‖ * ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
        ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ^ k := by
  rw [shuniaScaledCoeff_sub_mainTerm a n k α hα, norm_mul]
  gcongr
  calc
    ‖∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
        ZMod.stdAddChar (t * i) * (1 + (α : ℂ) * ZMod.stdAddChar (-t)) ^ k‖
        ≤ ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
          ‖ZMod.stdAddChar (t * i) *
            (1 + (α : ℂ) * ZMod.stdAddChar (-t)) ^ k‖ := norm_sum_le _ _
    _ = ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
        ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ^ k := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [norm_pow]

private lemma norm_shuniaScaledCoeff_sub_mainTerm_le
    (a n k : ℕ) [NeZero n] (α : ℝ) (hα : α ^ n = a) (i : ZMod n) (B : ℝ)
    (hB : ∀ t : ZMod n, t ≠ 0 → ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ≤ B) :
    ‖shuniaScaledCoeff a n k α i - shuniaMainTerm n k α‖ ≤
      ‖(n : ℂ)⁻¹‖ * ((n - 1 : ℕ) : ℝ) * B ^ k := by
  have hsum :
    ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
        ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ^ k
        ≤ ((n - 1 : ℕ) : ℝ) * B ^ k := by
    calc
      ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
          ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ^ k
          ≤ ∑ _t ∈ (Finset.univ.erase (0 : ZMod n)), B ^ k := by
        apply Finset.sum_le_sum
        intro t ht
        exact pow_le_pow_left₀ (norm_nonneg _) (hB t (Finset.ne_of_mem_erase ht)) k
      _ = ((n - 1 : ℕ) : ℝ) * B ^ k := by simp
  calc
    ‖shuniaScaledCoeff a n k α i - shuniaMainTerm n k α‖
        ≤ ‖(n : ℂ)⁻¹‖ * ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
          ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ^ k :=
      norm_shuniaScaledCoeff_sub_mainTerm_le_sum a n k α hα i
    _ ≤ ‖(n : ℂ)⁻¹‖ * (((n - 1 : ℕ) : ℝ) * B ^ k) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖(n : ℂ)⁻¹‖ * ((n - 1 : ℕ) : ℝ) * B ^ k := by ring

private lemma norm_one_sub_stdAddChar (n : ℕ) [NeZero n] (t : ZMod n) :
    ‖(1 : ℂ) - ZMod.stdAddChar t‖ =
      ‖2 * Real.sin (Real.pi * (t.val : ℝ) / n)‖ := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp]
  change ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * ((t.val : ℝ) / n) : ℝ) * Complex.I)‖ =
    ‖2 * Real.sin (Real.pi * (t.val : ℝ) / n)‖
  rw [← norm_neg, neg_sub]
  rw [show ((2 * Real.pi * ((t.val : ℝ) / n) : ℝ) : ℂ) * Complex.I =
      Complex.I * ((2 * Real.pi * (t.val : ℝ) / n : ℝ) : ℂ) by
        rw [mul_comm]
        norm_cast
        ring_nf]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  congr 2
  ring_nf

private lemma four_div_le_two_mul_sin_pi_mul_div_of_le_half
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hmhalf : m ≤ n / 2) :
    (4 : ℝ) / n ≤ 2 * Real.sin (Real.pi * (m : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have htwom : 2 * m ≤ n := by omega
  have htwomR : (2 : ℝ) * m ≤ n := by exact_mod_cast htwom
  have hx0 : (0 : ℝ) ≤ Real.pi * (m : ℝ) / n := by positivity
  have hxhalf : Real.pi * (m : ℝ) / n ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hnR]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hx0 hxhalf
  have hscale :
      (2 : ℝ) * m / n = 2 / Real.pi * (Real.pi * (m : ℝ) / n) := by
    field_simp
  have hone : (2 : ℝ) / n ≤ 2 * m / n := by
    apply (div_le_div_iff_of_pos_right hnR).2
    linarith
  have : (2 : ℝ) / n ≤ Real.sin (Real.pi * (m : ℝ) / n) := by
    calc
      (2 : ℝ) / n ≤ 2 * m / n := hone
      _ = 2 / Real.pi * (Real.pi * (m : ℝ) / n) := hscale
      _ ≤ Real.sin (Real.pi * (m : ℝ) / n) := hsin
  calc
    (4 : ℝ) / n = 2 * (2 / n) := by ring
    _ ≤ 2 * Real.sin (Real.pi * (m : ℝ) / n) :=
      mul_le_mul_of_nonneg_left this (by norm_num)

private lemma four_div_le_norm_one_sub_stdAddChar
    (n : ℕ) [NeZero n] (t : ZMod n) (ht : t ≠ 0) :
    (4 : ℝ) / n ≤ ‖(1 : ℂ) - ZMod.stdAddChar t‖ := by
  have hn : 0 < n := NeZero.pos n
  have hm : 0 < t.val := ZMod.val_pos.mpr ht
  have hmn : t.val < n := t.val_lt
  rw [norm_one_sub_stdAddChar]
  have hsin_nonneg :
      0 ≤ Real.sin (Real.pi * (t.val : ℝ) / n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_iff₀ hnR]
      have hmnR : (t.val : ℝ) ≤ n := by exact_mod_cast hmn.le
      nlinarith [Real.pi_pos]
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) hsin_nonneg)]
  by_cases hhalf : t.val ≤ n / 2
  · exact four_div_le_two_mul_sin_pi_mul_div_of_le_half n t.val hn hm hhalf
  · let d := n - t.val
    have hd : 0 < d := Nat.sub_pos_of_lt hmn
    have hdhalf : d ≤ n / 2 := by
      dsimp [d]
      omega
    have hsin :
        Real.sin (Real.pi * (t.val : ℝ) / n) =
          Real.sin (Real.pi * (d : ℝ) / n) := by
      calc
        Real.sin (Real.pi * (t.val : ℝ) / n) =
            Real.sin (Real.pi - Real.pi * (t.val : ℝ) / n) :=
          (Real.sin_pi_sub _).symm
        _ = Real.sin (Real.pi * (d : ℝ) / n) := by
          congr 1
          dsimp [d]
          have hnR : (n : ℝ) ≠ 0 := by positivity
          rw [Nat.cast_sub hmn.le]
          field_simp
    rw [hsin]
    exact four_div_le_two_mul_sin_pi_mul_div_of_le_half n d hn hd hdhalf

private lemma norm_one_add_mul_stdAddChar_sq
    (n : ℕ) [NeZero n] (α : ℝ) (t : ZMod n) :
    ‖1 + (α : ℂ) * ZMod.stdAddChar t‖ ^ 2 =
      (1 + α) ^ 2 - α * ‖(1 : ℂ) - ZMod.stdAddChar t‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_ofReal]
  rw [show Complex.normSq (ZMod.stdAddChar t) = 1 by
    rw [Complex.normSq_eq_norm_sq]
    simp]
  ring

private lemma norm_one_add_mul_stdAddChar_le_sqrt
    (n : ℕ) [NeZero n] (α : ℝ) (hα : 0 ≤ α) (t : ZMod n) (ht : t ≠ 0) :
    ‖1 + (α : ℂ) * ZMod.stdAddChar t‖ ≤
      Real.sqrt ((1 + α) ^ 2 - 16 * α / n ^ 2) := by
  have hchord := four_div_le_norm_one_sub_stdAddChar n t ht
  have hchord_sq :
      (16 : ℝ) / n ^ 2 ≤ ‖(1 : ℂ) - ZMod.stdAddChar t‖ ^ 2 := by
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 / n) hchord 2
    calc
      (16 : ℝ) / n ^ 2 = ((4 : ℝ) / n) ^ 2 := by ring
      _ ≤ ‖(1 : ℂ) - ZMod.stdAddChar t‖ ^ 2 := hsquare
  apply Real.le_sqrt_of_sq_le
  rw [norm_one_add_mul_stdAddChar_sq]
  calc
    (1 + α) ^ 2 - α * ‖(1 : ℂ) - ZMod.stdAddChar t‖ ^ 2
        ≤ (1 + α) ^ 2 - α * ((16 : ℝ) / n ^ 2) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hchord_sq hα) _
    _ = (1 + α) ^ 2 - 16 * α / n ^ 2 := by ring

/-- A uniform squared spectral ratio for all nontrivial Fourier modes. -/
private noncomputable def shuniaQSq (n : ℕ) (α : ℝ) : ℝ :=
  1 - 16 * α / ((n : ℝ) ^ 2 * (1 + α) ^ 2)

private lemma shuniaQSq_nonneg
    (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α) :
    0 ≤ shuniaQSq n α := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hαsq : 4 * α ≤ (1 + α) ^ 2 := by nlinarith [sq_nonneg (α - 1)]
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 * (1 + α) ^ 2 := by positivity
  rw [shuniaQSq, sub_nonneg, div_le_one hden]
  have hmul := mul_le_mul hnsq hαsq (mul_nonneg (by norm_num) hα) (by norm_num)
  nlinarith

private lemma shuniaQSq_le_exp (n : ℕ) (α : ℝ) :
    shuniaQSq n α ≤
      Real.exp (-(16 * α / ((n : ℝ) ^ 2 * (1 + α) ^ 2))) := by
  simpa [shuniaQSq, add_comm] using
    Real.add_one_le_exp (-(16 * α / ((n : ℝ) ^ 2 * (1 + α) ^ 2)))

/-- The exponent appearing in the uniform decay estimate. -/
private noncomputable def shuniaDecay (a n : ℕ) (α : ℝ) : ℝ :=
  16 * a * α / (n * (1 + α) ^ 2)

private lemma shuniaQSq_pow_le_exp_neg_decay
    (a n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α) :
    shuniaQSq n α ^ (a * n) ≤ Real.exp (-shuniaDecay a n α) := by
  have hpow := pow_le_pow_left₀ (shuniaQSq_nonneg n hn α hα)
    (shuniaQSq_le_exp n α) (a * n)
  calc
    shuniaQSq n α ^ (a * n)
        ≤ Real.exp (-(16 * α / ((n : ℝ) ^ 2 * (1 + α) ^ 2))) ^ (a * n) := hpow
    _ = Real.exp ((a * n : ℕ) *
        (-(16 * α / ((n : ℝ) ^ 2 * (1 + α) ^ 2)))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-shuniaDecay a n α) := by
      congr 1
      rw [shuniaDecay]
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (show n ≠ 0 by omega)
      push_cast
      field_simp

private lemma five_thirds_pow_le_two_pow_sub_one (n : ℕ) (hn : 6 ≤ n) :
    ((5 : ℝ) / 3) ^ n ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      calc
        ((5 : ℝ) / 3) ^ n * (5 / 3) ≤ 2 ^ (n - 1) * (5 / 3) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ 2 ^ (n - 1) * 2 :=
          mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
        _ = 2 ^ (n + 1 - 1) := by
          rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]

private lemma five_thirds_le_of_root_and_log_bound
    (a n : ℕ) (hn : 6 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (hroot : α ^ n = a) (ha : 2 ^ (n - 1) ≤ a) :
    (5 : ℝ) / 3 ≤ α := by
  have hpow : ((5 : ℝ) / 3) ^ n ≤ α ^ n := by
    calc
      ((5 : ℝ) / 3) ^ n ≤ 2 ^ (n - 1) := five_thirds_pow_le_two_pow_sub_one n hn
      _ ≤ (a : ℝ) := by exact_mod_cast ha
      _ = α ^ n := hroot.symm
  by_contra h
  have hlt : α < (5 : ℝ) / 3 := lt_of_not_ge h
  have hstrict : α ^ n < ((5 : ℝ) / 3) ^ n :=
    pow_lt_pow_left₀ hlt hα (by omega)
  exact (not_lt_of_ge hpow hstrict)

private lemma decay_lower_bound_of_six_le
    (a n : ℕ) (hn : 6 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (hroot : α ^ n = a) (ha : 2 ^ (n - 1) ≤ a) :
    (25 : ℝ) / 4 * a / (n * α) ≤ shuniaDecay a n α := by
  have hα53 := five_thirds_le_of_root_and_log_bound a n hn α hα hroot ha
  have hnR : (0 : ℝ) < n := by positivity
  have hαpos : 0 < α := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5 / 3) hα53
  have hlinear : 1 + α ≤ (8 / 5 : ℝ) * α := by linarith
  have hsquare : (1 + α) ^ 2 ≤ ((8 / 5 : ℝ) * α) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlinear 2
  rw [shuniaDecay]
  have hnum : (0 : ℝ) ≤ 16 * a * α := by positivity
  calc
    (25 : ℝ) / 4 * a / (n * α) =
        16 * a * α / (n * (((8 / 5 : ℝ) * α) ^ 2)) := by
      field_simp
      ring
    _ ≤ 16 * a * α / (n * (1 + α) ^ 2) := by
      apply div_le_div_of_nonneg_left hnum
      · positivity
      · exact mul_le_mul_of_nonneg_left hsquare (by positivity)

private lemma ten_factorial_poly_lt_two_pow (n : ℕ) (hn : 10 ≤ n) :
    16 * 10 ! * 4 ^ 10 * n ^ 12 < 25 ^ 10 * 2 ^ (7 * (n - 1)) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
      have hlinear : 10 * (n + 1) ≤ 11 * n := by omega
      have hpow := Nat.pow_le_pow_left hlinear 12
      have hconstant : 11 ^ 12 < 128 * 10 ^ 12 := by norm_num
      have hnpos : 0 < n ^ 12 := Nat.pow_pos (by omega)
      have hpoly : (n + 1) ^ 12 < 128 * n ^ 12 := by
        have hscaled :
            10 ^ 12 * (n + 1) ^ 12 < 10 ^ 12 * (128 * n ^ 12) := by
          calc
            10 ^ 12 * (n + 1) ^ 12 = (10 * (n + 1)) ^ 12 := by rw [mul_pow]
            _ ≤ (11 * n) ^ 12 := hpow
            _ = 11 ^ 12 * n ^ 12 := by rw [mul_pow]
            _ < (128 * 10 ^ 12) * n ^ 12 :=
              Nat.mul_lt_mul_of_pos_right hconstant hnpos
            _ = 10 ^ 12 * (128 * n ^ 12) := by ring
        omega
      let C : ℕ := 16 * 10 ! * 4 ^ 10
      let R : ℕ := 25 ^ 10 * 2 ^ (7 * (n - 1))
      have hC : 0 < C := by
        dsimp [C]
        positivity
      have hstep₁ : C * (n + 1) ^ 12 < 128 * (C * n ^ 12) := by
        calc
          C * (n + 1) ^ 12 < C * (128 * n ^ 12) :=
            Nat.mul_lt_mul_of_pos_left hpoly hC
          _ = 128 * (C * n ^ 12) := by ring
      have hstep₂ : 128 * (C * n ^ 12) < 128 * R := by
        apply Nat.mul_lt_mul_of_pos_left
        · simpa [C, R] using ih
        · norm_num
      calc
        16 * 10 ! * 4 ^ 10 * (n + 1) ^ 12 = C * (n + 1) ^ 12 := by rfl
        _ < 128 * (C * n ^ 12) := hstep₁
        _ < 128 * R := hstep₂
        _ = 25 ^ 10 * 2 ^ (7 * (n + 1 - 1)) := by
          dsimp [R]
          rw [show 7 * n = 7 * (n - 1) + 7 by omega, pow_add]
          norm_num
          ring

private lemma decay_large_of_ten_le
    (a n : ℕ) (hn : 10 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (hroot : α ^ n = a) (ha : 2 ^ (n - 1) ≤ a) :
    (16 : ℝ) * n * (n - 1) * a ^ 2 < Real.exp (shuniaDecay a n α) := by
  have hn6 : 6 ≤ n := hn.trans' (by norm_num)
  have hα53 := five_thirds_le_of_root_and_log_bound a n hn6 α hα hroot ha
  have hα1 : (1 : ℝ) ≤ α := le_trans (by norm_num) hα53
  have hαpos : 0 < α := zero_lt_one.trans_le hα1
  have haPos : (0 : ℝ) < a := by
    exact_mod_cast (lt_of_lt_of_le (Nat.pow_pos (by decide)) ha)
  have hα10 : α ^ 10 ≤ (a : ℝ) := by
    calc
      α ^ 10 ≤ α ^ n := pow_le_pow_right₀ hα1 hn
      _ = (a : ℝ) := hroot
  have ha7 : 2 ^ (7 * (n - 1)) ≤ a ^ 7 := by
    calc
      2 ^ (7 * (n - 1)) = (2 ^ (n - 1)) ^ 7 := by
        rw [show 7 * (n - 1) = (n - 1) * 7 by omega, pow_mul]
      _ ≤ a ^ 7 := Nat.pow_le_pow_left ha 7
  have hpolyNat :
      16 * 10 ! * 4 ^ 10 * n ^ 12 < 25 ^ 10 * a ^ 7 :=
    (ten_factorial_poly_lt_two_pow n hn).trans_le
      (Nat.mul_le_mul_left (25 ^ 10) ha7)
  have hpoly :
      (16 : ℝ) * (10 ! : ℕ) * 4 ^ 10 * n ^ 12 <
        (25 : ℝ) ^ 10 * (a : ℝ) ^ 7 := by
    exact_mod_cast hpolyNat
  have hcross :
      ((16 : ℝ) * n * (n - 1) * (a : ℝ) ^ 2) * (10 ! : ℕ) *
          (4 ^ 10 * n ^ 10 * α ^ 10) <
        (25 : ℝ) ^ 10 * (a : ℝ) ^ 10 := by
    calc
      ((16 : ℝ) * n * (n - 1) * (a : ℝ) ^ 2) * (10 ! : ℕ) *
          (4 ^ 10 * n ^ 10 * α ^ 10)
          ≤ ((16 : ℝ) * (10 ! : ℕ) * 4 ^ 10 * n ^ 12) * (a : ℝ) ^ 3 := by
        have haR : (0 : ℝ) ≤ a := by positivity
        calc
          ((16 : ℝ) * n * (n - 1) * (a : ℝ) ^ 2) * (10 ! : ℕ) *
              (4 ^ 10 * n ^ 10 * α ^ 10)
              ≤ ((16 : ℝ) * n * n * (a : ℝ) ^ 2) * (10 ! : ℕ) *
                (4 ^ 10 * n ^ 10 * α ^ 10) := by
                  gcongr
                  linarith
          _ ≤ ((16 : ℝ) * n * n * (a : ℝ) ^ 2) * (10 ! : ℕ) *
                (4 ^ 10 * n ^ 10 * (a : ℝ)) := by gcongr
          _ = ((16 : ℝ) * (10 ! : ℕ) * 4 ^ 10 * n ^ 12) * (a : ℝ) ^ 3 := by
            ring
      _ < ((25 : ℝ) ^ 10 * (a : ℝ) ^ 7) * (a : ℝ) ^ 3 :=
        mul_lt_mul_of_pos_right hpoly (pow_pos haPos 3)
      _ = (25 : ℝ) ^ 10 * (a : ℝ) ^ 10 := by ring
  let L : ℝ := (25 : ℝ) / 4 * a / (n * α)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hLpow :
      L ^ 10 = (25 : ℝ) ^ 10 * (a : ℝ) ^ 10 / (4 ^ 10 * n ^ 10 * α ^ 10) := by
    dsimp [L]
    field_simp
  have hterm :
      (16 : ℝ) * n * (n - 1) * a ^ 2 < L ^ 10 / (10 ! : ℕ) := by
    rw [hLpow]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (10 ! : ℕ))).2
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ 10 * n ^ 10 * α ^ 10)).2
    exact hcross
  have hLdecay : L ≤ shuniaDecay a n α :=
    decay_lower_bound_of_six_le a n hn6 α hα hroot ha
  have hdecay0 : 0 ≤ shuniaDecay a n α := hL0.trans hLdecay
  calc
    (16 : ℝ) * n * (n - 1) * a ^ 2
        < L ^ 10 / (10 ! : ℕ) := hterm
    _ ≤ shuniaDecay a n α ^ 10 / (10 ! : ℕ) := by
      gcongr
    _ ≤ Real.exp (shuniaDecay a n α) :=
      Real.pow_div_factorial_le_exp (x := shuniaDecay a n α) hdecay0 10

private lemma small_n_decay_numeric (n : ℕ) (hn6 : 6 ≤ n) (hn10 : n < 10) :
    (16 : ℝ) * (10 ! : ℕ) * 4 ^ 10 * n ^ 11 * (n - 1) <
      25 ^ 10 * (((2 ^ (n - 1) : ℕ) : ℝ) ^ 6) *
        ((5 : ℝ) / 3) ^ (2 * n - 10) := by
  interval_cases n <;> norm_num [Nat.factorial]

private lemma decay_large_of_six_le_of_lt_ten
    (a n : ℕ) (hn6 : 6 ≤ n) (hn10 : n < 10) (α : ℝ) (hα : 0 ≤ α)
    (hroot : α ^ n = a) (ha : 2 ^ (n - 1) ≤ a) :
    (16 : ℝ) * n * (n - 1) * a ^ 2 < Real.exp (shuniaDecay a n α) := by
  have hα53 := five_thirds_le_of_root_and_log_bound a n hn6 α hα hroot ha
  have hαpos : 0 < α := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5 / 3) hα53
  have haPos : (0 : ℝ) < a := by
    exact_mod_cast (lt_of_lt_of_le (Nat.pow_pos (by decide)) ha)
  have ha6 : ((2 ^ (n - 1) : ℕ) : ℝ) ^ 6 ≤ (a : ℝ) ^ 6 := by
    exact_mod_cast Nat.pow_le_pow_left ha 6
  have hαrem :
      ((5 : ℝ) / 3) ^ (2 * n - 10) ≤ α ^ (2 * n - 10) :=
    pow_le_pow_left₀ (by norm_num) hα53 _
  have hidentity :
      (a : ℝ) ^ 6 * α ^ (2 * n - 10) * α ^ 10 = (a : ℝ) ^ 8 := by
    rw [← hroot]
    simp only [← pow_mul]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hratio :
      ((16 : ℝ) * (10 ! : ℕ) * 4 ^ 10 * n ^ 11 * (n - 1)) * α ^ 10 <
        25 ^ 10 * (a : ℝ) ^ 8 := by
    calc
      ((16 : ℝ) * (10 ! : ℕ) * 4 ^ 10 * n ^ 11 * (n - 1)) * α ^ 10
          < (25 ^ 10 * ((2 ^ (n - 1) : ℕ) : ℝ) ^ 6 *
              ((5 : ℝ) / 3) ^ (2 * n - 10)) * α ^ 10 :=
        mul_lt_mul_of_pos_right (small_n_decay_numeric n hn6 hn10)
          (pow_pos hαpos 10)
      _ ≤ (25 ^ 10 * (a : ℝ) ^ 6 * α ^ (2 * n - 10)) * α ^ 10 := by
        gcongr
      _ = 25 ^ 10 * (a : ℝ) ^ 8 := by rw [← hidentity]; ring
  have hcross :
      ((16 : ℝ) * n * (n - 1) * (a : ℝ) ^ 2) * (10 ! : ℕ) *
          (4 ^ 10 * n ^ 10 * α ^ 10) <
        (25 : ℝ) ^ 10 * (a : ℝ) ^ 10 := by
    calc
      ((16 : ℝ) * n * (n - 1) * (a : ℝ) ^ 2) * (10 ! : ℕ) *
          (4 ^ 10 * n ^ 10 * α ^ 10)
          = (((16 : ℝ) * (10 ! : ℕ) * 4 ^ 10 * n ^ 11 * (n - 1)) *
              α ^ 10) * (a : ℝ) ^ 2 := by ring
      _ < (25 ^ 10 * (a : ℝ) ^ 8) * (a : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right hratio (pow_pos haPos 2)
      _ = (25 : ℝ) ^ 10 * (a : ℝ) ^ 10 := by ring
  let L : ℝ := (25 : ℝ) / 4 * a / (n * α)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hLpow :
      L ^ 10 = (25 : ℝ) ^ 10 * (a : ℝ) ^ 10 / (4 ^ 10 * n ^ 10 * α ^ 10) := by
    dsimp [L]
    field_simp
  have hterm :
      (16 : ℝ) * n * (n - 1) * a ^ 2 < L ^ 10 / (10 ! : ℕ) := by
    rw [hLpow]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (10 ! : ℕ))).2
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ 10 * n ^ 10 * α ^ 10)).2
    exact hcross
  have hLdecay : L ≤ shuniaDecay a n α :=
    decay_lower_bound_of_six_le a n hn6 α hα hroot ha
  have hdecay0 : 0 ≤ shuniaDecay a n α := hL0.trans hLdecay
  calc
    (16 : ℝ) * n * (n - 1) * a ^ 2
        < L ^ 10 / (10 ! : ℕ) := hterm
    _ ≤ shuniaDecay a n α ^ 10 / (10 ! : ℕ) := by gcongr
    _ ≤ Real.exp (shuniaDecay a n α) :=
      Real.pow_div_factorial_le_exp (x := shuniaDecay a n α) hdecay0 10

private lemma norm_one_add_mul_stdAddChar_sq_le
    (n : ℕ) [NeZero n] (α : ℝ) (hα : 0 ≤ α) (t : ZMod n) (ht : t ≠ 0) :
    ‖1 + (α : ℂ) * ZMod.stdAddChar t‖ ^ 2 ≤
      (1 + α) ^ 2 * shuniaQSq n α := by
  have hchord := four_div_le_norm_one_sub_stdAddChar n t ht
  have hchord_sq :
      (16 : ℝ) / n ^ 2 ≤ ‖(1 : ℂ) - ZMod.stdAddChar t‖ ^ 2 := by
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 / n) hchord 2
    calc
      (16 : ℝ) / n ^ 2 = ((4 : ℝ) / n) ^ 2 := by ring
      _ ≤ ‖(1 : ℂ) - ZMod.stdAddChar t‖ ^ 2 := hsquare
  rw [norm_one_add_mul_stdAddChar_sq]
  calc
    (1 + α) ^ 2 - α * ‖(1 : ℂ) - ZMod.stdAddChar t‖ ^ 2
        ≤ (1 + α) ^ 2 - α * ((16 : ℝ) / n ^ 2) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hchord_sq hα) _
    _ = (1 + α) ^ 2 * shuniaQSq n α := by
      rw [shuniaQSq]
      have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
      have hα1 : (1 + α : ℝ) ≠ 0 := by positivity
      field_simp

private lemma norm_one_add_mul_stdAddChar_even_pow_le
    (a n : ℕ) [NeZero n] (α : ℝ) (hα : 0 ≤ α) (t : ZMod n) (ht : t ≠ 0) :
    ‖1 + (α : ℂ) * ZMod.stdAddChar t‖ ^ (2 * a * n) ≤
      (1 + α) ^ (2 * a * n) * shuniaQSq n α ^ (a * n) := by
  have hsquare := norm_one_add_mul_stdAddChar_sq_le n α hα t ht
  have hpow := pow_le_pow_left₀ (sq_nonneg ‖1 + (α : ℂ) * ZMod.stdAddChar t‖)
    hsquare (a * n)
  calc
    ‖1 + (α : ℂ) * ZMod.stdAddChar t‖ ^ (2 * a * n) =
        (‖1 + (α : ℂ) * ZMod.stdAddChar t‖ ^ 2) ^ (a * n) := by
      simpa [mul_assoc] using
        (pow_mul ‖1 + (α : ℂ) * ZMod.stdAddChar t‖ 2 (a * n))
    _ ≤ ((1 + α) ^ 2 * shuniaQSq n α) ^ (a * n) := hpow
    _ = (1 + α) ^ (2 * a * n) * shuniaQSq n α ^ (a * n) := by
      rw [mul_pow]
      congr 1
      simpa [mul_assoc] using (pow_mul (1 + α) 2 (a * n)).symm

/-- The relative Fourier-error factor at the exponent `2 * a * n`. -/
private noncomputable def shuniaError (a n : ℕ) (α : ℝ) : ℝ :=
  ((n - 1 : ℕ) : ℝ) * shuniaQSq n α ^ (a * n)

private lemma norm_shuniaScaledCoeff_sub_mainTerm_at_K_le
    (a n : ℕ) [NeZero n] (α : ℝ) (hroot : α ^ n = a) (hα : 0 ≤ α)
    (i : ZMod n) :
    ‖shuniaScaledCoeff a n (2 * a * n) α i - shuniaMainTerm n (2 * a * n) α‖ ≤
      ‖(n : ℂ)⁻¹‖ * (1 + α) ^ (2 * a * n) * shuniaError a n α := by
  refine (norm_shuniaScaledCoeff_sub_mainTerm_le_sum
    a n (2 * a * n) α hroot i).trans ?_
  have hsum :
      ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
          ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ^ (2 * a * n) ≤
        ((n - 1 : ℕ) : ℝ) *
          ((1 + α) ^ (2 * a * n) * shuniaQSq n α ^ (a * n)) := by
    calc
      ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
          ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ^ (2 * a * n)
          ≤ ∑ _t ∈ (Finset.univ.erase (0 : ZMod n)),
            ((1 + α) ^ (2 * a * n) * shuniaQSq n α ^ (a * n)) := by
        apply Finset.sum_le_sum
        intro t ht
        exact norm_one_add_mul_stdAddChar_even_pow_le a n α hα (-t)
          (neg_ne_zero.mpr (Finset.ne_of_mem_erase ht))
      _ = ((n - 1 : ℕ) : ℝ) *
          ((1 + α) ^ (2 * a * n) * shuniaQSq n α ^ (a * n)) := by simp
  calc
    ‖(n : ℂ)⁻¹‖ * ∑ t ∈ (Finset.univ.erase (0 : ZMod n)),
        ‖1 + (α : ℂ) * ZMod.stdAddChar (-t)‖ ^ (2 * a * n)
        ≤ ‖(n : ℂ)⁻¹‖ * (((n - 1 : ℕ) : ℝ) *
          ((1 + α) ^ (2 * a * n) * shuniaQSq n α ^ (a * n))) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖(n : ℂ)⁻¹‖ * (1 + α) ^ (2 * a * n) * shuniaError a n α := by
      rw [shuniaError]
      ring

end Nat
