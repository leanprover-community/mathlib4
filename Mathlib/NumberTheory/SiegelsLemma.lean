/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Laura Capuano, Amos Turchet
-/
import Mathlib.Analysis.Matrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Pi.Interval

/-!
# Siegel's Lemma, first version for ℤ

In this file we introduce and prove Siegel's Lemma in its most basic version. This is a fundamental
tool in diophantine approximation and transcendency and says that there exists a "small" integral
non-zero solution of a non-trivial overdetermined system of linear equations with integer
coefficients.

## Notation

 - `‖_‖ ` : Matrix.seminormedAddCommGroup is the sup norm, the maximum of the absolute values of
 the entries of the matrix

## References

See [M. Hindry and J. Silverman, Diophantine Geometry: an Introduction][hindrysilverman00] .
-/

/- We set ‖⬝‖ to be Matrix.seminormedAddCommGroup  -/
attribute [local instance] Matrix.seminormedAddCommGroup

open Finset

namespace Int.Matrix

variable {m : Type*}  {n : Type*}
/-- The definition of ‖⬝‖ for integral matrixes -/
lemma sup_sup_norm_def [Fintype m] [Fintype n] (A : Matrix m n ℤ) :
    ‖A‖ = (sup univ fun b ↦ sup univ fun b' ↦ (A b b').natAbs) := by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def, ← NNReal.coe_natCast, NNReal.coe_inj,]
  rw [comp_sup_eq_sup_comp_of_is_total Nat.cast Nat.mono_cast
    (by simp only [bot_eq_zero', CharP.cast_eq_zero])]
  congr
  rw [Function.comp_def]
  ext; congr
  rw [comp_sup_eq_sup_comp_of_is_total Nat.cast Nat.mono_cast
    (by simp only [bot_eq_zero', CharP.cast_eq_zero])]
  congr; ext; congr;
  rw [Function.comp_apply, NNReal.natCast_natAbs]

/-- The norm of an integral matrix is the cast of a natural number -/
lemma norm_eq_NatCast [Fintype m] [Fintype n] (A : Matrix m n ℤ) :
    ∃ (a : ℕ), ‖A‖=↑a := by
  use sup univ fun b ↦ sup univ fun b' ↦ (A b b').natAbs
  exact sup_sup_norm_def A

/-- The norm of a non-singular integral matrix is a positive natural number-/
lemma one_le_norm_of_nonzero [Fintype m] [Fintype n] (A : Matrix m n ℤ) (hA_nezero : A ≠ 0) (a : ℕ)
    (h_norm_int : ‖A‖ = ↑a) : 1 ≤ a := by
  convert_to 0 < ( a : ℝ )
  · simp only [Nat.cast_pos]
    exact Nat.succ_le
  rw [← h_norm_int]
  exact norm_pos_iff'.mpr hA_nezero

end Int.Matrix

open Matrix

variable (m n a : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) (hn : m < n)
(hm : 0 < m)

--Some definitions and relative properties

local notation3 "e" => m / ((n : ℝ ) - m) --exponent
local notation3 "B" => Nat.floor (((n : ℝ) * ‖A‖) ^ e)
-- B' is the vector with all components = B
local notation3 "B'" => fun _ : Fin n => (B  : ℤ)
-- T is the box [0 B]^n
local notation3 "T" =>  Finset.Icc 0 B'


local notation3  "P" => fun i : Fin m => (∑ j : Fin n, B * posPart (A i j))
local notation3  "N" => fun i : Fin m =>  (∑ j : Fin n, B * (- negPart (A i j)))
   -- S is the box where the image of T goes
local notation3  "S" => Finset.Icc N P

section preparation

--In order to apply Pigeohole we need:  (1) ∀ v ∈  T, (A.mulVec v) ∈  S and (2) S.card < T.card

--(1)

private lemma image_T_subset_S : ∀ v ∈ T, (A.mulVec v) ∈ S := by
  intro v hv
  rw [Finset.mem_Icc] at hv
  rw [Finset.mem_Icc]
  rw [Matrix.mulVec_def] --unfolds def of MulVec
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ --this gives 2 goals
  all_goals simp only [mul_neg]
  all_goals gcongr (∑ _ : Fin n, ?_) with j _ -- gets rid of sums
  all_goals rw [← mul_comm (v j)] -- moves A i j to the right of the products
  all_goals by_cases hsign : 0 ≤ A i j   --we have to distinguish cases: we have now 4 goals
  ·  rw [negPart_eq_zero.2 hsign]
     exact mul_nonneg (hv.1 j) hsign
  ·  rw [not_le] at hsign
     rw [negPart_eq_neg.2 (le_of_lt hsign)]
     simp only [mul_neg, neg_neg]
     exact mul_le_mul_of_nonpos_right (hv.2 j) (le_of_lt hsign)
  ·  rw [posPart_eq_self.2  hsign]
     exact mul_le_mul_of_nonneg_right (hv.2 j) hsign
  ·  rw [not_le] at hsign
     rw [posPart_eq_zero.2 (le_of_lt hsign)]
     exact mul_nonpos_of_nonneg_of_nonpos (hv.1 j) (le_of_lt hsign)

end preparation
