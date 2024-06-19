/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Laura Capuano, Amos Turchet
-/
import Mathlib.Analysis.Matrix
import Mathlib.Data.Pi.Interval
import Mathlib.tactic.rify

/-!
# Siegel's Lemma

In this file we introduce and prove Siegel's Lemma in its most basic version. This is a fundamental
tool in diophantine approximation and transcendency and says that there exists a "small" integral
non-zero solution of a non-trivial underdetermined system of linear equations with integer
coefficients.

## Main results

- `exists_ne_zero_int_vec_norm_le`: Given a non-singular `m × n` matrix `A` with `m < n` the linear
system it determines has a non-zero integer solution `t` with
`‖t‖ ≤ ((n * ‖A‖) ^ ((m : ℝ) / (n - m)))`

## Notation

 - `‖_‖ ` : Matrix.seminormedAddCommGroup is the sup norm, the maximum of the absolute values of
 the entries of the matrix

## References

See [M. Hindry and J. Silverman, Diophantine Geometry: an Introduction][hindrysilverman00].
-/

/- We set ‖⬝‖ to be Matrix.seminormedAddCommGroup  -/
attribute [local instance] Matrix.seminormedAddCommGroup

open Matrix Finset

section generalMatrices

variable {m n α : Type*} [Fintype m] [Fintype n] [SeminormedAddCommGroup α]

lemma exists_entry_norm_eq_norm_Matrix [Nonempty m] [Nonempty n] (A : Matrix m n α) :
    ∃ (i : m) (j : n), ‖A‖ = ‖A i j‖₊ := by
  simp only [norm_eq_sup_sup_nnnorm]
  rcases Finset.exists_mem_eq_sup univ univ_nonempty (fun i => univ.sup fun j => ‖A i j‖₊)
    with ⟨i, hi⟩
  use i
  rcases Finset.exists_mem_eq_sup univ univ_nonempty (fun j => ‖A i j‖₊) with ⟨j, hj⟩
  use j
  rw [hi.2, hj.2]

end generalMatrices

namespace Int.Matrix

variable (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) (hn : m < n)
(hm : 0 < m)

--Some definitions and relative properties

local notation3 "e" => m / ((n : ℝ) - m) --exponent
local notation3 "B" => Nat.floor (((n : ℝ) * ‖A‖) ^ e)
-- B' is the vector with all components = B
local notation3 "B'" => fun _ : Fin n => (B : ℤ)
-- T is the box [0 B]^n
local notation3 "T" =>  Finset.Icc 0 B'


local notation3  "P" => fun i : Fin m => (∑ j : Fin n, B * posPart (A i j))
local notation3  "N" => fun i : Fin m =>  (∑ j : Fin n, B * (- negPart (A i j)))
-- S is the box where the image of T goes
local notation3  "S" => Finset.Icc N P

section preparation

/-  In order to apply Pigeohole we need:
# Step 1  ∀ v ∈  T, (A.mulVec v) ∈  S
and
# Step 2 S.card < T.card

-/

-- # Step 1: ∀ v ∈  T, (A.mulVec v) ∈  S


private lemma image_T_subset_S : ∀ v ∈ T, (A.mulVec v) ∈ S := by
  intro v hv
  rw [mem_Icc] at hv
  rw [mem_Icc]
  have mulVec_def : A.mulVec v =
      fun i => Finset.sum univ fun (j : (Fin n)) => A i j * v j := by rfl
  rw [mulVec_def] -- unfold def of MulVec
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ -- 2 goals
  all_goals simp only [mul_neg]
  all_goals gcongr (∑ _ : Fin n, ?_) with j _ -- get rid of sums
  all_goals rw [← mul_comm (v j)] -- move A i j to the right of the products
  all_goals by_cases hsign : 0 ≤ A i j   --we have to distinguish cases: we have now 4 goals
  · rw [negPart_eq_zero.2 hsign]
    exact mul_nonneg (hv.1 j) hsign
  · rw [not_le] at hsign
    rw [negPart_eq_neg.2 (le_of_lt hsign)]
    simp only [mul_neg, neg_neg]
    exact mul_le_mul_of_nonpos_right (hv.2 j) (le_of_lt hsign)
  · rw [posPart_eq_self.2  hsign]
    exact mul_le_mul_of_nonneg_right (hv.2 j) hsign
  · rw [not_le] at hsign
    rw [posPart_eq_zero.2 (le_of_lt hsign)]
    exact mul_nonpos_of_nonneg_of_nonpos (hv.1 j) (le_of_lt hsign)

--# Preparation for Step 2

private lemma card_T_eq : (T).card = (B+1)^n := by
   rw [Pi.card_Icc 0 B']
   simp only [Pi.zero_apply, Int.card_Icc, sub_zero, Int.toNat_ofNat_add_one, prod_const, card_fin]

variable  (hA : A ≠ 0 )

--This lemma is necessary to be able to apply the formula (Icc a b).card = b + 1 - a
private lemma N_le_P_add_one : ∀ i : Fin m, N i ≤ P i + 1 := by
  intro i
  calc N i ≤ 0 := by
              apply Finset.sum_nonpos
              intro j _
              simp only [mul_neg, Left.neg_nonpos_iff]
              exact mul_nonneg (Nat.cast_nonneg B) (negPart_nonneg (A i j))
         _ ≤ P i + 1 := by
              apply le_trans (Finset.sum_nonneg _) (Int.le_add_one (le_refl P i))
              intro j _
              exact mul_nonneg (Nat.cast_nonneg B) (posPart_nonneg (A i j))

private lemma card_S_eq : (Finset.Icc N P).card = (∏ i : Fin m, (P i - N i + 1)):= by
  rw [Pi.card_Icc N P, Nat.cast_prod]
  congr
  ext i
  rw [Int.card_Icc_of_le (N i) (P i) (N_le_P_add_one m n A i)]
  exact add_sub_right_comm (P i) 1 (N i)

private lemma one_le_norm_A_of_nezero : 1 ≤ ‖A‖ := by
  by_contra h
  apply lt_of_not_le at h
  apply hA
  ext i j
  simp only [zero_apply]
  rw [norm_lt_iff Real.zero_lt_one] at h
  specialize h i j
  rw [Int.norm_eq_abs, ← Int.cast_abs] at h
  norm_cast at h
  rw [Int.abs_lt_one_iff] at h
  exact h

-- # Step 2: S.card < T.card

open Real Nat

private lemma card_S_lt_card_T : (S).card < (T).card := by
  zify
  rw [card_T_eq, card_S_eq]
  rify
  calc
  ∏ x : Fin m, (∑ x_1 : Fin n, ↑B * ↑(A x x_1)⁺ - ∑ x_1 : Fin n, ↑B * -↑(A x x_1)⁻ + 1)
    ≤ (n * ‖A‖ * B + 1) ^ m := by
      rw [← Fin.prod_const m (n *  ‖A‖ * B + 1)]
      apply Finset.prod_le_prod
      all_goals intro i _
      · obtain hp:= N_le_P_add_one m n A i
        rify at hp
        linarith [hp]
      · simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add, add_le_add_iff_right]
        rw [← Finset.sum_add_distrib]
        have h1 :  ↑n * ‖A‖ * ↑B = ∑ _ : Fin n, ‖A‖ * ↑B := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
        rw [h1]
        gcongr with j _
        simp_rw [← mul_add, ← Int.cast_add, posPart_add_negPart (A i j), mul_comm]
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg B)
        rw [Int.cast_abs]
        exact norm_entry_le_entrywise_sup_norm A
  _  ≤ (n * ‖A‖) ^ m * (B + 1) ^ m := by
        rw [← mul_pow]
        apply pow_le_pow_left (add_nonneg _ (zero_le_one' ℝ)) _
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg A)) (Nat.cast_nonneg B)
        rw [mul_add]
        simp only [mul_one, add_le_add_iff_left]
        apply Left.one_le_mul_of_le_of_le
            (by exact_mod_cast Nat.one_le_of_lt hn) _ (Nat.cast_nonneg n)
        exact one_le_norm_A_of_nezero m n A hA
  _ = ((n * ‖A‖) ^ ((m / ((n : ℝ) - m)))) ^ ((n : ℝ) - m)  * (B + 1) ^ m := by
        rw [mul_left_inj' (pow_ne_zero m (Nat.cast_add_one_ne_zero B))]
        rw [← rpow_mul (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg A)), ← Real.rpow_natCast]
        congr
        rw [div_mul_cancel₀]
        apply sub_ne_zero_of_ne
        norm_cast
        exact Nat.ne_of_lt' hn
  _ < (B + 1) ^ ((n : ℝ) - m) * (B + 1) ^ m := by
        rw [mul_lt_mul_right (pow_pos (Nat.cast_add_one_pos B) m)]
        apply rpow_lt_rpow
        · exact rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg A)) e
        · exact Nat.lt_floor_add_one ((n * ‖A‖) ^ e)
        · simp only [sub_pos, Nat.cast_lt]
          exact hn
  _ = (B + 1) ^ n := by
        rw [← rpow_natCast, ← rpow_add, ← rpow_natCast]
        congr
        simp only [sub_add_cancel]
        exact Nat.cast_add_one_pos B

--end (2)

end preparation

theorem exists_ne_zero_int_vec_norm_le  (hA_nezero : A ≠ 0)  : ∃ (t : Fin n → ℤ), t ≠ 0 ∧
    A.mulVec t = 0 ∧ ‖t‖ ≤ ((n * ‖A‖)^((m : ℝ) / (n - m))) := by
  --Pigeonhole
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (card_S_lt_card_T m n A hn hA_nezero) (image_T_subset_S m n A)
    with ⟨x, hxT, y, hyT, hneq, hfeq⟩
  use x-y
  -- proof that x - y ≠ 0
  refine ⟨sub_ne_zero.mpr hneq, ?_, ?_⟩
  -- x-y is a solution
  simp only [mulVec_sub, sub_eq_zero, hfeq]
  ---Inequality
  have n_mul_norm_A_pow_e_nonneg : 0 ≤ (n * ‖A‖) ^ e :=
      Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_of_lt (norm_pos_iff'.mpr hA_nezero))) e
  rw [← norm_col, norm_le_iff n_mul_norm_A_pow_e_nonneg]
  intro i j
  rw [Finset.mem_Icc] at hyT
  rw [Finset.mem_Icc] at hxT
  simp only [col_apply, Pi.sub_apply, ge_iff_le]
  rw [Int.norm_eq_abs, ← Int.cast_abs]
  refine le_trans ?_ (Nat.floor_le n_mul_norm_A_pow_e_nonneg)
  norm_cast
  rw [abs_le]
  constructor
  · simp only [neg_le_sub_iff_le_add]
    apply le_trans (hyT.2 i)
    norm_cast
    simp only [le_add_iff_nonneg_left]
    exact hxT.1 i
  · simp only [ tsub_le_iff_right]
    apply le_trans (hxT.2 i)
    norm_cast
    simp only [le_add_iff_nonneg_right]
    exact hyT.1 i

    end Int.Matrix
