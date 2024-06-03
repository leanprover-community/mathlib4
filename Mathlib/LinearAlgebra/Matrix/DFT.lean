/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Algebra.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Discrete Fourier Transform (DFT) Matrix and DFT of a (finite) sequence

This file defines the `dft` operation on a sequence (also a vector) and the DFT operation matrix

## Main definitions

 - `dft n v`: given a sequence (v : Fin n → ℂ) we can transform it into a sequence (V : Fin n → ℂ )
 such that
 $$ V [p] = ∑_{k = 0}^{N - 1} e^{-i 2 π k p / n} v (k) $$
 - `idft n V` : given a sequence (V : Fin n → ℂ) we can transform it into a sequence
 (v : Fin n → ℂ)
such that
$$ v [k] = \frac{1}{N}∑_{p = 0}^{n - 1} e^{i 2 π k p / N} v [p] $$
- `dftMatrix n` : the n by n dft matrix with the `k, p` entry equal to
$$ dftMatrix[k, p] = e^{-i 2 π k p/n} $$
- `dftMatrixInv n` : the n by n the idft matrix with the `k, p` entry equal to
$$ dftMatrix[k, p] = (1/N) * e^{i 2 π k p / n} $$


## Main results

- `dft n v = dftMatrix n * v` : the dft operation on a sequence is the same as the dft matrix
  applied to the vector
- `idft n V = dftMatrixInv n * V` : the idft operation on a sequence is the same as the idft matrix
  applied to the vector
- `dft n (idft n v) = dft n (idft n v) = v` the dft and idft operations are inverses
- `dftMatrix n = vandermonde w` : the dft matrix is vandermonde with `w` being the first row of the
 dft matrix
- `circulant t = dftMatrixInv n⬝ diagonal (dft t) ⬝ dftMatrix n` : a circulant matrix is
diagonalizable by the dft and idft matrix pair.

-/

namespace DFT


open Complex Matrix BigOperators Finset Real

variable (n : ℕ)

/-- The DFT operation defined via a Sum -/
noncomputable def dft (v : Fin n → ℂ) : Fin n → ℂ :=
fun k : Fin n =>  ∑ p : Fin n,  (Complex.exp (2 * π * I * k * p / n)) * (v p)

/-- The IDFT operation defined via a Sum -/
noncomputable def idft  (V : Fin n → ℂ) : (Fin n) → ℂ :=
fun p : Fin n =>  ∑ k : Fin n,  ((Complex.exp (-2 * π * I * p * k / n))/ n) * (V k)

/-- The DFT Matrix -/
noncomputable def dftMatrix  : Matrix (Fin n) (Fin n) ℂ :=
Matrix.of (fun (k p : Fin n) => Complex.exp (2 * π * I * k * p / n))

lemma dftMatrix_apply (k p : Fin n) : dftMatrix n k p = exp (2 * π * I * k * p / n) := rfl

lemma mod_eq_mod_neg (m a : ℤ) : Int.mod (-a) m = -Int.mod (a) m := by
  rw [Int.mod_def, Int.mod_def, Int.neg_div, neg_sub', mul_neg, sub_neg_eq_add]

lemma cexp_sub_ne_one {m : ℕ} (k p : Fin m) (h : (k ≠ p)) :
    Complex.exp (2 * π * I * (k - p) / m) ≠ 1 := by
  by_cases hm : m = 0
  exfalso
  apply Fin.elim0 (by convert k; exact hm.symm)
  by_contra hg
  rw [Complex.exp_eq_one_iff] at hg
  obtain ⟨z, hz⟩ := hg
  rw [mul_div_assoc, mul_comm (z:ℂ) _, (mul_right_inj' two_pi_I_ne_zero),
      (div_eq_iff_mul_eq (Nat.cast_ne_zero.2 hm))] at hz
  norm_cast at hz
  apply_fun ( Int.mod · m) at hz
  simp only [Int.mul_mod_left, Int.subNatNat_eq_coe] at hz
  by_cases h1 : p ≤ k
  · rw [Int.mod_eq_of_lt, eq_comm, sub_eq_zero] at hz
    norm_cast at hz
    apply h (Fin.ext hz)
    simp only [sub_nonneg, Nat.cast_le, Fin.val_fin_le]
    exact h1
    rw [← Nat.cast_sub]
    norm_cast
    apply Nat.sub_lt_right_of_lt_add h1
    apply (Nat.lt_add_right _ _ _ (Fin.is_lt _))
    exact_mod_cast h1
  · push_neg at h1
    rw [ ← neg_sub, mod_eq_mod_neg, eq_comm, neg_eq_zero, Int.mod_eq_of_lt, sub_eq_zero,
      eq_comm] at hz
    norm_cast at hz
    apply h (Fin.ext hz)
    simp only [neg_sub, sub_nonneg, Nat.cast_le, Fin.val_fin_le]
    apply le_of_lt h1
    rw [← Nat.cast_sub]
    norm_cast
    apply Nat.sub_lt_right_of_lt_add (le_of_lt h1)
    apply (Nat.lt_add_right _ _ _ (Fin.is_lt _))
    apply le_of_lt h1

/-- The IDFT Matrix Invertible "def/instance"-/
noncomputable def invertible_dftMatrix : Invertible (dftMatrix n) := by
  apply invertibleOfRightInverse  _ (of (fun (k p : Fin n) => exp (-2 * π * I * k * p / n) / n)) _
  funext k p
  by_cases hn: n = 0
  apply False.elim $ Fin.elim0 (by convert k; exact hn.symm)
  simp_rw [mul_apply, dftMatrix_apply, of_apply, mul_div_assoc', ← Complex.exp_add]
  by_cases h : k = p
  · rw [h, one_apply_eq]
    ring_nf
    simp_rw [Complex.exp_zero, Finset.sum_const, card_fin, nsmul_eq_mul]
    apply mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hn)
  · rw [one_apply_ne h]
    have h1 : ∀ (x : Fin n), 2 * π * I * k * x / n +  (-2) * π * I * x * p / n  =
        (x : ℕ) * ((2*π * I * (k - p)) / n) := by intro x; ring
    simp_rw [h1, ← sum_div, div_eq_zero_iff, Complex.exp_nat_mul, Fin.sum_univ_eq_sum_range]
    left
    rw [geom_sum_eq, ← Complex.exp_nat_mul, div_eq_zero_iff]
    left
    rw [sub_eq_zero, Complex.exp_eq_one_iff]
    use (k - p)
    rw [mul_div_cancel', mul_comm, mul_eq_mul_right_iff]
    left
    simp_rw [Int.cast_sub, Int.cast_ofNat]
    exact (Nat.cast_ne_zero.2 hn)
    apply cexp_sub_ne_one _ _ h

/-- The IDFT Matrix -/
theorem dftMatrix_inv  [Invertible (dftMatrix n)] :
    ⅟(dftMatrix n) = of (fun (k p : Fin n) => exp ( -2 * π * I * k * p / n) / n) := by
  letI := (invertible_dftMatrix n)
  convert (rfl : ⅟(dftMatrix n) = _)

lemma idftMatrix_apply (k p : Fin n) : (dftMatrix n)⁻¹ k p = exp (-2 * π * I * k * p / n) / n := by
  letI := invertible_dftMatrix n
  rw [← Matrix.invOf_eq_nonsing_inv (dftMatrix n), dftMatrix_inv, of_apply]

/-- The DFT operation and DFT matrix applied to sequence/vector are tha same -/
theorem dft_eq_dftMatrix_mul (v : Fin n → ℂ) : dft n v = mulVec (dftMatrix n) v := by
  funext r
  simp only [dft, mulVec, dotProduct, dftMatrix_apply]

/-- The IDFT operation and IDFT matrix applied to sequence/vector are the same -/
theorem idft_eq_idftMatrix_mul (V : Fin n → ℂ ) : idft n V = mulVec (dftMatrix n)⁻¹ V := by
  funext r
  simp only [idft, mulVec, dotProduct, idftMatrix_apply]

/-- IDFT/DFT are bijective pair-/
theorem idft_dft  (v : Fin n → ℂ) : idft n (dft n v) = v := by
  letI := invertible_dftMatrix n
  rw [dft_eq_dftMatrix_mul, idft_eq_idftMatrix_mul, mulVec_mulVec, inv_mul_of_invertible,
    one_mulVec]

theorem dft_idft  (V : Fin n → ℂ) : dft  n (idft n V) = V := by
  letI := invertible_dftMatrix n
  rw [dft_eq_dftMatrix_mul, idft_eq_idftMatrix_mul, mulVec_mulVec, mul_inv_of_invertible,
    one_mulVec]

/-- The IDFT matrix is the scaled conjugate transpose of the DFT matrix-/
theorem dftMatrix_conjTranspose_eq_idftMatrix :
    (dftMatrix n)⁻¹ = ((1:ℂ) / n) • (dftMatrix n)ᴴ := by
  funext x y
  by_cases hn: n = 0
  apply False.elim $ Fin.elim0 (by convert x; exact hn.symm)
  simp only [idftMatrix_apply, smul_apply, conjTranspose_apply, dftMatrix_apply, smul_eq_mul]
  rw [star_def, ← Complex.exp_conj, ← div_mul_comm, mul_one, div_left_inj', ← star_def]
  simp only [star_div', star_natCast, star_mul', conj_I, star_def, conj_ofReal, map_ofNat, neg_mul,
    mul_neg]
  ring_nf
  exact (Nat.cast_ne_zero.2 hn)

/-- The DFT matrix is symmetric -/
lemma dftMatrix_transpose_eq_dftMatrix : (dftMatrix n)ᵀ = dftMatrix n := by
  funext a b
  simp only [transpose_apply, dftMatrix_apply]
  ring_nf

def shiftk (N : ℕ) (k : Fin N) : (Fin N → Fin N) := fun n : (Fin N) => (n - k)

def shiftk_equiv {N: ℕ} (k : Fin N) : (Fin N) ≃ (Fin N) where
  toFun := shiftk N k
  invFun := shiftk N (-k)
  left_inv := by
    intro x
    by_cases hn: N = 0
    apply False.elim $ Fin.elim0 (by convert x; exact hn.symm)
    letI := neZero_iff.2 hn
    simp only [shiftk, sub_neg_eq_add, sub_add_cancel]
  right_inv := by
    intro x
    by_cases hn: N = 0
    apply False.elim $ Fin.elim0 (by convert x; exact hn.symm)
    letI := neZero_iff.2 hn
    simp only [shiftk, sub_neg_eq_add, add_sub_cancel]

lemma cexp_shiftk_invariant (x a b : Fin n) :
    exp (2 * ↑π * I * (↑↑a * ((x:ℂ) - (b:ℂ))) / ↑n) =
    Complex.exp ((2*π*I)*(a*(shiftk_equiv (b) x))/n) := by
  by_cases hn: n = 0
  apply False.elim $ Fin.elim0 (by convert a; exact hn.symm)
  letI := neZero_iff.2 hn
  rw [Complex.exp_eq_exp_iff_exists_int]
  unfold shiftk_equiv shiftk
  simp only [sub_neg_eq_add, Equiv.coe_fn_mk]
  by_cases h : b ≤ x
  · use 0
    simp only [Int.cast_zero, zero_mul, add_zero]
    congr
    norm_cast
    rw [Int.subNatNat_of_le h]
    simp only [Fin.val_fin_le, Nat.cast_inj]
    apply ((@Fin.coe_sub_iff_le n x b).2 h).symm
  · push_neg at h
    use (-a)
    rw [mul_comm ((-a:ℤ):ℂ) (2*π*I), mul_div_assoc, mul_div_assoc, mul_div_assoc, ← mul_add,
      mul_right_inj', Int.cast_neg, Int.cast_ofNat, ← mul_div_assoc, div_eq_iff, add_mul,
      div_mul_cancel_of_invertible, neg_mul, ← sub_eq_add_neg, ← mul_sub, mul_eq_mul_left_iff]
    left
    rw [Fin.coe_sub, Nat.mod_eq, if_neg]
    norm_cast
    rw [← Nat.add_sub_assoc, Int.subNatNat_sub, add_comm n _, Int.subNatNat_add_add]

    -- Clear plethora of side goals
    apply (le_of_lt (Nat.lt_add_left _ _ _ (Fin.is_lt _)))
    apply (le_of_lt (Fin.is_lt _))
    push_neg
    intro _
    rw [← Nat.add_sub_assoc]
    apply Nat.sub_lt_left_of_lt_add
    apply (le_of_lt (Nat.lt_add_left _ _ _ (Fin.is_lt _)))

    apply Nat.add_lt_add_right h _
    apply (le_of_lt (Fin.is_lt _))
    apply (Nat.cast_ne_zero.2 (NeZero.ne _))
    apply (mul_ne_zero (mul_ne_zero two_ne_zero _) I_ne_zero)
    exact_mod_cast pi_ne_zero

/-- A circulant matrix is diagonalized by the IDFT DFT matrix pair -/
theorem circulant_dft  (t : Fin n → ℂ) :
    circulant t = (dftMatrix n)⁻¹ ⬝ (diagonal ( dft n t)) ⬝ (dftMatrix n) := by
  letI := invertible_dftMatrix n
  apply_fun ((dftMatrix n) ⬝ ·)
  dsimp
  rw [Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible]
  funext a b
  by_cases hn : n = 0
  apply False.elim $ Fin.elim0 (by convert a; exact hn.symm)
  letI := neZero_iff.2 hn
  simp only [diagonal_mul, mul_apply, circulant_apply, dftMatrix_apply, diagonal_apply, dft]
  simp_rw [ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
    ← mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _), ← Complex.exp_neg]
  rw [mul_comm]
  simp_rw [mul_sum, ← mul_assoc, ← Complex.exp_add, neg_add_eq_sub, ← sub_div, mul_assoc (2*π*I),
    ← mul_sub]
  let f := fun x : (Fin n) => (Complex.exp ( (2* π * I) * (a * (x))/n)) * (t (x))
  have h1 : ∀ (x : Fin n), (shiftk_equiv b) x = x - b := by
    intro x; unfold shiftk_equiv shiftk; simp only [sub_neg_eq_add, Equiv.coe_fn_mk]
  have h2 : ∀ (x : Fin n), Complex.exp (2 * ↑π * I * (↑↑a * ((x:ℂ) - (b:ℂ))) / ↑n) =
    Complex.exp ((2 * π * I) * (a * (shiftk_equiv b x) ) / n) := by
    intro x; apply cexp_shiftk_invariant n x a b
  simp_rw [← h1, h2]
  rw [Equiv.sum_comp (shiftk_equiv b) f]
  apply Matrix.mul_right_injective_of_invertible (dftMatrix n)

/-- The DFT matrix is a vandermonde matrix -/
theorem dftMatrix_eq_vandermonde :
    (dftMatrix n) = vandermonde (fun (k: Fin n) => exp (2 * π * I * k / n)) :=  by
  funext k n
  simp only [neg_mul, vandermonde_apply, dftMatrix_apply]
  rw [← Complex.exp_nat_mul]
  congr
  ring

/-- The IDFT matrix is a vandermonde matrix -/
theorem idftMatrix_eq_vandermonde :
    (dftMatrix n)⁻¹ = (1/(n:ℂ)) • vandermonde (fun (k: Fin n) => (exp (-2 * π * I * k / n))) :=  by
  funext k n
  simp only [neg_mul, vandermonde_apply, idftMatrix_apply, smul_apply, smul_eq_mul]
  rw [div_mul_comm, mul_one, ← Complex.exp_nat_mul]
  congr
  ring

end DFT
