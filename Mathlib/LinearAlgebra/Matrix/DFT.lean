/-
Copyright (c) 2020 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
-- import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
-- import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# Discrete Fourier Transform (DFT) Matrix and DFT of a (finite) sequence

This file defines the `dft` opertaion on a sequence (also a vecotr) and the DFT operation matrix

## Main definitions

 - `dft v`: given a sequence (v : (Fin n) → ℂ) we can transform it into a sequence (V : (Fin n) → ℂ)
 such that
 $$ V [p] = ∑_{k = 0}^{N - 1} e^{-j*2πkp/n} v [k] $$
 - `idft V` : given a sequence (V : (Fin n) → ℂ) we can transform it into a sequence
 (v : (Fin n) → ℂ)
such that
$$ v [k] = ¼{1}{N}∑_{p = 0}^{n - 1} e^{j*2πkp/N} v [p] $$
- `Wₙ` : the dft matrix with the `k, p` entry equal to
$$ Wₙ[k, p] = e^{-j2πkp/n} $$
- `Wₙ⁻¹` : the idft matrix with the `k, p` entry equal to
$$ Wₙ[k, p] = (1/N) * e^{j2πkp/n} $$


## Main results

- `dft v = Wₙ v` : the dft operation on a sequence is the same as the dft matrix applied to the
vector
- `idft V = Wₙ⁻¹ V` : the idft operation on a sequence is the same as the idft matrix applied to the
vector
- `dft (idft v) = dft ( idft v) = v` the dft and idft operations are inverses
- `Wₙ = vandermonde (w)` : the dft matrix is vandermonde with `w` being the first row of the dft
matrix
- `circulant t = Wₙ⁻¹ ⬝ diagonal (dft t) ⬝ Wₙ` : a circulant matrix is diagonalizable by the dft and
idft matrix pair.

-/

namespace DFT


open Complex Matrix BigOperators Finset Real

variable (n : ℕ) [NeZero n]

noncomputable def dft (v : (Fin n) → ℂ) : (Fin n) → ℂ :=
fun k : Fin n =>  ∑ p : (Fin n),  (Complex.exp (2 * π * I * k * p / n)) * (v p)

noncomputable def idft  (V : (Fin n) → ℂ) : (Fin n) → ℂ :=
fun p : Fin n =>  ∑ k : (Fin n),  ((Complex.exp (-2 * π * I * p * k / n))/ n) * (V k)

noncomputable def Wₙ  : Matrix (Fin n) (Fin n) ℂ :=
Matrix.of (fun (k p : Fin n) => Complex.exp (2 * π * I * k * p / n))

-- @[simp]
lemma Wₙ_apply (k p: Fin n) : Wₙ n k p = exp (2 * π * I * k * p / n) := rfl

lemma mod_eq_mod_neg (m a : ℤ) : Int.mod (-a) m = -Int.mod (a) m := by
  rw [Int.mod_def, Int.mod_def, Int.neg_div, neg_sub', mul_neg, sub_neg_eq_add]

lemma cexp_sub_ne_one {m : ℕ} [NeZero m](k p : Fin m) (h : ¬(k = p)) :
    Complex.exp (2 * π * I * (k - p) / m) ≠ 1 := by
  by_contra hg
  rw [Complex.exp_eq_one_iff] at hg
  obtain ⟨z, hz⟩ := hg
  rw [mul_div_assoc, mul_comm (z:ℂ) _, (mul_right_inj' two_pi_I_ne_zero),
      (div_eq_iff_mul_eq (Nat.cast_ne_zero.2 (NeZero.ne _)))] at hz
  norm_cast at hz
  apply_fun ( Int.mod · m) at hz
  simp only [Int.mul_mod_left, Int.subNatNat_eq_coe] at hz
  by_cases h1 : p ≤ k
  · rw [Int.mod_eq_of_lt, eq_comm, sub_eq_zero] at hz
    norm_cast at hz
    apply h (Fin.ext hz)
    simp only [sub_nonneg, Nat.cast_le, Fin.val_fin_le]
    apply (h1)
    rw [← Nat.cast_sub]
    norm_cast
    apply Nat.sub_lt_right_of_lt_add
    exact_mod_cast h1
    apply (Nat.lt_add_right _ _ _ (Fin.is_lt _))
    exact_mod_cast h1
  · push_neg at h1
    rw [ ← neg_sub, mod_eq_mod_neg, eq_comm, neg_eq_zero] at hz
    rw [Int.mod_eq_of_lt, sub_eq_zero, eq_comm] at hz
    norm_cast at hz
    apply h (Fin.ext hz)
    simp only [neg_sub, sub_nonneg, Nat.cast_le, Fin.val_fin_le]
    apply le_of_lt
    apply (h1)
    rw [← Nat.cast_sub]
    norm_cast
    apply Nat.sub_lt_right_of_lt_add
    apply le_of_lt
    exact_mod_cast h1
    apply (Nat.lt_add_right _ _ _ (Fin.is_lt _))
    apply le_of_lt h1

noncomputable def invWₙ : Invertible (Wₙ n) := by
  apply invertibleOfRightInverse  _ (of (fun (k p : Fin n) => exp (-2 * π * I * k * p / n) / n)) _
  funext k p
  -- rw [mul_apply]
  simp_rw [mul_apply, Wₙ_apply, of_apply, mul_div_assoc', ← Complex.exp_add]
  by_cases h : k = p
  · rw [h, one_apply_eq]
    ring_nf
    simp_rw [Complex.exp_zero, Finset.sum_const, card_fin, nsmul_eq_mul]
    apply mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 (NeZero.ne _))
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
    exact (Nat.cast_ne_zero.2 (NeZero.ne _))
    apply cexp_sub_ne_one _ _ h

theorem dftMatrix_inv  [Invertible (Wₙ n)] :
    ⅟(Wₙ n) = of (fun (k p : Fin n) => exp ( -2 * π * I * k * p / n) / n) := by
  letI := (invWₙ n)
  convert (rfl : ⅟(Wₙ n) = _)

lemma iWₙ_apply (k p : Fin n) : (Wₙ n)⁻¹ k p = exp (-2 * π * I * k * p / n)/n := by
  letI := invWₙ n
  rw [← Matrix.invOf_eq_nonsing_inv (Wₙ n), dftMatrix_inv, of_apply]

theorem dft_eq_Wₙ_mul (v : Fin n → ℂ) : dft n v = mulVec (Wₙ n) v := by
  funext r
  simp only [dft, mulVec, dotProduct, Wₙ_apply]

theorem idft_eq_iWₙ_mul (V : Fin n → ℂ ) : idft n V = mulVec (Wₙ n)⁻¹ V := by
  funext r
  simp only [idft, mulVec, dotProduct, iWₙ_apply]

theorem idft_dft  (v : Fin n → ℂ) : idft n (dft n v) = v := by
  letI := invWₙ n
  rw [dft_eq_Wₙ_mul, idft_eq_iWₙ_mul, mulVec_mulVec, inv_mul_of_invertible, one_mulVec]

theorem dft_idft  (V : Fin n → ℂ) : dft  n (idft n V) = V := by
  letI := invWₙ n
  rw [dft_eq_Wₙ_mul, idft_eq_iWₙ_mul, mulVec_mulVec, mul_inv_of_invertible, one_mulVec]

theorem Wₙ_conjTranspose_eq_iWₙ :  (Wₙ n)⁻¹ = ((1:ℂ)/n) • (Wₙ n)ᴴ := by
  funext x y
  simp only [iWₙ_apply, smul_apply, conjTranspose_apply, Wₙ_apply, smul_eq_mul]
  rw [star_def, ← Complex.exp_conj, ← div_mul_comm, mul_one, div_left_inj', ← star_def]
  simp only [star_div', star_natCast, star_mul', conj_I, star_def, conj_ofReal, map_ofNat, neg_mul,
    mul_neg]
  ring_nf
  exact (Nat.cast_ne_zero.2 (NeZero.ne _))

lemma Wₙ_transpose_eq_Wₙ : (Wₙ n)ᵀ = Wₙ n := by
  funext a b
  simp only [transpose_apply, Wₙ_apply]
  ring_nf

def shiftk (N : ℕ) (k : Fin N) : (Fin N → Fin N) := fun n : (Fin N) => (n - k)

def shiftk_equiv {N: ℕ} [hN : NeZero N] (k : Fin N) : (Fin N) ≃ (Fin N) where
  toFun := shiftk N k
  invFun := shiftk N (-k)
  left_inv := by intro x;  simp only [shiftk, sub_neg_eq_add, sub_add_cancel]
  right_inv := by intro x; simp only [shiftk, sub_neg_eq_add, add_sub_cancel]

theorem circulant_dft  (t : Fin n → ℂ) :
    circulant t = (Wₙ n)⁻¹ ⬝ (diagonal ( dft n t)) ⬝ (Wₙ n) := by
  letI := invWₙ n
  apply_fun ((Wₙ n) ⬝ ·)
  dsimp
  rw [Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible]
  funext a b
  simp only [diagonal_mul, mul_apply, circulant_apply, Wₙ_apply, diagonal_apply, dft]
  -- by_cases h : a = b
  simp_rw [ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
    ← mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _), ← Complex.exp_neg]
  rw [mul_comm]
  simp_rw [mul_sum, ← mul_assoc, ← Complex.exp_add, neg_add_eq_sub, ← sub_div, mul_assoc (2*π*I),
    ← mul_sub]
  let f := fun x : (Fin n) => (Complex.exp ( 2*π * I * (a * (x))/n)) * (t (x))
  have h1 : ∀ (x : Fin n), (shiftk_equiv (-b)) x = x - b := by sorry
  have h2 : ∀ (x : Fin n), ((x:ℂ) - (b:ℂ)) = (shiftk_equiv (-b)) x := by sorry
  simp_rw [← h1, h2]
  rw [Equiv.sum_comp (shiftk_equiv (-b)) f]
  sorry
  -- apply Matrix.mul_right_injective_of_invertible (Wₙ n)

  -- rw [Equiv.sum_comp (Equiv.refl _) f]



-- theorem dft_eq_vandermonde :
--     (Wₙ n) = vandermonde (fun (k: Fin n) => exp (-2 * π * I * k / n)) :=  sorry

end DFT
