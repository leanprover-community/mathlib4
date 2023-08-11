/-
Copyright (c) 2020 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
-- import Mathlib.Algebra.BigOperators.Fin
-- import Mathlib.Algebra.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
-- import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
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


noncomputable def dft (n : ℕ) (v : (Fin n) → ℂ) : (Fin n) → ℂ :=
fun k : Fin n =>  ∑ p : (Fin n),  (Complex.exp (2 * π * I * k * p / n)) * (v p)

noncomputable def idft (n : ℕ) (V : (Fin n) → ℂ) : (Fin n) → ℂ :=
fun p : Fin n =>  ∑ k : (Fin n),  (Complex.exp (-2 * π * I * k * p / n)) * (V p) / n

noncomputable def Wₙ (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
Matrix.of (fun (k p : Fin n) => Complex.exp (2 * π * I * k * p / n))

noncomputable instance invWₙ : Invertible (Wₙ n) := by sorry

theorem dftMatrix_inv (n : ℕ) : (Wₙ n)⁻¹ =
    of (fun (k p : Fin n) => exp (2 * π * I * k * p / n) / n) := by sorry

theorem idft_dft (n : ℕ) (v : Fin n → ℂ) : idft n (dft n v) = v := by sorry

theorem dft_idft (n : ℕ) (V : Fin n → ℂ) : dft  n (idft n V) = V := by sorry

theorem circulant_dft (n : ℕ) (t : Fin n → ℂ) :
    circulant t = (Wₙ n)⁻¹ ⬝ (diagonal ( dft n t)) ⬝ (Wₙ n) := by sorry

theorem dft_eq_vandermonde (n: ℕ):
    (Wₙ n) = vandermonde (fun (k: Fin n) => exp (-2 * π * I * k / n)) :=  sorry

end DFT
