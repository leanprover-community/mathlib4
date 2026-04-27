/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Polynomial identities from evaluation at invertible matrices

We prove `MvPolynomial.eq_of_eval_eq_on_gl`: two polynomials in `MvPolynomial (m × m) k` over an
infinite field `k` are equal if their evaluations agree at every invertible matrix. The proof
uses that the set of invertible matrices is Zariski-dense in `Matrix m m k`.
-/

@[expose] public section

namespace MvPolynomial

/-- Two polynomials in `MvPolynomial (m × m) k` over an infinite field `k` are equal if their
evaluations agree at every invertible matrix.

The proof considers `(p - q) * det(X)`, where `det(X) := Matrix.det (Matrix.mvPolynomialX m m k)`
is the generic determinant polynomial. Evaluated at any `s : m × m → k`, this product vanishes:
if `det (Matrix.of fun i j => s (i, j)) = 0` the determinant factor kills it; otherwise the
matrix is invertible and the hypothesis applies. By `MvPolynomial.funext` the product is zero,
and since `det(X) ≠ 0` and `MvPolynomial _ k` is an integral domain, `p = q`. -/
theorem eq_of_eval_eq_on_gl {m k : Type*} [Fintype m] [DecidableEq m] [Field k] [Infinite k]
    {p q : MvPolynomial (m × m) k}
    (h : ∀ g : Matrix.GeneralLinearGroup m k,
           MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) p =
           MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) q) :
    p = q := by
  classical
  have hdet_ne : Matrix.det (Matrix.mvPolynomialX m m k) ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero m k
  have hprod : (p - q) * Matrix.det (Matrix.mvPolynomialX m m k) = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_mul, map_sub, map_zero]
    have hdet_eval :
        MvPolynomial.eval s (Matrix.det (Matrix.mvPolynomialX m m k)) =
          Matrix.det (Matrix.of fun i j : m => s (i, j)) := by
      rw [(MvPolynomial.eval s).map_det]
      congr 1
      ext i j
      simp [Matrix.mvPolynomialX]
    rw [hdet_eval]
    by_cases hdet_s :
        Matrix.det (Matrix.of fun i j : m => s (i, j)) = 0
    · rw [hdet_s, mul_zero]
    · have hh := h (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (Matrix.of fun i j : m => s (i, j)) hdet_s)
      have hs_eq :
          (fun ij : m × m =>
              (Matrix.GeneralLinearGroup.mkOfDetNeZero
                  (Matrix.of fun i j : m => s (i, j)) hdet_s :
                Matrix m m k) ij.1 ij.2) = s := by
        funext ij
        rfl
      rw [hs_eq] at hh
      rw [hh, sub_self, zero_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hdet_ne)

end MvPolynomial
