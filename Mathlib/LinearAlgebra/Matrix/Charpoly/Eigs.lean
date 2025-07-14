/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Bound

/-!
# Eigenvalues are characteristic polynomial roots.

In fields we show that:

* `Matrix.det_eq_prod_roots_charpoly_of_splits`: the determinant (in the field of the matrix)
  is the product of the roots of the characteristic polynomial if the polynomial splits in the field
  of the matrix.
* `Matrix.trace_eq_sum_roots_charpoly_of_splits`: the trace is the sum of the roots of the
  characteristic polynomial if the polynomial splits in the field of the matrix.

In an algebraically closed field we show that:

* `Matrix.det_eq_prod_roots_charpoly`: the determinant is the product of the roots of the
  characteristic polynomial.
* `Matrix.trace_eq_sum_roots_charpoly`: the trace is the sum of the roots of the
  characteristic polynomial.

Note that over other fields such as `ℝ`, these results can be used by using
`A.map (algebraMap ℝ ℂ)` as the matrix, and then applying `RingHom.map_det`.

The two lemmas `Matrix.det_eq_prod_roots_charpoly` and `Matrix.trace_eq_sum_roots_charpoly` are more
commonly stated as trace is the sum of eigenvalues and determinant is the product of eigenvalues.
Mathlib has already defined eigenvalues in `LinearAlgebra.Eigenspace` as the roots of the minimal
polynomial of a linear endomorphism. These do not have correct multiplicity and cannot be used in
the theorems above. Hence we express these theorems in terms of the roots of the characteristic
polynomial directly.

## TODO

The proofs of `det_eq_prod_roots_charpoly_of_splits` and
`trace_eq_sum_roots_charpoly_of_splits` closely resemble
`norm_gen_eq_prod_roots` and `trace_gen_eq_sum_roots` respectively, but the
dependencies are not general enough to unify them. We should refactor
`Polynomial.prod_roots_eq_coeff_zero_of_monic_of_split` and
`Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split` to assume splitting over an arbitrary map.
-/


variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Field R]
variable {A : Matrix n n R}

open Matrix Polynomial

open scoped Matrix

namespace Matrix

theorem det_eq_prod_roots_charpoly_of_splits (hAps : A.charpoly.Splits (RingHom.id R)) :
    A.det = (Matrix.charpoly A).roots.prod := by
  rw [det_eq_sign_charpoly_coeff, ← charpoly_natDegree_eq_dim A,
    Polynomial.prod_roots_eq_coeff_zero_of_monic_of_splits A.charpoly_monic hAps, ← mul_assoc,
    ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul]

theorem trace_eq_sum_roots_charpoly_of_splits (hAps : A.charpoly.Splits (RingHom.id R)) :
    A.trace = (Matrix.charpoly A).roots.sum := by
  rcases isEmpty_or_nonempty n with h | _
  · rw [Matrix.trace, Fintype.sum_empty, Matrix.charpoly,
      det_eq_one_of_card_eq_zero (Fintype.card_eq_zero_iff.2 h), Polynomial.roots_one,
      Multiset.empty_eq_zero, Multiset.sum_zero]
  · rw [trace_eq_neg_charpoly_coeff, neg_eq_iff_eq_neg,
      ← Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split A.charpoly_monic hAps, nextCoeff,
      charpoly_natDegree_eq_dim, if_neg (Fintype.card_ne_zero : Fintype.card n ≠ 0)]

variable (A)

theorem det_eq_prod_roots_charpoly [IsAlgClosed R] : A.det = (Matrix.charpoly A).roots.prod :=
  det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)

theorem trace_eq_sum_roots_charpoly [IsAlgClosed R] : A.trace = (Matrix.charpoly A).roots.sum :=
  trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Matrix n n 𝕜}

theorem IsHermitian.charpoly_roots_eq_eigenvalues (hA : A.IsHermitian) :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
  -- Since M is Hermitian, its characteristic polynomial splits into linear factors over the reals.
  have h_split : A.charpoly = Multiset.prod (Multiset.map (fun (e : ℝ) => Polynomial.X - Polynomial.C (RCLike.ofReal e))
    (Multiset.map (fun (i : n) => hA.eigenvalues i) Finset.univ.val)) := by
    -- Since M is Hermitian, it is diagonalizable, and its characteristic polynomial splits into linear factors over the reals.
    have h_diag : ∃ P : Matrix n n 𝕜, P.det ≠ 0 ∧ ∃ D : Matrix n n 𝕜, D = Matrix.diagonal
        (fun i => RCLike.ofReal (hA.eigenvalues i)) ∧ A = P * D * P⁻¹ := by
      have := hA.spectral_theorem;
      refine' ⟨ hA.eigenvectorUnitary, _, _ ⟩;
      -- Case 1
      · -- Since the eigenvector unitary is a unitary matrix, its determinant is a unit, hence non-zero.
        have h_det_unitary : IsUnit (Matrix.det (hA.eigenvectorUnitary : Matrix n n 𝕜)) := by
          exact UnitaryGroup.det_isUnit hA.eigenvectorUnitary
        exact h_det_unitary.ne_zero;
      -- Case 2
      · refine' ⟨ _, rfl, this.trans _ ⟩;
        rw [ Matrix.inv_eq_left_inv ];
        congr!;
        bound;
    -- Since M is similar to D, their characteristic polynomials are the same.
    have h_char_poly : A.charpoly = Matrix.charpoly (Matrix.diagonal (fun i =>
        RCLike.ofReal (hA.eigenvalues i))) := by
      rcases h_diag with ⟨P, left, ⟨D, left_1, rfl⟩⟩
      rw [ ← left_1, Matrix.charpoly, Matrix.charpoly ];
      simp +decide [ Matrix.charmatrix, Matrix.mul_assoc ];
      -- Since $w$ is invertible, we can simplify the determinant.
      have h_inv : (P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) = 1 := by
        simp ( config := { decide := Bool.true } ) [ ← Matrix.map_mul, left ];
      -- Since $w$ is invertible, we can simplify the determinant using the fact that the determinant of a product is the product of the determinants.
      have h_det_prod : Matrix.det ((Matrix.diagonal (fun _ => Polynomial.X) - P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜) * (D.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜) * P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)))) = Matrix.det ((P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (Matrix.diagonal (fun _ => Polynomial.X) - D.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜))) := by
        simp ( config := { decide := Bool.true } ) only [ mul_sub, sub_mul, Matrix.mul_assoc, h_inv ];
        -- Since Matrix.diagonal (fun _ => Polynomial.X) is a scalar matrix, it commutes with any matrix.
        have h_comm : Matrix.diagonal (fun _ => Polynomial.X) * P⁻¹.map Polynomial.C = P⁻¹.map Polynomial.C * Matrix.diagonal (fun _ => Polynomial.X) := by
          ext i j; by_cases hi : i = j <;> simp ( config := { decide := Bool.true } ) [ hi ];
        simp ( config := { decide := Bool.true } ) only [ h_comm, Matrix.mul_assoc ];
        simp ( config := { decide := Bool.true } ) [ ← mul_assoc, h_inv ];
      rw [ h_det_prod, Matrix.det_mul, Matrix.det_mul ];
      -- Since the determinant of the product of two matrices is the product of their determinants, and the determinant of the identity matrix is 1, we have:
      have h_det_identity : Matrix.det (P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * Matrix.det (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) = 1 := by
        rw [ ← Matrix.det_mul, h_inv, Matrix.det_one ];
      rw [ mul_right_comm, h_det_identity, one_mul ];
    rw [h_char_poly];
    simp ( config := { decide := Bool.true } ) [ Matrix.charpoly, Matrix.det_diagonal ];
  rw [ h_split, Polynomial.roots_multiset_prod ];
  -- Case 1
  · erw [ Multiset.bind_map ];
    aesop;
  -- Case 2
  · -- Since the eigenvalues are real, and we're working over the complex numbers (since 𝕜 is a real closed field), the polynomial X - C(e) would be zero only if e is zero. But if e is zero, then the polynomial would be X, which isn't zero. So 0 can't be in the multiset.
    simp [Polynomial.X_sub_C_ne_zero]

end RCLike

end Matrix
