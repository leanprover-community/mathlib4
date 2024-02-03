import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The coeffients of the characteristic polynomial are polynomial in the matrix entries
-/

namespace Matrix.charpoly

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

noncomputable
def univ : Polynomial (MvPolynomial (n × n) ℤ) :=
  charpoly <| Matrix.of fun i j ↦ MvPolynomial.X (i, j)

lemma univ_map (M : Matrix n n R) :
    univ.map (MvPolynomial.aeval fun ij : n × n ↦ M ij.1 ij.2).toRingHom = charpoly M := by
  rw [← Polynomial.coe_mapRingHom]
  simp only [univ, charpoly, det_apply', map_sum, _root_.map_mul, map_prod]
  apply Finset.sum_congr rfl
  rintro i -
  congr 1
  · simp only [AlgHom.toRingHom_eq_coe, map_intCast]
  · apply Finset.prod_congr rfl
    rintro j -
    by_cases h : i j = j <;> simp [h]

lemma univ_coeff_map (M : Matrix n n R) (i : ℕ) :
    MvPolynomial.aeval (fun ij : n × n ↦ M ij.1 ij.2) (univ.coeff i) =
      (charpoly M).coeff i := by
  rw [← univ_map]; simp

end Matrix.charpoly
