import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Data.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The universal characteristic polynomial

In this file we define the universal characteristic polynomial.
We use it to show that the coeffients of the characteristic polynomial
of a matrix are homogeneous polynomials in the matrix entries.

## Main results

* `Matrix.charpoly.univ`: the universal characteristic polynomial
* `Matrix.charpoly.univ_map`: evaluating `univ` on the entries of a matrix `M`
  gives the characteristic polynomial of `M`.
* `Matrix.charpoly.univ_coeff_isHomogeneous`:
  the `i`-th coefficient of `univ` is a homogeneous polynomial of degree `n - i`.
-/

open BigOperators

namespace Matrix.charpoly

variable {R : Type*} (n : Type*) [CommRing R] [Fintype n] [DecidableEq n]

/-- The universal characteristic polynomial for `n × n`-matrices.-/
noncomputable
def univ : Polynomial (MvPolynomial (n × n) ℤ) :=
  charpoly <| Matrix.of fun i j ↦ MvPolynomial.X (i, j)

lemma univ_map (M : Matrix n n R) :
    (univ n).map (MvPolynomial.aeval fun ij ↦ M ij.1 ij.2).toRingHom = charpoly M := by
  rw [← Polynomial.coe_mapRingHom]
  simp only [univ, charpoly, det_apply', map_sum, _root_.map_mul, map_prod]
  apply Finset.sum_congr rfl
  rintro i -
  congr 1
  · simp only [AlgHom.toRingHom_eq_coe, map_intCast]
  · apply Finset.prod_congr rfl
    rintro j -
    by_cases h : i j = j <;> simp [h]

lemma univ_coeff_aeval (M : Matrix n n R) (i : ℕ) :
    MvPolynomial.aeval (fun ij ↦ M ij.1 ij.2) ((univ n).coeff i) =
      (charpoly M).coeff i := by
  simp [← univ_map]

@[simp]
lemma univ_coeff_card : (univ n).coeff (Fintype.card n) = 1 := by
  apply MvPolynomial.funext
  intro M'
  let M := Matrix.of <| Function.curry M'
  erw [univ_coeff_aeval n M]
  rw [_root_.map_one, ← M.charpoly_natDegree_eq_dim]
  exact M.charpoly_monic.leadingCoeff

@[simp]
lemma univ_natDegree : (univ n).natDegree = Fintype.card n := by
  have aux : univ n ≠ 0 := by
    intro h; simpa [h] using univ_coeff_card n
  apply le_antisymm
  · rw [Polynomial.natDegree_eq_support_max' aux, Finset.max'_le_iff]
    intro i hi
    simp only [Polynomial.mem_support_iff, ne_eq] at hi
    contrapose! hi
    apply MvPolynomial.funext
    intro M'
    let M := Matrix.of <| Function.curry M'
    rw [← M.charpoly_natDegree_eq_dim] at hi
    erw [univ_coeff_aeval n M, Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero]
  · by_contra! h
    simpa only [Polynomial.coeff_eq_zero_of_natDegree_lt h, zero_ne_one]
      using univ_coeff_card n

lemma univ_monic : (univ n).Monic := by
  simp only [Polynomial.Monic, Polynomial.leadingCoeff, univ_natDegree, univ_coeff_card]

open MvPolynomial in
lemma optionEquivLeft_symm_univ_isHomogeneous :
    ((optionEquivLeft ℤ (n × n)).symm (univ n)).IsHomogeneous (Fintype.card n) := by
  have aux : Fintype.card n = 0 + ∑ i : n, 1 := by
    simp only [zero_add, Finset.sum_const, smul_eq_mul, mul_one, Fintype.card]
  simp only [aux, univ, charpoly, charmatrix, scalar_apply, RingHom.mapMatrix_apply, det_apply',
    sub_apply, map_apply, of_apply, map_sum, _root_.map_mul, map_intCast, map_prod, map_sub,
    optionEquivLeft_symm_apply, Polynomial.aevalTower_C, rename_X, diagonal]
  apply IsHomogeneous.sum
  rintro i -
  apply IsHomogeneous.mul
  · apply isHomogeneous_C
  · apply IsHomogeneous.prod
    rintro j -
    rw [← mem_homogeneousSubmodule]
    by_cases h : i j = j
    · simp only [h, ↓reduceIte, Polynomial.aevalTower_X]
      apply Submodule.sub_mem <;> apply isHomogeneous_X
    · simp only [h, ↓reduceIte, map_zero, zero_sub]
      apply Submodule.neg_mem; apply isHomogeneous_X

-- move this
open MvPolynomial in
lemma _root_.MvPolynomial.coeff_isHomogeneous_of_optionEquivLeft_symm_isHomogeneous
    {σ : Type*} [Fintype σ] {p : Polynomial (MvPolynomial σ R)} {n : ℕ}
    (hp : ((optionEquivLeft R σ).symm p).IsHomogeneous n)
    (i j : ℕ) (h : i + j = n) :
    (p.coeff i).IsHomogeneous j := by
  have e := Fintype.equivFin σ
  let e' := e.optionCongr.trans (_root_.finSuccEquiv _).symm
  let F := renameEquiv R e
  let F' := renameEquiv R e'
  let φ := F' ((optionEquivLeft R σ).symm p)
  have hφ : φ.IsHomogeneous n := hp.rename_isHomogeneous
  suffices IsHomogeneous (F (p.coeff i)) j by
    rwa [← (IsHomogeneous.rename_isHomogeneous_iff e.injective)]
  convert hφ.finSuccEquiv_coeff_isHomogeneous i j h using 1
  dsimp only
  clear hp hφ φ
  induction p using Polynomial.induction_on'
  case h_add H₁ H₂ => simp only [Polynomial.coeff_add, map_add, H₁, H₂]
  case h_monomial k c =>
    conv_rhs => rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [
      mul_ite, mul_one, mul_zero, renameEquiv_apply, _root_.map_mul, optionEquivLeft_symm_apply,
      Polynomial.aevalTower_C, map_pow, Polynomial.aevalTower_X, Equiv.coe_trans, Function.comp_def,
      Equiv.optionCongr_apply, rename_rename, Option.map_some', finSuccEquiv_symm_some, rename_X,
      Option.map_none', finSuccEquiv_symm_none, finSuccEquiv_apply, coe_eval₂Hom, eval₂_rename,
      Fin.cases_succ, eval₂Hom_X', Fin.cases_zero]
    induction c using MvPolynomial.induction_on'
    case h2 H₁ H₂ => simp [H₁, H₂, add_mul]
    case h1 d a =>
      simp only [eval₂_monomial, eq_intCast, Finsupp.prod_pow, Fintype.prod_prod_type,
        Polynomial.coeff_mul_X_pow', Polynomial.coeff_intCast_mul,
        RingHom.comp_apply]
      simp_rw [← Polynomial.C_pow, ← map_prod, Polynomial.coeff_C_mul, Polynomial.coeff_C]
      simp only [tsub_eq_zero_iff_le, mul_ite, mul_zero]
      split
      · split
        · rw [Polynomial.coeff_monomial, if_pos]
          · simp only [rename, aeval, algebraMap_int_eq, AlgHom.coe_mk, coe_eval₂Hom, eq_intCast,
              eval₂_monomial, Function.comp_apply, Finsupp.prod_pow, Fintype.prod_prod_type]
            rfl
          · omega
        · rw [Polynomial.coeff_monomial, if_neg, map_zero]
          omega
      · rw [Polynomial.coeff_monomial, if_neg, map_zero]
        omega

lemma univ_coeff_isHomogeneous (i j : ℕ) (h : i + j = Fintype.card n) :
    ((univ n).coeff i).IsHomogeneous j :=
  MvPolynomial.coeff_isHomogeneous_of_optionEquivLeft_symm_isHomogeneous
    (optionEquivLeft_symm_univ_isHomogeneous n) _ _ h

end Matrix.charpoly
