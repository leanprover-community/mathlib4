import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Data.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Lie.PolyStuff

/-!
# The coeffients of the characteristic polynomial are polynomial in the matrix entries
-/

open BigOperators

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
  simp [← univ_map]

@[simp]
lemma univ_coeff_card : (univ (n := n)).coeff (Fintype.card n) = 1 := by
  apply MvPolynomial.funext
  intro M'
  let M := Matrix.of <| Function.curry M'
  erw [univ_coeff_map M]
  rw [_root_.map_one, ← M.charpoly_natDegree_eq_dim]
  exact M.charpoly_monic.leadingCoeff

@[simp]
lemma univ_natDegree : (univ (n := n)).natDegree = Fintype.card n := by
  have aux : univ (n := n) ≠ 0 := by
    intro h; simpa [h] using univ_coeff_card (n := n)
  apply le_antisymm
  · rw [Polynomial.natDegree_eq_support_max' aux, Finset.max'_le_iff]
    intro i hi
    simp only [Polynomial.mem_support_iff, ne_eq] at hi
    contrapose! hi
    apply MvPolynomial.funext
    intro M'
    let M := Matrix.of <| Function.curry M'
    rw [← M.charpoly_natDegree_eq_dim] at hi
    erw [univ_coeff_map M, Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero]
  · by_contra! h
    simpa only [Polynomial.coeff_eq_zero_of_natDegree_lt h, zero_ne_one]
      using univ_coeff_card (n := n)

lemma univ_monic : (univ (n := n)).Monic := by
  simp only [Polynomial.Monic, Polynomial.leadingCoeff, univ_natDegree, univ_coeff_card]

open MvPolynomial in
lemma optionEquivLeft_univ_isHomogeneous :
    ((optionEquivLeft ℤ (n × n)).symm univ).IsHomogeneous (Fintype.card n) := by
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

open MvPolynomial in
lemma univ_coeff_isHomogeneous (i j : ℕ) (h : i + j = Fintype.card n) :
    ((univ (n := n)).coeff i).IsHomogeneous j := by
  have e := Fintype.equivFin (n × n)
  let e' := e.optionCongr.trans (_root_.finSuccEquiv _).symm
  let F := renameEquiv ℤ e
  let F' := renameEquiv ℤ e'
  let φ := F' ((optionEquivLeft ℤ (n × n)).symm univ)
  have hφ : φ.IsHomogeneous (Fintype.card n) := by
    apply optionEquivLeft_univ_isHomogeneous.rename_isHomogeneous
  suffices IsHomogeneous (F (univ.coeff i)) j by
    rwa [← (IsHomogeneous.rename_isHomogeneous_iff e.injective)]
  replace hφ := IsHomogeneous.finSuccEquiv_coeff_isHomogeneous φ _ hφ i j h
  convert hφ using 1
  dsimp only
  generalize (univ (n := n)) = ψ
  induction ψ using Polynomial.induction_on'
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
        Polynomial.coeff_mul_X_pow', Polynomial.coeff_intCast_mul]
      simp_rw [← Polynomial.C_pow, ← map_prod, Polynomial.coeff_C]
      simp only [tsub_eq_zero_iff_le, mul_ite, mul_zero]
      split
      · split
        · rw [Polynomial.coeff_monomial, if_pos]
          · simp only [rename, aeval, algebraMap_int_eq, AlgHom.coe_mk, coe_eval₂Hom, eq_intCast,
              eval₂_monomial, Function.comp_apply, Finsupp.prod_pow, Fintype.prod_prod_type]
          · omega
        · rw [Polynomial.coeff_monomial, if_neg, map_zero]
          omega
      · rw [Polynomial.coeff_monomial, if_neg, map_zero]
        omega

end Matrix.charpoly
