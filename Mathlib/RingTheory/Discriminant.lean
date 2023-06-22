/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module ring_theory.discriminant
! leanprover-community/mathlib commit 3e068ece210655b7b9a9477c3aff38a492400aa1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Trace
import Mathbin.RingTheory.Norm
import Mathbin.NumberTheory.NumberField.Basic

/-!
# Discriminant of a family of vectors

Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define the
*discriminant* of `b` as the determinant of the matrix whose `(i j)`-th element is the trace of
`b i * b j`.

## Main definition

* `algebra.discr A b` : the discriminant of `b : ι → B`.

## Main results

* `algebra.discr_zero_of_not_linear_independent` : if `b` is not linear independent, then
  `algebra.discr A b = 0`.
* `algebra.discr_of_matrix_vec_mul` and `discr_of_matrix_mul_vec` : formulas relating
  `algebra.discr A ι b` with `algebra.discr A ((P.map (algebra_map A B)).vec_mul b)` and
  `algebra.discr A ((P.map (algebra_map A B)).mul_vec b)`.
* `algebra.discr_not_zero_of_basis` : over a field, if `b` is a basis, then
  `algebra.discr K b ≠ 0`.
* `algebra.discr_eq_det_embeddings_matrix_reindex_pow_two` : if `L/K` is a field extension and
  `b : ι → L`, then `discr K b` is the square of the determinant of the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the embedding in an algebraically closed
  field `E` corresponding to `j : ι` via a bijection `e : ι ≃ (L →ₐ[K] E)`.
* `algebra.discr_of_power_basis_eq_prod` : the discriminant of a power basis.
* `discr_is_integral` : if `K` and `L` are fields and `is_scalar_tower R K L`, is `b : ι → L`
  satisfies ` ∀ i, is_integral R (b i)`, then `is_integral R (discr K b)`.
* `discr_mul_is_integral_mem_adjoin` : let `K` be the fraction field of an integrally closed domain
  `R` and let `L` be a finite separable extension of `K`. Let `B : power_basis K L` be such that
  `is_integral R B.gen`. Then for all, `z : L` we have
  `(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`.

## Implementation details

Our definition works for any `A`-algebra `B`, but note that if `B` is not free as an `A`-module,
then `trace A B = 0` by definition, so `discr A b = 0` for any `b`.
-/


universe u v w z

open scoped Matrix BigOperators

open Matrix FiniteDimensional Fintype Polynomial Finset IntermediateField

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z) {ι : Type w}

variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

section Discr

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discr A ι b` as the determinant of `trace_matrix A ι b`. -/
noncomputable def discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] (b : ι → B) := by classical exact (trace_matrix A b).det
#align algebra.discr Algebra.discr

theorem discr_def [DecidableEq ι] [Fintype ι] (b : ι → B) : discr A b = (traceMatrix A b).det := by
  convert rfl
#align algebra.discr_def Algebra.discr_def

variable {ι' : Type _} [Fintype ι'] [Fintype ι]

section Basic

@[simp]
theorem discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : discr A (b ∘ ⇑f.symm) = discr A b := by
  classical rw [← Basis.coe_reindex, discr_def, trace_matrix_reindex, det_reindex_self, ← discr_def]
#align algebra.discr_reindex Algebra.discr_reindex

/-- If `b` is not linear independent, then `algebra.discr A b = 0`. -/
theorem discr_zero_of_not_linearIndependent [IsDomain A] {b : ι → B}
    (hli : ¬LinearIndependent A b) : discr A b = 0 := by
  classical
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have : (trace_matrix A b).mulVec g = 0 := by
    ext i
    have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) := by intro j;
      simp [mul_comm]
    simp only [mul_vec, dot_product, trace_matrix_apply, Pi.zero_apply, trace_form_apply, fun j =>
      this j, ← LinearMap.map_sum, ← sum_mul, hg, MulZeroClass.zero_mul, LinearMap.map_zero]
  by_contra h
  rw [discr_def] at h 
  simpa [Matrix.eq_zero_of_mulVec_eq_zero h this] using hi
#align algebra.discr_zero_of_not_linear_independent Algebra.discr_zero_of_not_linearIndependent

variable {A}

/-- Relation between `algebra.discr A ι b` and
`algebra.discr A ((P.map (algebra_map A B)).vec_mul b)`. -/
theorem discr_of_matrix_vecMul [DecidableEq ι] (b : ι → B) (P : Matrix ι ι A) :
    discr A ((P.map (algebraMap A B)).vecMul b) = P.det ^ 2 * discr A b := by
  rw [discr_def, trace_matrix_of_matrix_vec_mul, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]
#align algebra.discr_of_matrix_vec_mul Algebra.discr_of_matrix_vecMul

/-- Relation between `algebra.discr A ι b` and
`algebra.discr A ((P.map (algebra_map A B)).mul_vec b)`. -/
theorem discr_of_matrix_mulVec [DecidableEq ι] (b : ι → B) (P : Matrix ι ι A) :
    discr A ((P.map (algebraMap A B)).mulVec b) = P.det ^ 2 * discr A b := by
  rw [discr_def, trace_matrix_of_matrix_mul_vec, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]
#align algebra.discr_of_matrix_mul_vec Algebra.discr_of_matrix_mulVec

end Basic

section Field

variable (K : Type u) {L : Type v} (E : Type z) [Field K] [Field L] [Field E]

variable [Algebra K L] [Algebra K E]

variable [Module.Finite K L] [IsAlgClosed E]

/-- Over a field, if `b` is a basis, then `algebra.discr K b ≠ 0`. -/
theorem discr_not_zero_of_basis [IsSeparable K L] (b : Basis ι K L) : discr K b ≠ 0 :=
  by
  cases isEmpty_or_nonempty ι
  · simp [discr]
  · have :=
      span_eq_top_of_linearIndependent_of_card_eq_finrank b.linear_independent
        (finrank_eq_card_basis b).symm
    classical
    rw [discr_def, trace_matrix]
    simp_rw [← Basis.mk_apply b.linear_independent this.ge]
    rw [← trace_matrix, trace_matrix_of_basis, ← BilinForm.nondegenerate_iff_det_ne_zero]
    exact traceForm_nondegenerate _ _
#align algebra.discr_not_zero_of_basis Algebra.discr_not_zero_of_basis

/-- Over a field, if `b` is a basis, then `algebra.discr K b` is a unit. -/
theorem discr_isUnit_of_basis [IsSeparable K L] (b : Basis ι K L) : IsUnit (discr K b) :=
  IsUnit.mk0 _ (discr_not_zero_of_basis _ _)
#align algebra.discr_is_unit_of_basis Algebra.discr_isUnit_of_basis

variable (b : ι → L) (pb : PowerBasis K L)

/-- If `L/K` is a field extension and `b : ι → L`, then `discr K b` is the square of the
determinant of the matrix whose `(i, j)` coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the
embedding in an algebraically closed field `E` corresponding to `j : ι` via a bijection
`e : ι ≃ (L →ₐ[K] E)`. -/
theorem discr_eq_det_embeddingsMatrixReindex_pow_two [DecidableEq ι] [IsSeparable K L]
    (e : ι ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K b) = (embeddingsMatrixReindex K E b e).det ^ 2 := by
  rw [discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    trace_matrix_eq_embeddings_matrix_reindex_mul_trans, det_mul, det_transpose, pow_two]
#align algebra.discr_eq_det_embeddings_matrix_reindex_pow_two Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two

/-- The discriminant of a power basis. -/
theorem discr_powerBasis_eq_prod (e : Fin pb.dim ≃ (L →ₐ[K] E)) [IsSeparable K L] :
    algebraMap K E (discr K pb.Basis) =
      ∏ i : Fin pb.dim, ∏ j in Ioi i, (e j pb.gen - e i pb.gen) ^ 2 :=
  by
  rw [discr_eq_det_embeddings_matrix_reindex_pow_two K E pb.basis e,
    embeddings_matrix_reindex_eq_vandermonde, det_transpose, det_vandermonde, ← prod_pow]
  congr; ext i
  rw [← prod_pow]
#align algebra.discr_power_basis_eq_prod Algebra.discr_powerBasis_eq_prod

/-- A variation of `of_power_basis_eq_prod`. -/
theorem discr_powerBasis_eq_prod' [IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.Basis) =
      ∏ i : Fin pb.dim, ∏ j in Ioi i, -((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)) :=
  by
  rw [discr_power_basis_eq_prod _ _ _ e]
  congr; ext i; congr; ext j
  ring
#align algebra.discr_power_basis_eq_prod' Algebra.discr_powerBasis_eq_prod'

local notation "n" => finrank K L

/-- A variation of `of_power_basis_eq_prod`. -/
theorem discr_powerBasis_eq_prod'' [IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.Basis) =
      (-1) ^ (n * (n - 1) / 2) *
        ∏ i : Fin pb.dim, ∏ j in Ioi i, (e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen) :=
  by
  rw [discr_power_basis_eq_prod' _ _ _ e]
  simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)),
    prod_mul_distrib]
  congr
  simp only [prod_pow_eq_pow_sum, prod_const]
  congr
  rw [← @Nat.cast_inj ℚ, Nat.cast_sum]
  have : ∀ x : Fin pb.dim, ↑x + 1 ≤ pb.dim := by simp [Nat.succ_le_iff, Fin.is_lt]
  simp_rw [Fin.card_Ioi, Nat.sub_sub, add_comm 1]
  simp only [Nat.cast_sub, this, Finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    Nat.cast_add, Nat.cast_one, sum_add_distrib, mul_one]
  rw [← Nat.cast_sum, ← @Finset.sum_range ℕ _ pb.dim fun i => i, sum_range_id]
  have hn : n = pb.dim :=
    by
    rw [← AlgHom.card K L E, ← Fintype.card_fin pb.dim]
    exact card_congr (Equiv.symm e)
  have h₂ : 2 ∣ pb.dim * (pb.dim - 1) := even_iff_two_dvd.1 (Nat.even_mul_self_pred _)
  have hne : ((2 : ℕ) : ℚ) ≠ 0 := by simp
  have hle : 1 ≤ pb.dim :=
    by
    rw [← hn, Nat.one_le_iff_ne_zero, ← zero_lt_iff, FiniteDimensional.finrank_pos_iff]
    infer_instance
  rw [hn, Nat.cast_div h₂ hne, Nat.cast_mul, Nat.cast_sub hle]
  field_simp
  ring
#align algebra.discr_power_basis_eq_prod'' Algebra.discr_powerBasis_eq_prod''

/-- Formula for the discriminant of a power basis using the norm of the field extension. -/
theorem discr_powerBasis_eq_norm [IsSeparable K L] :
    discr K pb.Basis =
      (-1) ^ (n * (n - 1) / 2) * norm K (aeval pb.gen (minpoly K pb.gen).derivative) :=
  by
  let E := AlgebraicClosure L
  letI := fun a b : E => Classical.propDecidable (Eq a b)
  have e : Fin pb.dim ≃ (L →ₐ[K] E) :=
    by
    refine' equiv_of_card_eq _
    rw [Fintype.card_fin, AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  have hnodup : (map (algebraMap K E) (minpoly K pb.gen)).roots.Nodup :=
    nodup_roots (separable.map (IsSeparable.separable K pb.gen))
  have hroots : ∀ σ : L →ₐ[K] E, σ pb.gen ∈ (map (algebraMap K E) (minpoly K pb.gen)).roots :=
    by
    intro σ
    rw [mem_roots, is_root.def, eval_map, ← aeval_def, aeval_alg_hom_apply]
    repeat' simp [minpoly.ne_zero (IsSeparable.isIntegral K pb.gen)]
  apply (algebraMap K E).Injective
  rw [RingHom.map_mul, RingHom.map_pow, RingHom.map_neg, RingHom.map_one,
    discr_power_basis_eq_prod'' _ _ _ e]
  congr
  rw [norm_eq_prod_embeddings, prod_prod_Ioi_mul_eq_prod_prod_off_diag]
  conv_rhs =>
    congr
    skip
    ext
    rw [← aeval_alg_hom_apply,
      aeval_root_derivative_of_splits (minpoly.monic (IsSeparable.isIntegral K pb.gen))
        (IsAlgClosed.splits_codomain _) (hroots σ),
      ← Finset.prod_mk _ (hnodup.erase _)]
  rw [prod_sigma', prod_sigma']
  refine'
    prod_bij (fun i hi => ⟨e i.2, e i.1 pb.gen⟩) (fun i hi => _) (fun i hi => by simp at hi )
      (fun i j hi hj hij => _) fun σ hσ => _
  · simp only [true_and_iff, Finset.mem_mk, mem_univ, mem_sigma]
    rw [Multiset.mem_erase_of_ne fun h => _]
    · exact hroots _
    · simp only [true_and_iff, mem_univ, Ne.def, mem_sigma, mem_compl, mem_singleton] at hi 
      rw [← PowerBasis.liftEquiv_apply_coe, ← PowerBasis.liftEquiv_apply_coe] at h 
      exact hi (e.injective <| pb.lift_equiv.injective <| Subtype.eq h.symm)
  · simp only [Equiv.apply_eq_iff_eq, heq_iff_eq] at hij 
    have h := hij.2
    rw [← PowerBasis.liftEquiv_apply_coe, ← PowerBasis.liftEquiv_apply_coe] at h 
    refine' Sigma.eq (Equiv.injective e (Equiv.injective _ (Subtype.eq h))) (by simp [hij.1])
  · simp only [true_and_iff, Finset.mem_mk, mem_univ, mem_sigma] at hσ ⊢
    simp only [Sigma.exists, exists_prop, mem_compl, mem_singleton, Ne.def]
    refine' ⟨e.symm (PowerBasis.lift pb σ.2 _), e.symm σ.1, ⟨fun h => _, Sigma.eq _ _⟩⟩
    · rw [aeval_def, eval₂_eq_eval_map, ← is_root.def, ← mem_roots]
      · exact Multiset.erase_subset _ _ hσ
      · simp [minpoly.ne_zero (IsSeparable.isIntegral K pb.gen)]
    · replace h := AlgHom.congr_fun (Equiv.injective _ h) pb.gen
      rw [PowerBasis.lift_gen] at h 
      rw [← h] at hσ 
      exact hnodup.not_mem_erase hσ
    all_goals simp
#align algebra.discr_power_basis_eq_norm Algebra.discr_powerBasis_eq_norm

section Integral

variable {R : Type z} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]

/-- If `K` and `L` are fields and `is_scalar_tower R K L`, and `b : ι → L` satisfies
` ∀ i, is_integral R (b i)`, then `is_integral R (discr K b)`. -/
theorem discr_isIntegral {b : ι → L} (h : ∀ i, IsIntegral R (b i)) : IsIntegral R (discr K b) := by
  classical
  rw [discr_def]
  exact IsIntegral.det fun i j => is_integral_trace (isIntegral_mul (h i) (h j))
#align algebra.discr_is_integral Algebra.discr_isIntegral

/-- If `b` and `b'` are `ℚ`-bases of a number field `K` such that
`∀ i j, is_integral ℤ (b.to_matrix b' i j)` and `∀ i j, is_integral ℤ (b'.to_matrix b i j)` then
`discr ℚ b = discr ℚ b'`. -/
theorem discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K] {b : Basis ι ℚ K}
    {b' : Basis ι' ℚ K} (h : ∀ i j, IsIntegral ℤ (b.toMatrix b' i j))
    (h' : ∀ i j, IsIntegral ℤ (b'.toMatrix b i j)) : discr ℚ b = discr ℚ b' :=
  by
  replace h' : ∀ i j, IsIntegral ℤ (b'.to_matrix (b.reindex (b.index_equiv b')) i j)
  · intro i j
    convert h' i ((b.index_equiv b').symm j)
    simpa
  classical
  rw [← (b.reindex (b.index_equiv b')).toMatrix_map_vecMul b', discr_of_matrix_vec_mul, ←
    one_mul (discr ℚ b), Basis.coe_reindex, discr_reindex]
  congr
  have hint : IsIntegral ℤ ((b.reindex (b.index_equiv b')).toMatrix b').det :=
    IsIntegral.det fun i j => h _ _
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hunit : IsUnit r :=
    by
    have : IsIntegral ℤ (b'.to_matrix (b.reindex (b.index_equiv b'))).det :=
      IsIntegral.det fun i j => h' _ _
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    refine' isUnit_iff_exists_inv.2 ⟨r', _⟩
    suffices algebraMap ℤ ℚ (r * r') = 1
      by
      rw [← RingHom.map_one (algebraMap ℤ ℚ)] at this 
      exact (IsFractionRing.injective ℤ ℚ) this
    rw [RingHom.map_mul, hr, hr', ← det_mul, Basis.toMatrix_mul_toMatrix_flip, det_one]
  rw [← RingHom.map_one (algebraMap ℤ ℚ), ← hr]
  cases' Int.isUnit_iff.1 hunit with hp hm
  · simp [hp]
  · simp [hm]
#align algebra.discr_eq_discr_of_to_matrix_coeff_is_integral Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral

/-- Let `K` be the fraction field of an integrally closed domain `R` and let `L` be a finite
separable extension of `K`. Let `B : power_basis K L` be such that `is_integral R B.gen`.
Then for all, `z : L` that are integral over `R`, we have
`(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`. -/
theorem discr_mul_isIntegral_mem_adjoin [IsDomain R] [IsSeparable K L] [IsIntegrallyClosed R]
    [IsFractionRing R K] {B : PowerBasis K L} (hint : IsIntegral R B.gen) {z : L}
    (hz : IsIntegral R z) : discr K B.Basis • z ∈ adjoin R ({B.gen} : Set L) :=
  by
  have hinv : IsUnit (trace_matrix K B.basis).det := by
    simpa [← discr_def] using discr_is_unit_of_basis _ B.basis
  have H :
    (trace_matrix K B.basis).det • (trace_matrix K B.basis).mulVec (B.basis.equiv_fun z) =
      (trace_matrix K B.basis).det • fun i => trace K L (z * B.basis i) :=
    by congr; exact trace_matrix_of_basis_mul_vec _ _
  have cramer := mul_vec_cramer (trace_matrix K B.basis) fun i => trace K L (z * B.basis i)
  suffices ∀ i, ((trace_matrix K B.basis).det • B.basis.equiv_fun z) i ∈ (⊥ : Subalgebra R K)
    by
    rw [← B.basis.sum_repr z, Finset.smul_sum]
    refine' Subalgebra.sum_mem _ fun i hi => _
    replace this := this i
    rw [← discr_def, Pi.smul_apply, mem_bot] at this 
    obtain ⟨r, hr⟩ := this
    rw [Basis.equivFun_apply] at hr 
    rw [← smul_assoc, ← hr, algebraMap_smul]
    refine' Subalgebra.smul_mem _ _ _
    rw [B.basis_eq_pow i]
    refine' Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
  intro i
  rw [← H, ← mul_vec_smul] at cramer 
  replace cramer := congr_arg (mul_vec (trace_matrix K B.basis)⁻¹) cramer
  rw [mul_vec_mul_vec, nonsing_inv_mul _ hinv, mul_vec_mul_vec, nonsing_inv_mul _ hinv, one_mul_vec,
    one_mul_vec] at cramer 
  rw [← congr_fun cramer i, cramer_apply, det_apply]
  refine'
    Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => _) _
  by_cases hji : j = i
  · simp only [update_column_apply, hji, eq_self_iff_true, PowerBasis.coe_basis]
    exact
      mem_bot.2
        (IsIntegrallyClosed.isIntegral_iff.1 <|
          is_integral_trace <| isIntegral_mul hz <| IsIntegral.pow hint _)
  · simp only [update_column_apply, hji, PowerBasis.coe_basis]
    exact
      mem_bot.2
        (IsIntegrallyClosed.isIntegral_iff.1 <|
          is_integral_trace <| isIntegral_mul (IsIntegral.pow hint _) (IsIntegral.pow hint _))
#align algebra.discr_mul_is_integral_mem_adjoin Algebra.discr_mul_isIntegral_mem_adjoin

end Integral

end Field

end Discr

end Algebra

