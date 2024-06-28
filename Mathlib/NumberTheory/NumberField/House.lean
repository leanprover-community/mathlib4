/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Analysis.Matrix
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# House of an algebraic number
This file defines the house of an algebraic number `α`, which is
the largest modulus of its conjugates.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [Keng, H. L, *Introduction to number theory*][keng1982house]

## Tags
number field, algebraic number, house
-/

variable {K : Type*} [Field K] [NumberField K]

noncomputable section

open Module.Free FiniteDimensional NumberField.canonicalEmbedding NumberField

/-- The house of an algebraic number as the norm of its image by the canonical embedding.-/
abbrev House (α : K) : ℝ := ‖canonicalEmbedding K α‖

theorem House_eq_sup' (α : K) :
    House α = Finset.univ.sup' Finset.univ_nonempty (fun φ : K →+* ℂ ↦ ‖φ α‖₊) := by
  rw [House, ← coe_nnnorm, nnnorm_eq, ← Finset.sup'_eq_sup Finset.univ_nonempty]

variable (K)

/-- An equivalence between the set of embeddings of `K` into `ℂ` and the index set of the chosen
  basis of the ring of integers of `K`. -/
abbrev equivReindex : (K →+* ℂ) ≃ (ChooseBasisIndex ℤ (𝓞 K)) := by
  refine Fintype.equivOfCardEq ?_
  rw [Embeddings.card, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

/-- The basis matrix for the embeddings of `K` into `ℂ`. This matrix is formed by
  taking the lattice basis vectors of `K` and reindexing them according to the
  equivalence `equivReindex`, then transposing the resulting matrix. -/
abbrev basisMatrix : Matrix (K →+* ℂ) (K →+* ℂ) ℂ :=
  (Matrix.of fun i ↦ latticeBasis K (equivReindex K i)).transpose

theorem canonicalEmbedding.mem_rat_span_latticeBasis (x : K) :
    (canonicalEmbedding K) x ∈ Submodule.span ℚ (Set.range (latticeBasis K)) := by
  rw [← Basis.sum_repr (integralBasis K) x, map_sum]
  simp_rw [map_rat_smul]
  refine Submodule.sum_smul_mem _ _ (fun i _ ↦ Submodule.subset_span ?_)
  rw [← latticeBasis_apply]
  exact Set.mem_range_self i

theorem canonicalEmbedding.integralBasis_repr_apply (x : K) (i : ChooseBasisIndex ℤ (𝓞 K)) :
    (canonicalEmbedding.latticeBasis K).repr (canonicalEmbedding K x) i =
      (integralBasis K).repr x i := by
  rw [← Basis.restrictScalars_repr_apply ℚ _ ⟨_, mem_rat_span_latticeBasis K x⟩, eq_ratCast,
    Rat.cast_inj]
  let f := (canonicalEmbedding K).toRatAlgHom.toLinearMap.codRestrict _
    (fun x ↦ mem_rat_span_latticeBasis K x)
  suffices ((latticeBasis K).restrictScalars ℚ).repr.toLinearMap ∘ₗ f =
    (integralBasis K).repr.toLinearMap from DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext (integralBasis K) (fun i ↦ ?_)
  have : f (integralBasis K i) = ((latticeBasis K).restrictScalars ℚ) i := by
    apply Subtype.val_injective
    rw [LinearMap.codRestrict_apply, AlgHom.toLinearMap_apply, Basis.restrictScalars_apply,
      latticeBasis_apply]
    rfl
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this, Basis.repr_self]

instance : DecidableEq (K →+* ℂ) := Classical.typeDecidableEq (K →+* ℂ)

theorem det_of_basisMatrix_non_zero : (basisMatrix K).transpose.det ≠ 0 := by
      let e : (K →+* ℂ) ≃ ChooseBasisIndex ℤ (𝓞 K) := equivReindex K
      let N := Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => integralBasis K (e i))
         RingHom.equivRatAlgHom
      rw [show (basisMatrix K).transpose = N by {
        ext:2; simp only [N, Matrix.transpose_apply, latticeBasis_apply, integralBasis_apply,
        Matrix.of_apply, apply_at]; rfl}, ← pow_ne_zero_iff two_ne_zero]
      convert (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
        (Algebra.discr_not_zero_of_basis ℚ (integralBasis K))
      rw [← Algebra.discr_reindex ℚ (integralBasis K) e.symm]
      exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
        (fun i => integralBasis K (e i)) RingHom.equivRatAlgHom).symm

instance : Invertible (basisMatrix K) := by
    have :(basisMatrix K).transpose.det ≠ 0 := det_of_basisMatrix_non_zero K
    rw [Matrix.det_transpose (basisMatrix K)] at this
    exact Matrix.invertibleOfIsUnitDet _ (Ne.isUnit this)

/-- `c` is defined as the product of the maximum absolute value of the entries of the
  inverse of the matrix `basisMatrix` and  `(finrank ℚ K)`. -/
def c := (finrank ℚ K) * ‖fun i j => (basisMatrix K)⁻¹ i j‖

theorem basis_repr_abs_le_const_mul_house (α : 𝓞 K) :
    ∀ i, Complex.abs (((integralBasis K).reindex (equivReindex K).symm).repr α i : ℂ) ≤
    @c K _ _ * House (algebraMap (𝓞 K) K α) := fun i => calc

   _ = Complex.abs (∑ j, (basisMatrix  K)⁻¹ i j *
        (canonicalEmbedding K (algebraMap (𝓞 K) K α) j)) := by
      have : canonicalEmbedding K α = (basisMatrix K).mulVec (fun i ↦
         (((integralBasis K).reindex (equivReindex K).symm).repr α i : ℂ)) := by
        ext
        rw [← (latticeBasis K).sum_repr (canonicalEmbedding K α),
            ← Equiv.sum_comp (equivReindex K)]
        simp_rw [canonicalEmbedding.integralBasis_repr_apply, Matrix.mulVec, Matrix.dotProduct,
          basisMatrix, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_apply,
          mul_comm, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm,
          Pi.smul_apply, smul_eq_mul]
      have : (basisMatrix K)⁻¹.mulVec (fun j => canonicalEmbedding K (algebraMap (𝓞 K) K α) j) i =
        ((integralBasis K).reindex (equivReindex K).symm).repr α i := by
        {rw [Matrix.inv_mulVec_eq_vec (basisMatrix  K) this]}
      rw [← this]; rfl

    _ ≤ ∑ j, ‖fun i j => (basisMatrix K)⁻¹ i j‖ *
         Complex.abs (canonicalEmbedding K (algebraMap (𝓞 K) K α) j) := by
           trans
           ·  trans
              · apply AbsoluteValue.sum_le Complex.abs
              · apply Finset.sum_le_sum (fun _ _ => (AbsoluteValue.map_mul Complex.abs _ _).le)
           · apply Finset.sum_le_sum
              (fun _ _ =>  mul_le_mul_of_nonneg_right ?_ (AbsoluteValue.nonneg Complex.abs _))
             · rw [← Complex.norm_eq_abs]
               exact Matrix.norm_entry_le_entrywise_sup_norm (basisMatrix K)⁻¹

    _ ≤ ∑ _, ‖fun i j => (basisMatrix K)⁻¹ i j‖ * House  (algebraMap (𝓞 K) K α) := by
          apply Finset.sum_le_sum
          intros j _
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg fun i j ↦ (basisMatrix K)⁻¹ i j)
          · rw [← Complex.norm_eq_abs]
            exact norm_le_pi_norm ((canonicalEmbedding K) ((algebraMap (𝓞 K) K) α)) j

    _ =  ↑(finrank ℚ K) * ‖fun i j => (basisMatrix K)⁻¹ i j‖ * House  (algebraMap (𝓞 K) K α) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Embeddings.card, mul_assoc]

end section
