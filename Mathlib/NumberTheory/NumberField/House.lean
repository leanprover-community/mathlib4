/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

import Mathlib.NumberTheory.NumberField.Embeddings

/-!
# House of an algebraic number
This file defines the house of an algebraic number `α`, which is
the largest modulus of its conjugates.

## Tags
number field, algebraic number, house
-/

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional Matrix
  Set Algebra Polynomial Basis Finset

variable {K : Type*} [Field K] [NumberField K]

local notation "h" => finrank ℚ K

theorem Matrix.inv_mulVec_eq {u v : Fin h → ℂ} {M : Matrix (Fin h) (Fin h) ℂ} [Invertible M]
    (hM : u = M.mulVec v) : M⁻¹.mulVec u = v := by
  simp only [hM, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

theorem Finset.max'_eq_of_eq {γ : Type _} [LinearOrder γ] {s t : Finset γ} (hs : s.Nonempty)
    (ht : t.Nonempty) (hst : s = t) : s.max' hs = t.max' ht := by simp_rw [hst]

/-- `Finset.max'OfFintype` takes a function `f` from a finite and nonempty type `s` to a
  linearly ordered type `γ`, and returns the maximum value of `f` over all elements of `s`. -/
def Finset.max'OfFintype {s γ : Type _} [Fintype s] [Nonempty s] (f : Π _ : s, γ)
    [LinearOrder γ] : γ := by
  apply Finset.max' (f '' Set.univ).toFinset
  simp only [Set.image_univ, Set.toFinset_range, Finset.image_nonempty]
  exact Finset.univ_nonempty

/-- `Matrix.max_abs_entry` takes a matrix `B` of size `finrank ℚ K` and returns the maximum
  absolute value of its entries. This is done by first finding the maximum absolute value of the
  entries in each row, and then finding the maximum of those row maxima. -/
noncomputable def Matrix.maxAbsEntry (B : Matrix (Fin (finrank ℚ K)) (Fin (finrank ℚ K)) ℂ) := by
  letI : Nonempty (Fin (finrank ℚ K)) := Fin.pos_iff_nonempty.mp (finrank_pos)
  apply Finset.max'OfFintype (fun i => Finset.max'OfFintype (fun j => Complex.abs (B i j)))

noncomputable section

/-- There is noncomputably a bijection between `Fin h` and `ChooseBasisIndex ℤ (𝓞 K)`
 composing the equivalence `σ` with an equivalence derived from the cardinality of
the embeddings and the cardinality of the integral basis of `K`.-/
abbrev Fin.equivChooseBasisIndex : Fin h ≃ ChooseBasisIndex ℤ (𝓞 K) :=
  (Fintype.equivFinOfCardEq (card K ℂ)).symm.trans
    (equivOfCardEq ((card K ℂ).trans (finrank_eq_card_basis (integralBasis K))))

/-- `basisReindex` is a basis of `𝓞 K` over `ℤ` by reindexing the basis
provided by `RingOfIntegers.basis K` using the inverse of the equivalence `f`.-/
abbrev basisReindex : Basis (Fin h) ℤ (𝓞 K) := (RingOfIntegers.basis K).reindex
  (Fin.equivChooseBasisIndex).symm

/-- `basisMatrixTranspose` is the matrix whose `(i, j)` coefficient is `σⱼ (b i)`. -/
def basisMatrixTranspose : Matrix (Fin h) (Fin h) ℂ := ((embeddingsMatrixReindex ℚ ℂ
  (fun i => algebraMap (𝓞 K) K (basisReindex i))
    ((Fintype.equivFinOfCardEq (card K ℂ)).symm.trans (RingHom.equivRatAlgHom)))).transpose

theorem embeddings_matrix_reindex_eq_basis_matrix_transpose :
  ((embeddingsMatrixReindex ℚ ℂ (fun i => ((reindex (integralBasis K)
    ((Fintype.equivFinOfCardEq (card K ℂ)).symm.trans
    (equivOfCardEq ((card K ℂ).trans (finrank_eq_card_basis (integralBasis K))))).symm) i))
      ((Fintype.equivFinOfCardEq (card K ℂ)).symm.trans (RingHom.equivRatAlgHom)))) =
     (@basisMatrixTranspose K  _ _).transpose := by
  simp only [basisMatrixTranspose, integralBasis, coe_reindex, Equiv.symm_symm,
    Function.comp_apply, localizationLocalization_apply, transpose_transpose]

theorem rootSet_abs_nonempty (α : K) :
    (toFinset (⇑Complex.abs '' rootSet (minpoly ℚ α) ℂ)).Nonempty := by
  rw [toFinset_nonempty]
  apply Set.Nonempty.image
  rw [← range_eval_eq_rootSet_minpoly]
  apply range_nonempty

theorem range_embeddings_eq {j : Fin h} (α : K) : (Set.range fun σ : (Fin h) → K →+* ℂ => σ j α) =
    Set.range fun φ : K →+* ℂ => φ α :=
  ext (fun _ => Iff.symm (Function.Surjective.exists fun b => Exists.intro (fun _ => b) rfl))

/-- The house of `α` is the largest modulus of its conjugates.-/
abbrev House (α : K) : ℝ :=
  (Complex.abs '' rootSet (minpoly ℚ α) ℂ).toFinset.max' (rootSet_abs_nonempty α)

theorem rootSet_abs_nonempty' {j : Fin h} (α : K) :
    (toFinset (⇑Complex.abs '' range fun σ : Fin h → K →+* ℂ => σ j α)).Nonempty := by
  rw [toFinset_nonempty]; apply Set.Nonempty.image; apply range_nonempty

theorem house_modulus_eq_max {j : Fin h} (α : K) :
  House α = (Finset.max' (toFinset (⇑Complex.abs ''
    (Set.range fun σ : (Fin h) → K →+* ℂ => σ j α))) (rootSet_abs_nonempty' α)) := by
  apply Finset.max'_eq_of_eq (rootSet_abs_nonempty α) (rootSet_abs_nonempty' α)
  rw [toFinset_inj.mpr (congrArg (Set.image ⇑Complex.abs) (range_embeddings_eq α))]
  apply toFinset_inj.mpr
  rw [range_eval_eq_rootSet_minpoly]

/-- `c` is defined as the product of the maximum absolute value of the entries of the
 inverse of the matrix `B` and  `h`. -/
def c := @Matrix.maxAbsEntry K _ _ basisMatrixTranspose⁻¹ * h

theorem remark (α : 𝓞 K) : ∀ i, Complex.abs (basisReindex.repr α i) ≤
    @c K _ _ * House (algebraMap (𝓞 K) K α) := by

  intros i

  let σ := (Fintype.equivFinOfCardEq (card K ℂ)).symm

  let c' := @Matrix.maxAbsEntry K _ _ basisMatrixTranspose⁻¹

  calc Complex.abs (basisReindex.repr α i) =
    Complex.abs (∑ j, (basisMatrixTranspose)⁻¹ i j *  σ _ (algebraMap (𝓞 K) K α)) := by
    {
      haveI : Invertible (@basisMatrixTranspose K _ _ ) := by
        have : (@basisMatrixTranspose K  _ _ ).det ≠ 0 := by
          rw [(det_transpose (basisMatrixTranspose)).symm,
            ← embeddings_matrix_reindex_eq_basis_matrix_transpose,
            ← pow_ne_zero_iff two_ne_zero,
            ← discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ ((reindex (integralBasis K)
               (Fin.equivChooseBasisIndex).symm))
               ((Fintype.equivFinOfCardEq (card K ℂ)).symm.trans RingHom.equivRatAlgHom)]
          convert (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
           (discr_not_zero_of_basis ℚ ( reindex (integralBasis K)
             (Fin.equivChooseBasisIndex).symm))
        exact invertibleOfIsUnitDet _ (Ne.isUnit this)

      have getEntries : (basisMatrixTranspose)⁻¹.mulVec
         (fun j => σ j (algebraMap (𝓞 K) K α)) i = basisReindex.repr α i := by
        have : (fun j => σ j (algebraMap (𝓞 K) K α)) =
          (basisMatrixTranspose) *ᵥ fun {i} => (basisReindex.repr α) i := by
          ext j
          nth_rewrite 1 [← sum_repr basisReindex α]
          unfold basisMatrixTranspose embeddingsMatrixReindex
            RingHom.equivRatAlgHom embeddingsMatrix RingHom.toRatAlgHom algebraMap
            toRingHom Matrix.reindex
          simp only [id.map_eq_id, Subalgebra.toSubsemiring_subtype, RingHomCompTriple.comp_eq,
             coe_reindex, Equiv.symm_symm, Function.comp_apply, zsmul_eq_mul, map_sum,
             _root_.map_mul, map_intCast, RingHom.coe_coe, Subalgebra.coe_val, Equiv.refl_symm,
             Equiv.coe_refl, Equiv.coe_trans, Equiv.coe_fn_mk, transpose_submatrix, mulVec,
             dotProduct, submatrix_apply, Function.comp_apply, id_eq, transpose_apply, of_apply,
             AlgHom.coe_mk]
          rw [Fintype.sum_congr]
          intros i
          rw [mul_comm]
        rw [Matrix.inv_mulVec_eq this]
      rw [← getEntries]
      rfl
      }
       _ ≤ ∑ _, c' * Complex.abs (σ _ (algebraMap (𝓞 K) K α)) := by
           trans
           ·  trans
              · apply AbsoluteValue.sum_le Complex.abs
              · apply sum_le_sum
                intros j _
                exact (AbsoluteValue.map_mul Complex.abs _ _).le
           · apply sum_le_sum
             intros j _
             apply mul_le_mul_of_nonneg_right
             · simp only [c', Matrix.maxAbsEntry, Finset.max'OfFintype, max' ,image_univ,
                  toFinset_range, id_eq, sup'_image, Function.comp_apply, le_sup'_iff,
                  Finset.mem_univ, true_and]
               use i
               use j
             · exact AbsoluteValue.nonneg Complex.abs _
       _ ≤ ∑ _, c' * House (algebraMap (𝓞 K) K α) := by
          apply sum_le_sum
          intros j _
          apply mul_le_mul_of_nonneg_left
          · rw [house_modulus_eq_max (algebraMap (𝓞 K) K α)]
            apply le_max'
            simp only [toFinset_image, toFinset_range, Finset.mem_image, Finset.mem_univ, true_and,
              exists_exists_eq_and]
            use σ
          · simp only [c', Matrix.maxAbsEntry, Finset.max'OfFintype, max', image_univ,
            toFinset_range, id_eq, sup'_image, Function.comp_apply, le_sup'_iff, Finset.mem_univ,
            apply_nonneg, and_self, exists_const, true_and]
            use i
            use j
       _ =  c' * h * House  (algebraMap (𝓞 K) K α) := by
        rw [sum_const, Finset.card_fin, nsmul_eq_mul, ← mul_assoc,
            mul_comm ↑h (Matrix.maxAbsEntry (basisMatrixTranspose)⁻¹)]

end section
