import Mathlib.NumberTheory.NumberField.Embeddings

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional Matrix
  Set Algebra Polynomial Basis Finset

variable {K : Type*} [Field K] [NumberField K]

local notation "h" => finrank ℚ K

theorem matricesMulLeft {u v : Fin h → ℂ} {M : Matrix (Fin h) (Fin h) ℂ} [Invertible M]
    (hM : u = M.mulVec v) : M⁻¹.mulVec u = v := by
  simp only [hM, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

theorem max0fEqSets {γ : Type _} [LinearOrder γ] {s t : Finset γ} (hs : s.Nonempty)
  (ht : t.Nonempty) (hst : s = t) : s.max' hs = t.max' ht := by simp_rw [hst]

/-- `maxFinFun` takes a function `f` from a finite and nonempty type `s` to a
  linearly ordered type `γ`, and returns the maximum value of `f` over all elements of `s`. -/
def maxFinFun {s γ : Type _} [Fintype s] [Nonempty s] (f : Π _ : s, γ) [LinearOrder γ] : γ := by
  apply Finset.max' (f '' Set.univ).toFinset
  simp only [Set.image_univ, Set.toFinset_range, Finset.image_nonempty]
  exact Finset.univ_nonempty

/-- `maxFinFunMatrix` takes a matrix `B` of size `finrank ℚ K` and returns the maximum
  absolute value of its entries. This is done by first finding the maximum absolute value of the
  entries in each row, and then finding the maximum of those row maxima. -/
noncomputable def maxFinFunMatrix (B : Matrix (Fin (finrank ℚ K)) (Fin (finrank ℚ K)) ℂ) := by
  letI : Nonempty (Fin (finrank ℚ K)) := Fin.pos_iff_nonempty.mp (finrank_pos)
  apply maxFinFun (fun i => maxFinFun (fun j => Complex.abs (B i j)))

noncomputable section

/-- There is noncomputably a bijection between `Fin h` and the set of embeddings from `K` to `ℂ`-/
abbrev σ : Fin h ≃ (K →+* ℂ) := (Fintype.equivFinOfCardEq (card K ℂ)).symm

/-- There is noncomputably a bijection between `Fin h` and `ChooseBasisIndex ℤ (𝓞 K)`
 composing the equivalence `σ` with an equivalence derived from the cardinality of
the embeddings and the cardinality of the integral basis of `K`.-/
abbrev f : Fin h ≃ ChooseBasisIndex ℤ (𝓞 K) :=
  σ.trans (equivOfCardEq ((card K ℂ).trans (finrank_eq_card_basis (integralBasis K))))

/-- `b` is a basis of `𝓞 K` over `ℤ` by reindexing the basis
provided by `RingOfIntegers.basis K` using the inverse of the equivalence `f`.-/
abbrev b : Basis (Fin h) ℤ (𝓞 K) := (RingOfIntegers.basis K).reindex f.symm

/-- `B` is the matrix whose `(i, j)` coefficient is `σⱼ (b i)`. -/
def B : Matrix (Fin h) (Fin h) ℂ := ((embeddingsMatrixReindex ℚ ℂ
  (fun i => algebraMap (𝓞 K) K (b i)) (σ.trans (RingHom.equivRatAlgHom)))).transpose

theorem matricesequal : ((embeddingsMatrixReindex ℚ ℂ (fun i =>
    (( reindex (integralBasis K) f.symm) i)) (σ.trans (RingHom.equivRatAlgHom)))) =
     (@B K  _ _).transpose := by
  simp only [ B, integralBasis,  coe_reindex, Equiv.symm_symm, Function.comp_apply,
     localizationLocalization_apply, transpose_transpose]

theorem trial {i j : Fin h} : B i j = σ i (algebraMap (𝓞 K) K (b j)) := rfl

theorem hmax (α : K) : (toFinset (⇑Complex.abs '' rootSet (minpoly ℚ α) ℂ)).Nonempty := by
  rw [toFinset_nonempty]
  apply Set.Nonempty.image
  rw [← range_eval_eq_rootSet_minpoly]
  apply range_nonempty

theorem hnewsets {j : Fin h} (α : K) : (Set.range fun σ : (Fin h) → K →+* ℂ => σ j α) =
    Set.range fun φ : K →+* ℂ => φ α :=
  ext (fun _ => Iff.symm (Function.Surjective.exists fun b => Exists.intro (fun _ => b) rfl))

/-- The house of `α` is the largest modulus of its conjugates.-/
abbrev House (α : K) : ℝ := (Complex.abs '' rootSet (minpoly ℚ α) ℂ).toFinset.max' (hmax α)

theorem hmax' {j : Fin h} (α : K) :
  (toFinset (⇑Complex.abs '' range fun σ : Fin h → K →+* ℂ => σ j α)).Nonempty := by
  rw [toFinset_nonempty]; apply Set.Nonempty.image; apply range_nonempty

theorem switch {j : Fin h} (α : K) : House α = (Finset.max' (toFinset (⇑Complex.abs ''
    (Set.range fun σ : (Fin h) → K →+* ℂ => σ j α))) (hmax' α)) := by
  apply max0fEqSets (hmax α) (hmax' α)
  rw [toFinset_inj.mpr (congrArg (Set.image ⇑Complex.abs) (hnewsets α))]
  apply toFinset_inj.mpr
  rw [range_eval_eq_rootSet_minpoly]

/-- `c` is defined as the product of the maximum absolute value of the entries of the
 inverse of the matrix `B` and  `h`. -/
def c := @maxFinFunMatrix K _ _ B⁻¹ * h

theorem remark (α : 𝓞 K) : ∀ i, Complex.abs (b.repr α i) ≤
  @c K _ _ * House (algebraMap (𝓞 K) K α) := by

  intros i

  let c' := @maxFinFunMatrix K _ _ B⁻¹

  calc Complex.abs (b.repr α i) = Complex.abs (∑ j, B⁻¹ i j *  σ _ (algebraMap (𝓞 K) K α)) := by
    {
      haveI : Invertible (@B K _ _ ) := by
        have : (@B K  _ _ ).det ≠ 0 := by
          rw [(det_transpose B).symm, ← matricesequal, ← pow_ne_zero_iff two_ne_zero,
            ← discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ ((reindex (integralBasis K) f.symm))
            ((Fintype.equivFinOfCardEq (card K ℂ)).symm.trans RingHom.equivRatAlgHom)]
          convert (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
           (discr_not_zero_of_basis ℚ ( reindex (integralBasis K) f.symm))
        exact invertibleOfIsUnitDet _ (Ne.isUnit this)

      have getBmatrixEntries : B⁻¹.mulVec (fun j => σ j (algebraMap (𝓞 K) K α)) i = b.repr α i := by
        have : (fun j => σ j (algebraMap (𝓞 K) K α)) = B *ᵥ fun {i} => (b.repr α) i := by
          ext j
          nth_rewrite 1 [← sum_repr b α]
          unfold B embeddingsMatrixReindex RingHom.equivRatAlgHom embeddingsMatrix
            RingHom.toRatAlgHom algebraMap toRingHom Matrix.reindex
          simp only [id.map_eq_id, Subalgebra.toSubsemiring_subtype, RingHomCompTriple.comp_eq,
             coe_reindex, Equiv.symm_symm, Function.comp_apply, zsmul_eq_mul, map_sum,
             _root_.map_mul, map_intCast, RingHom.coe_coe, Subalgebra.coe_val, Equiv.refl_symm,
             Equiv.coe_refl, Equiv.coe_trans, Equiv.coe_fn_mk, transpose_submatrix, mulVec,
             dotProduct, submatrix_apply, Function.comp_apply, id_eq, transpose_apply, of_apply,
             AlgHom.coe_mk]
          rw [Fintype.sum_congr]
          intros i
          rw [mul_comm]
        rw [matricesMulLeft this]
      rw [← getBmatrixEntries]
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
             · simp only [c', maxFinFunMatrix, maxFinFun, max' ,image_univ, toFinset_range, id_eq,
                 sup'_image, Function.comp_apply, le_sup'_iff, Finset.mem_univ, true_and]
               use i
               use j
             · exact AbsoluteValue.nonneg Complex.abs _
       _ ≤ ∑ _, c' * House  (algebraMap (𝓞 K) K α) := by
          apply sum_le_sum
          intros j _
          apply mul_le_mul_of_nonneg_left
          · rw [switch (algebraMap (𝓞 K) K α)]
            apply le_max'
            simp only [toFinset_image, toFinset_range, Finset.mem_image, Finset.mem_univ, true_and,
              exists_exists_eq_and]
            use σ
          · simp only [c', maxFinFunMatrix, maxFinFun, max', image_univ, toFinset_range, id_eq,
              sup'_image, Function.comp_apply, le_sup'_iff, Finset.mem_univ, apply_nonneg, and_self,
              exists_const, true_and]
            use i
            use j
       _ =  c' * h * House  (algebraMap (𝓞 K) K α) := by
        rw [sum_const, Finset.card_fin, nsmul_eq_mul, ← mul_assoc, mul_comm ↑h (maxFinFunMatrix B⁻¹)]

end section
