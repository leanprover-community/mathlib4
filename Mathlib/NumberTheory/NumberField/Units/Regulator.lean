/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Regulator of a number field

We define and prove basic results about the regulator of a number field `K`.

## Main definitions and results

* `NumberField.Units.regOfFamily`: the regulator of a family of units of `K`.

* `NumberField.Units.regulator`: the regulator of the number field `K`.

* `Number.Field.Units.regOfFamily_eq_det`: For any infinite place `w'`, the regulator of the
family `u` is equal to the absolute value of the determinant of the matrix
`(mult w * log w (u i)))_i, w` where `w` runs through the infinite places distinct from `w'`.


## Tags
number field, units, regulator
-/

open scoped NumberField

noncomputable section

namespace NumberField.Units

variable (K : Type*) [Field K]

open MeasureTheory NumberField.InfinitePlace Module Submodule
  NumberField NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

open scoped Classical in
/--
An `equiv` between `Fin (rank K)`, used to index the family of units, and `{w // w ≠ w₀}`
the index of the `logSpace`.
-/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

section regOfFamily

open Matrix

variable {K}

/--
A family of units is of maximal rank if its image by `logEmbedding` is linearly independent
over `ℝ`.
-/
def IsMaxRank (u : Fin (rank K) → (𝓞 K)ˣ) : Prop :=
  LinearIndependent ℝ (fun i ↦ logEmbedding K (Additive.ofMul (u i)))

/--
The images by `logEmbedding` of a family of units of maximal rank form a basis of `logSpace K`.
-/
def basisOfIsMaxRank {u : Fin (rank K) → (𝓞 K)ˣ} (hu : IsMaxRank u) :
    Basis (Fin (rank K)) ℝ (logSpace K) := by
  classical
  exact (basisOfPiSpaceOfLinearIndependent
    ((linearIndependent_equiv (equivFinRank K).symm).mpr hu)).reindex (equivFinRank K).symm

theorem basisOfIsMaxRank_apply {u : Fin (rank K) → (𝓞 K)ˣ} (hu : IsMaxRank u) (i : Fin (rank K)) :
    (basisOfIsMaxRank hu) i = logEmbedding K (Additive.ofMul (u i)) := by
  classical
  simp [basisOfIsMaxRank, Basis.coe_reindex,  Equiv.symm_symm, Function.comp_apply,
    coe_basisOfPiSpaceOfLinearIndependent]

theorem finiteIndex_iff_sup_torsion_finiteIndex (s : Subgroup (𝓞 K)ˣ) :
    s.FiniteIndex ↔ (s ⊔ torsion K).FiniteIndex := by
  refine ⟨fun h ↦ Subgroup.finiteIndex_of_le le_sup_left, fun h ↦ ?_⟩
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relindex_mul_index (le_sup_left : s ≤ s ⊔ torsion K)]
  refine Nat.mul_ne_zero ?_ (Subgroup.finiteIndex_iff.mp h)
  rw [Subgroup.relindex_sup_left]
  exact Subgroup.FiniteIndex.index_ne_zero

open Subgroup in
/--
A family of units is of maximal rank iff the index of the subgroup it generates has finite index.
-/
theorem isMaxRank_iff_closure_finiteIndex {u : Fin (rank K) → (𝓞 K)ˣ} :
    IsMaxRank u ↔ (closure (Set.range u)).FiniteIndex := by
  classical
  have h₁ : (closure (Set.range u) ⊔ torsion K).index ≠ 0 ↔
      Finite (unitLattice K ⧸ span ℤ (Set.range ((logEmbeddingEquiv K) ∘ Additive.toMul.symm ∘
        QuotientGroup.mk ∘ u))) := by
    change _ ↔ Finite ((unitLattice K).toAddSubgroup ⧸ (span ℤ (Set.range _)).toAddSubgroup)
    rw [← AddSubgroup.index_ne_zero_iff_finite]
    have := index_map (closure (Set.range u)) (QuotientGroup.mk' (torsion K))
    rw [QuotientGroup.ker_mk', QuotientGroup.range_mk', index_top, mul_one] at this
    rw [← this, ← index_toAddSubgroup, ← AddSubgroup.index_map_equiv
      _ (logEmbeddingEquiv K).toAddEquiv, Set.range_comp, ← map_span (logEmbeddingEquiv K),
      ← map_coe_toLinearMap, map_toAddSubgroup, span_int_eq_addSubgroup_closure,
      MonoidHom.map_closure, toAddSubgroup_closure, Set.range_comp, Set.range_comp,
      QuotientGroup.coe_mk',  Set.preimage_equiv_eq_image_symm]
    exact Iff.rfl
  have h₂ : DiscreteTopology
      (span ℤ (Set.range fun i ↦ (logEmbedding K) (Additive.ofMul (u i)))) := by
    refine DiscreteTopology.of_subset (inferInstance : DiscreteTopology (unitLattice K)) ?_
    rw [SetLike.coe_subset_coe, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Additive.ofMul (u i), mem_top, rfl⟩
  rw [finiteIndex_iff_sup_torsion_finiteIndex, finiteIndex_iff, h₁, finiteQuotient_iff,
    unitLattice_rank, ← Set.finrank, IsMaxRank, linearIndependent_iff_card_eq_finrank_span,
    Real.finrank_eq_int_finrank_of_discrete h₂, Set.finrank, Set.finrank, ← finrank_map_subtype_eq,
    map_span, ← Set.range_comp', eq_comm]
  simp

/--
The regulator of a family of units of `K`.
-/
def regOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) : ℝ := by
  classical
  by_cases hu : isMaxRank u
  · exact ZLattice.covolume (span ℤ (Set.range (basisOfIsMaxRank  hu)))
  · exact 0

theorem regOfFamily_eq_zero {u : Fin (rank K) → (𝓞 K)ˣ} (hu : ¬ isMaxRank u) :
    regOfFamily u = 0 := by
  rw [regOfFamily, dif_neg hu]

open scoped Classical in
theorem regOfFamily_of_isMaxRank {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) :
    regOfFamily u = ZLattice.covolume (span ℤ (Set.range (basisOfIsMaxRank  hu))) := by
  rw [regOfFamily, dif_pos hu]

theorem regOfFamily_pos {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) :
    0 < regOfFamily u := by
  classical
  rw [regOfFamily_of_isMaxRank hu]
  exact ZLattice.covolume_pos _ volume

theorem regOfFamily_ne_zero {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) :
    regOfFamily u ≠ 0 := (regOfFamily_pos hu).ne'

theorem regOfFamily_ne_zero_iff {u : Fin (rank K) → (𝓞 K)ˣ} :
    regOfFamily u ≠ 0 ↔ isMaxRank u :=
  ⟨by simpa using (fun hu ↦ regOfFamily_eq_zero hu).mt, fun hu ↦ regOfFamily_ne_zero hu⟩

open scoped Classical in
theorem regOfFamily_eq_det' (u : Fin (rank K) → (𝓞 K)ˣ) :
    regOfFamily u =
      |(of fun i ↦ logEmbedding K (Additive.ofMul (u ((equivFinRank K).symm i)))).det| := by
  by_cases hu : isMaxRank u
  · rw [regOfFamily_of_isMaxRank hu, ZLattice.covolume_eq_det _
      (((basisOfIsMaxRank hu).restrictScalars ℤ).reindex (equivFinRank K)), Basis.coe_reindex]
    congr with i
    simp [basisOfIsMaxRank_apply hu]
  · rw [regOfFamily_eq_zero hu, det_eq_zero_of_not_linearIndependent_rows, abs_zero]
    rwa [IsMaxRank, ← linearIndependent_equiv (equivFinRank K).symm] at hu

open scoped Classical in
/--
Let `u : Fin (rank K) → (𝓞 K)ˣ` be a family of units and let `w₁` and `w₂` be two infinite
places. Then, the two square matrices with entries `(mult w * log w (u i))_i` where `w ≠ w_j` for
`j = 1, 2` have the same determinant in absolute value.
-/
theorem abs_det_eq_abs_det (u : Fin (rank K) → (𝓞 K)ˣ)
    {w₁ w₂ : InfinitePlace K} (e₁ : {w // w ≠ w₁} ≃ Fin (rank K))
    (e₂ : {w // w ≠ w₂} ≃ Fin (rank K)) :
    |(of fun i w : {w // w ≠ w₁} ↦ (mult w.val : ℝ) * (w.val (u (e₁ i) : K)).log).det| =
    |(of fun i w : {w // w ≠ w₂} ↦ (mult w.val : ℝ) * (w.val (u (e₂ i) : K)).log).det| := by
  -- We construct an equiv `Fin (rank K + 1) ≃ InfinitePlace K` from `e₂.symm`
  let f : Fin (rank K + 1) ≃ InfinitePlace K :=
    (finSuccEquiv _).trans ((Equiv.optionSubtype _).symm e₁.symm).val
  -- And `g` corresponds to the restriction of `f⁻¹` to `{w // w ≠ w₂}`
  let g : {w // w ≠ w₂} ≃ Fin (rank K) :=
    (Equiv.subtypeEquiv f.symm (fun _ ↦ by simp [f])).trans
      (finSuccAboveEquiv (f.symm w₂)).symm
  have h_col := congr_arg abs <| det_permute (g.trans e₂.symm)
    (of fun i w : {w // w ≠ w₂} ↦ (mult w.val : ℝ) * (w.val (u (e₂ i) : K)).log)
  rw [abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul] at h_col
  rw [← h_col]
  have h := congr_arg abs <| submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'
    (of fun i w ↦ (mult (f w) : ℝ) * ((f w) (u i)).log) ?_ 0 (f.symm w₂)
  · rw [← det_reindex_self e₁, ← det_reindex_self g]
    · rw [Units.smul_def, abs_zsmul, Int.abs_negOnePow, one_smul] at h
      convert h
      · ext; simp only [ne_eq, reindex_apply, submatrix_apply, of_apply, Equiv.apply_symm_apply,
          Equiv.trans_apply, Fin.succAbove_zero, id_eq, finSuccEquiv_succ,
          Equiv.optionSubtype_symm_apply_apply_coe, f]
      · ext; simp only [ne_eq, Equiv.coe_trans, reindex_apply, submatrix_apply, Function.comp_apply,
          Equiv.apply_symm_apply, id_eq, of_apply]; rfl
  · intro _
    simp_rw [of_apply, ← Real.log_pow]
    rw [← Real.log_prod, Equiv.prod_comp f (fun w ↦ (w (u _) ^ (mult w))), prod_eq_abs_norm,
      Units.norm, Rat.cast_one, Real.log_one]
    exact fun _ _ ↦ pow_ne_zero _ <| (map_ne_zero _).mpr (coe_ne_zero _)

open scoped Classical in
/--
For any infinite place `w'`, the regulator of the family `u` is equal to the absolute value of
the determinant of the matrix with entries `(mult w * log w (u i))_i` for `w ≠ w'`.
<<<<<<< HEAD
-/
theorem regOfFamily_eq_det (u : Fin (rank K) → (𝓞 K)ˣ) (w' : InfinitePlace K)
    (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    regOfFamily u =
      |(of fun i w : {w // w ≠ w'} ↦ (mult w.val : ℝ) * Real.log (w.val (u (e i) : K))).det| := by
  rw [regOfFamily_eq_det', abs_det_eq_abs_det u e (equivFinRank K).symm]
  simp [logEmbedding]
=======
-/
theorem regOfFamily_eq_det (u : Fin (rank K) → (𝓞 K)ˣ) (w' : InfinitePlace K)
    (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    regOfFamily u =
      |(of fun i w : {w // w ≠ w'} ↦ (mult w.val : ℝ) * Real.log (w.val (u (e i) : K))).det| := by
  simp [regOfFamily_eq_det', abs_det_eq_abs_det u e (equivFinRank K).symm, logEmbedding]

open scoped Classical in
/--
The degree of `K` times the regulator of the family `u` is equal to the absolute value of the
determinant of the matrix whose columns are
`(mult w * log w (fundSystem K i))_i, w` and the column `(mult w)_w`.
-/
theorem finrank_mul_regOfFamily_eq_det (u : Fin (rank K) → (𝓞 K)ˣ) (w' : InfinitePlace K)
    (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    finrank ℚ K * regOfFamily u =
      |(of (fun i w : InfinitePlace K ↦
        if h : i = w' then (w.mult : ℝ) else w.mult * (w (u (e ⟨i, h⟩))).log)).det| := by
  let f : Fin (rank K + 1) ≃ InfinitePlace K :=
    (finSuccEquiv _).trans ((Equiv.optionSubtype _).symm e.symm).val
  let g : {w // w ≠ w'} ≃ Fin (rank K) :=
    (Equiv.subtypeEquiv f.symm (fun _ ↦ by simp [f])).trans (finSuccAboveEquiv (f.symm w')).symm
  rw [← det_reindex_self f.symm, det_eq_sum_row_mul_submatrix_succAbove_succAbove_det _ (f.symm w')
    (f.symm w'), abs_mul, abs_mul, abs_neg_one_pow, one_mul]
  · simp_rw [reindex_apply, submatrix_submatrix, ← f.symm.sum_comp, f.symm_symm, submatrix_apply,
      Function.comp_def, Equiv.apply_symm_apply, of_apply, dif_pos, ← Nat.cast_sum, sum_mult_eq,
      Nat.abs_cast]
    rw [regOfFamily_eq_det u w' e, ← Matrix.det_reindex_self g]
    congr with i j
    rw [reindex_apply, submatrix_apply, submatrix_apply, of_apply, of_apply, dif_neg]
    rfl
  · simp_rw [Equiv.forall_congr_left f, ← f.symm.sum_comp, reindex_apply, submatrix_apply,
      of_apply, f.symm_symm, f.apply_symm_apply, Finset.sum_dite_irrel, ne_eq,
      EmbeddingLike.apply_eq_iff_eq]
    intro _ h
    rw [dif_neg h, sum_mult_mul_log]

end regOfFamily

open scoped Classical in
/-- The regulator of a number field `K`. -/
def regulator : ℝ := ZLattice.covolume (unitLattice K)

theorem isMaxRank_fundSystem :
    IsMaxRank (fundSystem K) := by
  classical
  convert ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)).linearIndependent
  rw [logEmbedding_fundSystem, Basis.ofZLatticeBasis_apply]

open scoped Classical in
theorem basisOfIsMaxRank_fundSystem :
    basisOfIsMaxRank (isMaxRank_fundSystem K) = (basisUnitLattice K).ofZLatticeBasis ℝ := by
  ext
  rw [Basis.ofZLatticeBasis_apply, basisOfIsMaxRank_apply, logEmbedding_fundSystem]

theorem regulator_eq_regOfFamily_fundSystem :
    regulator K = regOfFamily (fundSystem K) := by
  classical
  rw [regOfFamily_of_isMaxRank (isMaxRank_fundSystem K), regulator,
    ← (basisUnitLattice K).ofZLatticeBasis_span ℝ, basisOfIsMaxRank_fundSystem]

theorem regulator_pos : 0 < regulator K :=
  regulator_eq_regOfFamily_fundSystem K ▸ regOfFamily_pos (isMaxRank_fundSystem K)

theorem regulator_ne_zero : regulator K ≠ 0 :=
  (regulator_pos K).ne'

open scoped Classical in
theorem regulator_eq_det' :
    regulator K = |(Matrix.of fun i ↦
      logEmbedding K (Additive.ofMul (fundSystem K ((equivFinRank K).symm i)))).det| := by
  rw [regulator_eq_regOfFamily_fundSystem, regOfFamily_eq_det']

open scoped Classical in
/--
For any infinite place `w'`, the regulator is equal to the absolute value of the determinant
of the matrix with entries `(mult w * log w (fundSystem K i))_i` for `w ≠ w'`.
-/
theorem regulator_eq_det (w' : InfinitePlace K) (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    regulator K =
      |(Matrix.of fun i w : {w // w ≠ w'} ↦ (mult w.val : ℝ) *
        Real.log (w.val (fundSystem K (e i) : K))).det| := by
  rw [regulator_eq_regOfFamily_fundSystem, regOfFamily_eq_det]
>>>>>>> origin/master

open scoped Classical in
/--
The degree of `K` times the regulator of the family `u` is equal to the absolute value of the
determinant of the matrix whose columns are
`(mult w * log w (fundSystem K i))_i, w` and the column `(mult w)_w`.
-/
<<<<<<< HEAD
theorem finrank_mul_regOfFamily_eq_det (u : Fin (rank K) → (𝓞 K)ˣ) (w' : InfinitePlace K)
    (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    finrank ℚ K * regOfFamily u =
      |(of (fun i w : InfinitePlace K ↦
        if h : i = w' then (w.mult : ℝ) else w.mult * (w (u (e ⟨i, h⟩))).log)).det| := by
  let f : Fin (rank K + 1) ≃ InfinitePlace K :=
    (finSuccEquiv _).trans ((Equiv.optionSubtype _).symm e.symm).val
  let g : {w // w ≠ w'} ≃ Fin (rank K) :=
    (Equiv.subtypeEquiv f.symm (fun _ ↦ by simp [f])).trans (finSuccAboveEquiv (f.symm w')).symm
  rw [← det_reindex_self f.symm, det_eq_sum_row_mul_submatrix_succAbove_succAbove_det _ (f.symm w')
    (f.symm w'), abs_mul, abs_mul, abs_neg_one_pow, one_mul]
  · simp_rw [reindex_apply, submatrix_submatrix, ← f.symm.sum_comp, f.symm_symm, submatrix_apply,
      Function.comp_def, Equiv.apply_symm_apply, of_apply, dif_pos, ← Nat.cast_sum, sum_mult_eq,
      Nat.abs_cast]
    rw [regOfFamily_eq_det u w' e, ← Matrix.det_reindex_self g]
    congr with i j
    rw [reindex_apply, submatrix_apply, submatrix_apply, of_apply, of_apply, dif_neg]
    rfl
  · simp_rw [Equiv.forall_congr_left f, ← f.symm.sum_comp, reindex_apply, submatrix_apply,
      of_apply, f.symm_symm, f.apply_symm_apply, Finset.sum_dite_irrel, ne_eq,
      EmbeddingLike.apply_eq_iff_eq]
    intro _ h
    rw [dif_neg h, sum_mult_mul_log]
=======
theorem finrank_mul_regulator_eq_det (w' : InfinitePlace K) (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    finrank ℚ K * regulator K =
      |(Matrix.of (fun i w : InfinitePlace K ↦
        if h : i = w' then (w.mult : ℝ) else w.mult * (w (fundSystem K (e ⟨i, h⟩))).log)).det| := by
  rw [regulator_eq_regOfFamily_fundSystem, finrank_mul_regOfFamily_eq_det]
>>>>>>> origin/master

end regOfFamily

open scoped Classical in
/-- The regulator of a number field `K`. -/
def regulator : ℝ := ZLattice.covolume (unitLattice K)

theorem isMaxRank_fundSystem :
    isMaxRank (fundSystem K) := by
  classical
  convert ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)).linearIndependent
  rw [logEmbedding_fundSystem, Basis.ofZLatticeBasis_apply]

open scoped Classical in
theorem basisOfIsMaxRank_fundSystem :
    basisOfIsMaxRank (isMaxRank_fundSystem K) = (basisUnitLattice K).ofZLatticeBasis ℝ := by
  ext
  rw [Basis.ofZLatticeBasis_apply, basisOfIsMaxRank_apply, logEmbedding_fundSystem]

theorem regulator_eq_regOfFamily_fundSystem :
    regulator K = regOfFamily (fundSystem K) := by
  classical
  rw [regOfFamily_of_isMaxRank (isMaxRank_fundSystem K), regulator,
    ← (basisUnitLattice K).ofZLatticeBasis_span ℝ, basisOfIsMaxRank_fundSystem]

theorem regulator_pos : 0 < regulator K :=
  regulator_eq_regOfFamily_fundSystem K ▸ regOfFamily_pos (isMaxRank_fundSystem K)

theorem regulator_ne_zero : regulator K ≠ 0 :=
  (regulator_pos K).ne'

end Units

end NumberField
