/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

import Mathlib.Sandbox

/-!
# Regulator of a number field

We define and prove basic results about the regulator of a number field `K`.

## Main definitions and results

* `NumberField.Units.regulator`: the regulator of the number field `K`.

* `Number.Field.Units.regulator_eq_det`: For any infinite place `w'`, the regulator is equal to
the absolute value of the determinant of the matrix `(mult w * log w (fundSystem K i)))_i, w`
where `w` runs through the infinite places distinct from `w'`.

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
 Docstring.
 -/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

variable {K} in
def regOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) : ℝ := by
  classical
  by_cases hu : LinearIndependent ℝ (fun i ↦ logEmbedding K (Additive.ofMul (u i)))
  · exact ZLattice.covolume <| span ℤ <| Set.range <|
      basisOfPiSpaceOfLinearIndependent <| (linearIndependent_equiv (equivFinRank K).symm).mpr hu
  · exact 0

-- variable {K} in
-- def regOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) : ℝ := by
--   classical
--   by_cases hr :  0 < rank K
--   · by_cases hu : isMaxRank u
--     · have : Nonempty (Fin (rank K)) := Fin.pos_iff_nonempty.mp hr
--       let B := basisOfLinearIndependentOfCardEqFinrank hu
--         (by rw [Units.finrank_eq_rank, Fintype.card_fin])
--       exact ZLattice.covolume (span ℤ (Set.range B))
--     · exact 0
--   · exact 1

variable {K} in
theorem regOfFamily_eq_zero {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : ¬ LinearIndependent ℝ (fun i ↦ logEmbedding K (Additive.ofMul (u i)))) :
    regOfFamily u = 0 := by
  rw [regOfFamily, dif_neg hu]

open scoped Classical in
/-- The regulator of a number field `K`. -/
def regulator : ℝ := ZLattice.covolume (unitLattice K)

example : regulator K = regOfFamily (fundSystem K) := by
  classical
  simp only [regOfFamily, logEmbedding_fundSystem]
  rw [regulator, dif_pos]
  · simp only [coe_basisOfPiSpaceOfLinearIndependent, Function.comp_def]
    simp_rw [← ((basisUnitLattice K).reindex (equivFinRank K)).ofZLatticeBasis_span ℝ]
    congr! with i
    rw [Basis.ofZLatticeBasis_apply, Basis.reindex_apply]
  · convert ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)).linearIndependent
    simp [logEmbedding_fundSystem, Basis.ofZLatticeBasis_apply]

open scoped Classical in
theorem regulator_ne_zero : regulator K ≠ 0 := ZLattice.covolume_ne_zero (unitLattice K) volume

open scoped Classical in
theorem regulator_pos : 0 < regulator K := ZLattice.covolume_pos (unitLattice K) volume

open scoped Classical in
example (u :  Fin (rank K) → (𝓞 K)ˣ) (e : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K)) :
    regOfFamily u = |(Matrix.of fun i ↦ logEmbedding K (Additive.ofMul (u (e i)))).det| := by
  by_cases hu : LinearIndependent ℝ (fun i ↦ logEmbedding K (Additive.ofMul (u i)))
  ·
    rw [regOfFamily, dif_pos hu, ZLattice.covolume_eq_det]
    sorry


  · have := (linearIndependent_equiv e).not.mpr hu
    simp_rw [Function.comp_def] at this
    rw [regOfFamily_eq_zero hu, Matrix.det_eq_zero_iff.mpr this, abs_zero]

open scoped Classical in
theorem regulator_eq_det' (e : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K)) :
    regulator K = |(Matrix.of fun i ↦
      logEmbedding K (Additive.ofMul (fundSystem K (e i)))).det| := by
  simp_rw [regulator, ZLattice.covolume_eq_det _
    (((basisModTorsion K).map (logEmbeddingEquiv K)).reindex e.symm), Basis.coe_reindex,
    Function.comp_def, Basis.map_apply, ← fundSystem_mk, Equiv.symm_symm, logEmbeddingEquiv_apply]

open scoped Classical in
/--
Let `u : Fin (rank K) → (𝓞 K)ˣ` be a family of units and let `w₁` and `w₂` be two infinite
places. Then, the two square matrices with entries `(mult w * log w (u i))_i` where `w ≠ w_j` for
`j = 1, 2` have the same determinant in absolute value.
-/
theorem abs_det_eq_abs_det (u : Fin (rank K) → (𝓞 K)ˣ)
    {w₁ w₂ : InfinitePlace K} (e₁ : {w // w ≠ w₁} ≃ Fin (rank K))
    (e₂ : {w // w ≠ w₂} ≃ Fin (rank K)) :
    |(Matrix.of fun i w : {w // w ≠ w₁} ↦ (mult w.val : ℝ) * (w.val (u (e₁ i) : K)).log).det| =
    |(Matrix.of fun i w : {w // w ≠ w₂} ↦ (mult w.val : ℝ) * (w.val (u (e₂ i) : K)).log).det| := by
  -- We construct an equiv `Fin (rank K + 1) ≃ InfinitePlace K` from `e₂.symm`
  let f : Fin (rank K + 1) ≃ InfinitePlace K :=
    (finSuccEquiv _).trans ((Equiv.optionSubtype _).symm e₁.symm).val
  -- And `g` corresponds to the restriction of `f⁻¹` to `{w // w ≠ w₂}`
  let g : {w // w ≠ w₂} ≃ Fin (rank K) :=
    (Equiv.subtypeEquiv f.symm (fun _ ↦ by simp [f])).trans
      (finSuccAboveEquiv (f.symm w₂)).symm
  have h_col := congr_arg abs <| Matrix.det_permute (g.trans e₂.symm)
    (Matrix.of fun i w : {w // w ≠ w₂} ↦ (mult w.val : ℝ) * (w.val (u (e₂ i) : K)).log)
  rw [abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul] at h_col
  rw [← h_col]
  have h := congr_arg abs <| Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'
    (Matrix.of fun i w ↦ (mult (f w) : ℝ) * ((f w) (u i)).log) ?_ 0 (f.symm w₂)
  · rw [← Matrix.det_reindex_self e₁, ← Matrix.det_reindex_self g]
    · rw [Units.smul_def, abs_zsmul, Int.abs_negOnePow, one_smul] at h
      convert h
      · ext; simp only [ne_eq, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
          Equiv.apply_symm_apply, Equiv.trans_apply, Fin.succAbove_zero, id_eq, finSuccEquiv_succ,
          Equiv.optionSubtype_symm_apply_apply_coe, f]
      · ext; simp only [ne_eq, Equiv.coe_trans, Matrix.reindex_apply, Matrix.submatrix_apply,
          Function.comp_apply, Equiv.apply_symm_apply, id_eq, Matrix.of_apply]; rfl
  · intro _
    simp_rw [Matrix.of_apply, ← Real.log_pow]
    rw [← Real.log_prod, Equiv.prod_comp f (fun w ↦ (w (u _) ^ (mult w))), prod_eq_abs_norm,
      Units.norm, Rat.cast_one, Real.log_one]
    exact fun _ _ ↦ pow_ne_zero _ <| (map_ne_zero _).mpr (coe_ne_zero _)

open scoped Classical in
/--
For any infinite place `w'`, the regulator is equal to the absolute value of the determinant
of the matrix with entries `(mult w * log w (fundSystem K i))_i` for `w ≠ w'`.
-/
theorem regulator_eq_det (w' : InfinitePlace K) (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    regulator K =
      |(Matrix.of fun i w : {w // w ≠ w'} ↦ (mult w.val : ℝ) *
        Real.log (w.val (fundSystem K (e i) : K))).det| := by
  let e' : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K) := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank])
  simp_rw [regulator_eq_det' K e', logEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact abs_det_eq_abs_det K (fun i ↦ fundSystem K i) e' e

open scoped Classical in
/--
The degree of `K` times the regulator of `K` is equal to the absolute value of the determinant of
the matrix whose columns are `(mult w * log w (fundSystem K i))_i, w` and the column `(mult w)_w`.
-/
theorem finrank_mul_regulator_eq_det (w' : InfinitePlace K) (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    finrank ℚ K * regulator K =
      |(Matrix.of (fun i w : InfinitePlace K ↦
        if h : i = w' then (w.mult : ℝ) else w.mult * (w (fundSystem K (e ⟨i, h⟩))).log)).det| := by
  let f : Fin (rank K + 1) ≃ InfinitePlace K :=
    (finSuccEquiv _).trans ((Equiv.optionSubtype _).symm e.symm).val
  let g : {w // w ≠ w'} ≃ Fin (rank K) :=
    (Equiv.subtypeEquiv f.symm (fun _ ↦ by simp [f])).trans (finSuccAboveEquiv (f.symm w')).symm
  rw [← Matrix.det_reindex_self f.symm, Matrix.det_eq_sum_row_mul_submatrix_succAbove_succAbove_det
    _ (f.symm w') (f.symm w'), abs_mul, abs_mul, abs_neg_one_pow, one_mul]
  · simp_rw [Matrix.reindex_apply, Matrix.submatrix_submatrix, ← f.symm.sum_comp, f.symm_symm,
      Matrix.submatrix_apply, Function.comp_def, Equiv.apply_symm_apply, Matrix.of_apply,
      dif_pos, ← Nat.cast_sum, sum_mult_eq, Nat.abs_cast]
    rw [regulator_eq_det _ w' e, ← Matrix.det_reindex_self g]
    congr with i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.of_apply, dif_neg]
    rfl
  · simp_rw [Equiv.forall_congr_left f, ← f.symm.sum_comp, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.of_apply, f.symm_symm, f.apply_symm_apply,
      Finset.sum_dite_irrel, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    intro _ h
    rw [dif_neg h, sum_mult_mul_log]

end Units

end NumberField
