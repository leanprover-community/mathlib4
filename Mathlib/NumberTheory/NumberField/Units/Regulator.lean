/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

import Mathlib.Sandbox

/-!
# Regulator of a number field

We define and prove basic results about the regulator of a number field `K`.

## Main definition

* `NumberField.Units.regulator`: the regulator of the number field `K`.

## Tags
number field, units, regulator
 -/

open scoped NumberField

noncomputable section

namespace NumberField.Units

variable (K : Type*) [Field K]

open MeasureTheory Classical BigOperators NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

/-- The regulator of a number fied `K`. -/
def regulator : ℝ := Zlattice.covolume (unitLattice K)

theorem regulator_ne_zero : regulator K ≠ 0 := Zlattice.covolume_ne_zero (unitLattice K) volume

theorem regulator_pos : 0 < regulator K := Zlattice.covolume_pos (unitLattice K) volume

theorem regulator_eq_det' (e : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K)) :
    regulator K = |(Matrix.of fun i ↦ (logEmbedding K) (fundSystem K (e i))).det| := by
  simp_rw [regulator, Zlattice.covolume_eq_det _
    (((basisModTorsion K).map (logEmbeddingEquiv K)).reindex e.symm), Basis.coe_reindex,
    Function.comp, Basis.map_apply, ← fundSystem_mk, logEmbeddingEquiv_apply, Equiv.symm_symm]

example (w' : InfinitePlace K) (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    regulator K =
      |(Matrix.of fun i w : {w // w ≠ w'} ↦ (mult w.val : ℝ) *
        Real.log (w.val (fundSystem K (e i) : K))).det| := by
  -- We construct an equiv `Fin (rank K + 1) ≃ InfinitePlace K` that extends `e.symm` by sending
  -- `rank K + 1` to `w'`
  let f : Fin (rank K + 1) ≃ InfinitePlace K :=
    finSuccEquivLast.trans ((Equiv.optionSubtype _).symm e.symm).val
  let g : { w // w ≠ w₀ } ≃ Fin (rank K) :=
    (Equiv.subtypeEquiv f.symm (fun _ ↦ by simp [f])).trans
      (finSuccAboveEquiv (f.symm w₀)).toEquiv.symm
  rw [← Matrix.det_reindex_self e, eq_comm, regulator_eq_det' K g, ← Matrix.det_reindex_self g]
  have := congr_arg abs <| Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'
    (Matrix.of fun i w ↦ (mult (f w) : ℝ) * Real.log ((f w) (fundSystem K i)))
    ?_ (Fin.last _) (f.symm w₀)
  · rw [Units.smul_def, abs_zsmul, Int.negOnePow_abs, one_smul] at this
    convert this
    · ext
      simp_rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last,
        Equiv.apply_symm_apply, id_eq, f, Equiv.trans_apply, finSuccEquivLast_castSucc]
      rfl
    · ext
      simp_rw [Matrix.reindex_apply, Matrix.submatrix_apply, logEmbedding, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, Matrix.of_apply, Equiv.apply_symm_apply]
      rfl
  · intro _
    simp only [Matrix.of_apply]
    rw [Equiv.sum_comp f (fun w ↦ (mult w : ℝ) * Real.log (w (fundSystem K _)))]
    simp_rw [← Real.log_pow]
    rw [← Real.log_prod, prod_eq_abs_norm]
    sorry
    sorry
