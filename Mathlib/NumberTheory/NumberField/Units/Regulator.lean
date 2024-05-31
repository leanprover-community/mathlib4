/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

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

variable [NumberField K]

/-- The regulator of a number fied `K`. -/
def regulator : ℝ := Zlattice.covolume (unitLattice K)

theorem regulator_ne_zero : regulator K ≠ 0 := Zlattice.covolume_ne_zero (unitLattice K) volume

theorem regulator_pos : 0 < regulator K := Zlattice.covolume_pos (unitLattice K) volume

theorem regulator_eq_det'
    (e : {w : InfinitePlace K // w ≠ dirichletUnitTheorem.w₀} ≃ Fin (rank K)) :
    regulator K = |(Matrix.of fun x ↦ (logEmbedding K) (fundSystem K (e x))).det| := by
  simp_rw [regulator, Zlattice.covolume_eq_det _
    (((basisModTorsion K).map (logEmbeddingEquiv K)).reindex e.symm), Basis.coe_reindex,
    Function.comp, Basis.map_apply, ← fundSystem_mk, logEmbeddingEquiv_apply, Equiv.symm_symm]

example {e : {w : InfinitePlace K // w ≠ dirichletUnitTheorem.w₀} ≃ Fin (rank K)} :
    regulator K =
      |(Matrix.of fun i w : {w // w ≠ dirichletUnitTheorem.w₀} ↦
        (mult w.val : ℝ) * Real.log (w.val (fundSystem K (e i) : K))).det| := by
  rw [regulator_eq_det' K e]
  simp_rw [logEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rfl
