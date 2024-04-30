/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Regulator of a number field
We prove results about the regulator of a number field `K`.

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

def regulatorOfFamily (w' : InfinitePlace K) (u : Fin (rank K) → (𝓞 K)ˣ)
    (e : {w : InfinitePlace K // w ≠ w'} ≃ Fin (rank K)) :=
  (Matrix.of (fun w₁ : {w // w ≠ w'} ↦ fun w₂ ↦ mult w₁.val * Real.log (w₁.val (u (e w₂))))).det

theorem regulator_eq_regulatorOfFamily (w' : InfinitePlace K) {u : Fin (rank K) → (𝓞 K)ˣ}
    (h : ∀ x : (𝓞 K)ˣ, ∃ ζe : torsion K × (Fin (rank K) → ℤ), x = ζe.1 * ∏ i, (u i ^ (ζe.2 i)))
    (e : {w : InfinitePlace K // w ≠ w'} ≃ Fin (rank K)) :
    regulator K = regulatorOfFamily K w' u e := by
  sorry
