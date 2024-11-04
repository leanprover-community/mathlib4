/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.ExteriorAlgebra.Temp

/-!
Documentation
-/

open ExteriorAlgebra BigOperators

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : LinearMap.BilinForm R M)
variable {k : ℕ}

section inducedForm

theorem aux (v w : Fin k → M) (x y : M) (j': Fin k) :
  (Matrix.of fun i j ↦ (B (v i)) (Function.update w j' (x + y) j)) =
  (Matrix.of fun i j ↦ (B (v i)) (w j)).updateColumn j' (fun i ↦ B (v i) (x + y)) := by
  ext i j
  rw [Matrix.of_apply, Matrix.updateColumn_apply, Function.update_apply, apply_ite (B (v i))]
  rfl

private def BilinFormAux :
    M [⋀^Fin k]→ₗ[R] M [⋀^Fin k]→ₗ[R] R where
  toFun v :=
    { toFun := fun w ↦ Matrix.det <| Matrix.of (fun i j ↦ B (v i) (w j))
      map_add' := by
        intro _ w j' x y
        dsimp
        convert_to ((Matrix.of fun i j => (B (v i)) (w j)).updateColumn j'
          fun i => (B (v i)) (x + y)).det = _
        · congr 1
          convert aux B v w x y j'
        --rw [aux B v w x y j']
        --rw [Matrix.det_updateColumn_add]
        sorry
      map_smul' := sorry
      map_eq_zero_of_eq' := sorry }
  map_add' := sorry
  map_smul' := sorry
  map_eq_zero_of_eq' := sorry

protected def BilinForm : LinearMap.BilinForm R (⋀[R]^k M) :=
  (liftAlternating R M R k) ∘ₗ
  (liftAlternating R M (M [⋀^Fin k]→ₗ[R] R) k (BilinFormAux B))

end inducedForm

end exteriorPower
