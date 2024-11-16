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

section matrix

variable {m n α : Type*}

theorem Matrix.of_eq (f g : m → n → α) : f = g →
  Matrix.of (fun i j ↦ f i j) = Matrix.of (fun i j ↦ g i j) := by
  intro h
  rw [h]

theorem Matrix.of_updateRow [DecidableEq m] (f : m → n → α) (x : α) (i' : m) :
  Matrix.of (fun i j ↦ (Function.update f i' (fun _ ↦ x)) i j) =
  (Matrix.of fun i j ↦ f i j).updateRow i' (fun _ ↦ x) := by
  ext i j
  simp only [of_apply, updateRow_apply]
  rw [Function.update_apply, ite_apply]

theorem Matrix.of_updateColumn [DecidableEq n] (f : m → n → α) (x : α) (j' : n) :
  Matrix.of (fun i j ↦ (Function.update (f i) j' x) j) =
  (Matrix.of fun i j ↦ f i j).updateColumn j' (fun _ ↦ x) := by
  ext i j
  simp only [of_apply, updateColumn_apply]
  exact Function.update_apply (f i) j' x j

variable {m' n' : Type*}

theorem Matrix.of_update_right [DecidableEq n'] (f : m → n → α) (v : m' → m) (w : n' → n) (j' : n')
  (x : n) :
  Matrix.of (fun i j ↦ f (v i) (Function.update w j' x <| j)) =
  (Matrix.of (fun i j ↦ f (v i) (w j))).updateColumn j' (fun i ↦ f (v i) x) := by
  ext i j
  simp only [of_apply, updateColumn_apply, Function.update_apply]
  rw [apply_ite (f (v i))]

theorem Matrix.det_of_updateColumn_add [CommRing α] [DecidableEq n'] [Fintype n']
  (f : n → n → α) (v w : n' → n)
  (j' : n') (x y : n) :
  ((Matrix.of (fun i j ↦ f (v i) (w j))).updateColumn j' (fun i ↦ f (v i) x + f (v i) y)).det =
  ((Matrix.of (fun i j ↦ f (v i) (w j))).updateColumn j' (fun i ↦ f (v i) x)).det +
  ((Matrix.of (fun i j ↦ f (v i) (w j))).updateColumn j' (fun i ↦ f (v i) y)).det := by
  rw [← Matrix.det_updateColumn_add]
  rfl



end matrix

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : LinearMap.BilinForm R M)
variable {k : ℕ}

section inducedForm

theorem Matrix.bilin_det_of_updateColumn_add (v w : Fin k → M)
  (j' : Fin k) (x y : M) :
  ((Matrix.of (fun i j ↦ B (v i) (w j))).updateColumn j' (fun i ↦ B (v i) x + B (v i) y)).det =
  ((Matrix.of (fun i j ↦ B (v i) (w j))).updateColumn j' (fun i ↦ B (v i) x)).det +
  ((Matrix.of (fun i j ↦ B (v i) (w j))).updateColumn j' (fun i ↦ B (v i) y)).det := by
  rw [← Matrix.det_updateColumn_add]
  rfl

#check Matrix.bilin_det_of_updateColumn_add B ?v ?w ?j' ?x ?y

#check Matrix.det_updateColumn_add

private def BilinFormAux :
    M [⋀^Fin k]→ₗ[R] M [⋀^Fin k]→ₗ[R] R where
  toFun v :=
    { toFun := fun w ↦ Matrix.det <| Matrix.of (fun i j ↦ B (v i) (w j))
      map_add' := by
        intro _ w j' x y
        dsimp
        simp only [Matrix.of_update_right]
        simp only [B.add_right]
        --rw [← Matrix.bilin_det_of_updateColumn_add B v w j' x y]
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
