/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Generators

/-!
Documentation
-/

open Function

namespace exteriorPower

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (k : ℕ)

variable {R M}
variable (B : LinearMap.BilinForm R M)

theorem auxCol {ι : Type*} [DecidableEq ι] (v w : ι → M) (z : M) (l : ι) :
    (Matrix.of fun i j ↦ B (v i) (Function.update w l z j)) =
    (Matrix.of fun i j ↦ B (v i) (w j)).updateColumn l (fun i ↦ B (v i) z) := by
  ext i j
  simp only [update_apply, Matrix.of_apply, Matrix.updateColumn_apply]
  aesop

theorem auxRow {ι : Type*} [DecidableEq ι] (v w : ι → M) (z : M) (l : ι) :
    (Matrix.of fun i j ↦ B (Function.update v l z i) (w j)) =
    (Matrix.of fun i j ↦ B (v i) (w j)).updateRow l (fun j ↦ B z (w j)) := by
  ext i j
  simp only [update_apply, Matrix.of_apply, Matrix.updateRow_apply]
  aesop

private def BilinFormAux :
    M [⋀^Fin k]→ₗ[R] M [⋀^Fin k]→ₗ[R] R where
  toFun v :=
    { toFun := fun w ↦ (Matrix.of fun i j ↦ B (v i) (w j)).det
      map_add' := fun {_i} w l x y ↦ by
        simp only [auxCol, map_add]
        convert Matrix.det_updateColumn_add _ l _ _
      map_smul' := fun {_i} w l t x ↦ by
        simp only [auxCol, map_smul]
        convert Matrix.det_updateColumn_smul _ l t _
      map_eq_zero_of_eq' := fun w l₁ l₂ hl hl' ↦ Matrix.det_zero_of_column_eq hl' <| by simp [hl] }
  map_add' {_i} v l x y := by
    ext w
    simp only [AlternatingMap.coe_mk, MultilinearMap.coe_mk, AlternatingMap.add_apply,
      auxRow, map_add, LinearMap.add_apply]
    convert Matrix.det_updateRow_add _ l _ _
  map_smul' {_i} v l t x := by
    ext w
    simp only [AlternatingMap.coe_mk, MultilinearMap.coe_mk, AlternatingMap.smul_apply, smul_eq_mul,
      auxRow, map_smul, LinearMap.smul_apply, smul_eq_mul]
    convert Matrix.det_updateRow_smul _ l t _
  map_eq_zero_of_eq' v l₁ l₂ hl hl' :=
    AlternatingMap.ext fun w ↦ Matrix.det_zero_of_row_eq hl' <| funext fun i ↦ by simp [hl]

protected def BilinForm : LinearMap.BilinForm R (⋀[R]^k M) :=
  (liftAlternating k) ∘ₗ liftAlternating k (BilinFormAux k B)

local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm k B v w

theorem bilin_apply_ιMulti (v w : Fin k → M) :
  ⟪(ιMulti R k v), (ιMulti R k w)⟫ = (Matrix.of fun i j ↦ B (v i) (w j)).det := by
  unfold exteriorPower.BilinForm
  simp only [LinearMap.coe_comp, comp_apply, liftAlternating_apply_ιMulti]
  rfl

theorem bilin_apply_ιMulti_family {I : Type*} [LinearOrder I] (b : I → M)
  (s t : {s : Finset I // Finset.card s = k}) :
  ⟪ιMulti_family R k b s, ιMulti_family R k b t⟫ = (Matrix.of fun i j ↦
  B (b (Finset.orderIsoOfFin s.1 s.2 i)) (b (Finset.orderIsoOfFin t.1 t.2 j))).det := by
  unfold exteriorPower.BilinForm
  unfold ιMulti_family
  simp only [LinearMap.coe_comp, comp_apply, liftAlternating_apply_ιMulti]
  rfl

theorem bilin_symm_ιMulti (h : B.IsSymm) : ∀ v w : Fin k → M, ⟪(ιMulti R k v), (ιMulti R k w)⟫ =
  ⟪(ιMulti R k w), (ιMulti R k v)⟫ := by
  intro v w
  simp only [bilin_apply_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [← h (v j) (w i)]
  simp only [RingHom.id_apply]

section overField

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (k : ℕ)
variable (B : LinearMap.BilinForm K M) (hN : B.Nondegenerate)
variable {I : Type*} [LinearOrder I] [Finite I] (b : Basis I K M)
variable {k : ℕ}

local notation "⟪" v ", " w "⟫" => exteriorPower.BilinForm k B v w
noncomputable abbrev basis := Basis.exteriorPower K k b


end overField

end exteriorPower
