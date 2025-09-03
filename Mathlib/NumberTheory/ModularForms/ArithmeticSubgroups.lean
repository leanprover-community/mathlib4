/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Commensurable
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Arithmetic subgroups of `GL(2, ℝ)`

We define a subgroup of `GL (Fin 2) ℝ` to be *arithmetic* if it is commensurable with the image
of `SL(2, ℤ)`.
-/

open Matrix.SpecialLinearGroup

open scoped MatrixGroups

section ArithmeticSubgroups

/-- A subgroup of `GL(2, ℝ)` is arithmetic if it is commensurable with the image of `SL(2, ℤ)`. -/
class IsArith (Γ : Subgroup (GL (Fin 2) ℝ)) : Prop where
  is_comm : Commensurable Γ (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range

/-- The image of `SL(2, ℤ)` in `GL(2, ℝ)` is arithmetic. -/
instance : IsArith (mapGL (R := ℤ) ℝ).range := ⟨by rfl⟩

/-- Images in `GL(2, ℝ)` of finite-index subgroups of `SL(2, ℤ)` are arithmetic. -/
instance (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : IsArith (Γ.map <| mapGL ℝ) where
  is_comm := by simpa [Commensurable, MonoidHom.range_eq_map, ← Subgroup.relindex_comap,
        Subgroup.comap_map_eq_self_of_injective mapGL_injective]
      using Subgroup.FiniteIndex.index_ne_zero

/-- If `Γ` is arithmetic, its preimage in `SL(2, ℤ)` has finite index. -/
instance IsArith.finiteIndex_comap (Γ : Subgroup (GL (Fin 2) ℝ)) [IsArith Γ] :
    (Γ.comap (mapGL (R := ℤ) ℝ)).FiniteIndex :=
  ⟨Subgroup.index_comap Γ (mapGL (R := ℤ) ℝ) ▸ (IsArith.is_comm).1⟩

end ArithmeticSubgroups
