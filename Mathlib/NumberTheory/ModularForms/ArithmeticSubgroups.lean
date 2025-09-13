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

namespace Subgroup

/-- The image of the modular group `SL(2, ℤ)`, as a subgroup of `GL(2, ℝ)`. -/
scoped[MatrixGroups] notation "𝒮ℒ" => MonoidHom.range (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)

/-- Coercion from subgroups of `SL(2, ℤ)` to subgroups of `GL(2, ℝ)` by mapping along the obvious
inclusion homomorphism. -/
instance : Coe (Subgroup SL(2, ℤ)) (Subgroup (GL (Fin 2) ℝ)) where
  coe := map (mapGL ℝ)

/-- A subgroup of `GL(2, ℝ)` is arithmetic if it is commensurable with the image of `SL(2, ℤ)`. -/
class IsArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) : Prop where
  is_commensurable : Commensurable 𝒢 𝒮ℒ

/-- The image of `SL(2, ℤ)` in `GL(2, ℝ)` is arithmetic. -/
instance : IsArithmetic 𝒮ℒ where is_commensurable := .refl 𝒮ℒ

lemma isArithmetic_iff_finiteIndex {Γ : Subgroup SL(2, ℤ)} : IsArithmetic Γ ↔ Γ.FiniteIndex := by
  constructor <;>
  · refine fun ⟨h⟩ ↦ ⟨?_⟩
    simpa [Commensurable, MonoidHom.range_eq_map, ← relIndex_comap,
      comap_map_eq_self_of_injective mapGL_injective] using h

/-- Images in `GL(2, ℝ)` of finite-index subgroups of `SL(2, ℤ)` are arithmetic. -/
instance (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : IsArithmetic Γ :=
  isArithmetic_iff_finiteIndex.mpr ‹_›

/-- If `Γ` is arithmetic, its preimage in `SL(2, ℤ)` has finite index. -/
instance IsArithmetic.finiteIndex_comap (𝒢 : Subgroup (GL (Fin 2) ℝ)) [IsArithmetic 𝒢] :
    (𝒢.comap (mapGL (R := ℤ) ℝ)).FiniteIndex :=
  ⟨𝒢.index_comap (mapGL (R := ℤ) ℝ) ▸ IsArithmetic.is_commensurable.1⟩

end Subgroup
