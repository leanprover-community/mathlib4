/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Arithmetic subgroups of `GL(2, ℝ)`

We define a subgroup of `GL (Fin 2) ℝ` to be *arithmetic* if it is commensurable with the image
of `SL(2, ℤ)`.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

local notation "SL" => SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Subgroup

section det_typeclasses

variable {R : Type*} [CommRing R] (Γ : Subgroup (GL n R))

/-- Typeclass saying that a subgroup of `GL(2, ℝ)` has determinant contained in `{±1}`. Necessary
so that the typeclass system can detect when the slash action is multiplicative. -/
class HasDetPlusMinusOne : Prop where
  det_eq {g} (hg : g ∈ Γ) : g.det = 1 ∨ g.det = -1

variable {Γ} in
lemma HasDetPlusMinusOne.abs_det [LinearOrder R] [IsOrderedRing R] [HasDetPlusMinusOne Γ]
    {g} (hg : g ∈ Γ) : |g.det.val| = 1 := by
  rcases HasDetPlusMinusOne.det_eq hg with h | h <;> simp [h]

lemma hasDetPlusMinusOne_iff_abs_det [LinearOrder R] [IsOrderedRing R] :
    HasDetPlusMinusOne Γ ↔ ∀ {g}, g ∈ Γ → |g.det.val| = 1 := by
  refine ⟨fun h {g} hg => h.abs_det hg, fun h => ⟨?_⟩⟩
  simpa [-GeneralLinearGroup.val_det_apply, abs_eq zero_le_one] using @h

/-- Typeclass saying that a subgroup of `GL(n, R)` is contained in `SL(n, R)`. Necessary so that
the typeclass system can detect when the slash action is `ℂ`-linear. -/
class HasDetOne : Prop where
  det_eq {g} (hg : g ∈ Γ) : g.det = 1

instance (Γ : Subgroup (SL n R)) : HasDetOne (Γ.map toGL) where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp

instance {S : Type*} [CommRing S] [Algebra S R] (Γ : Subgroup (SL n S)) :
    HasDetOne (Γ.map <| mapGL R) where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp

instance [HasDetOne Γ] : HasDetPlusMinusOne Γ := ⟨fun {g} hg ↦ by simp [HasDetOne.det_eq hg]⟩

end det_typeclasses

section SL2Z_in_GL2R

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

instance {Γ : Subgroup (GL (Fin 2) ℝ)} [h : Γ.IsArithmetic] : HasDetPlusMinusOne Γ := by
  rw [hasDetPlusMinusOne_iff_abs_det]
  intro g hg
  obtain ⟨n, hn, _, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    Subgroup.IsArithmetic.is_commensurable.2 hg
  suffices |(g.det ^ n).val| = 1 by simpa [← abs_pow, abs_pow_eq_one _ (Nat.ne_zero_of_lt hn)]
  obtain ⟨t, ht⟩ := hgn.1
  have := congr_arg Matrix.GeneralLinearGroup.det ht.symm
  rw [Matrix.SpecialLinearGroup.det_mapGL, map_pow] at this
  simp [this]

end SL2Z_in_GL2R

end Subgroup

namespace Matrix.SpecialLinearGroup

instance discreteSpecialLinearGroupIntRange : DiscreteTopology (mapGL (n := n) (R := ℤ) ℝ).range :=
  (isEmbedding_mapGL (Isometry.isEmbedding fun _ _ ↦ rfl)).toHomeomorph.discreteTopology

lemma isClosedEmbedding_mapGLInt : Topology.IsClosedEmbedding (mapGL ℝ : SL n ℤ → GL n ℝ) :=
  ⟨isEmbedding_mapGL (Isometry.isEmbedding fun _ _ ↦ rfl), (mapGL ℝ).range.isClosed_of_discrete⟩

end Matrix.SpecialLinearGroup

/-- Arithmetic subgroups of `GL(2, ℝ)` are discrete. -/
instance Subgroup.IsArithmetic.discreteTopology {𝒢 : Subgroup (GL (Fin 2) ℝ)} [IsArithmetic 𝒢] :
    DiscreteTopology 𝒢 := by
  rw [is_commensurable.discreteTopology_iff]
  infer_instance
