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

/-- Typeclass saying that a subgroup of `GL(n, R)` is contained in `SL(n, R)`. Necessary so that
the typeclass system can detect when the slash action is `ℂ`-linear. -/
class HasDetOne : Prop where
  det_eq {g} (hg : g ∈ Γ) : g.det = 1

instance (Γ : Subgroup (SL n R)) : HasDetOne (Γ.map toGL) where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp

instance {S : Type*} [CommRing S] [Algebra R S] (Γ : Subgroup (SL n R)) :
    HasDetOne (Γ.map <| mapGL S) where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp

instance {S : Type*} [CommRing S] [Algebra R S] :
    HasDetOne (mapGL (n := n) (R := R) S).range where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp

instance [HasDetOne Γ] : HasDetPlusMinusOne Γ := ⟨fun {g} hg ↦ by simp [HasDetOne.det_eq hg]⟩

instance (Γ' : Subgroup (GL n R)) [HasDetOne Γ] : HasDetOne (Γ ⊓ Γ') where
  det_eq hg := HasDetOne.det_eq hg.1

instance (Γ' : Subgroup (GL n R)) [HasDetOne Γ] : HasDetOne (Γ' ⊓ Γ) where
  det_eq hg := HasDetOne.det_eq hg.2

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
  refine ⟨fun {g} hg ↦ ?_⟩
  suffices |g.det.val| = 1 by rcases abs_cases g.det.val <;> aesop
  obtain ⟨n, hn, _, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    Subgroup.IsArithmetic.is_commensurable.2 hg
  suffices |(g.det ^ n).val| = 1 by simpa [← abs_pow, abs_pow_eq_one _ (Nat.ne_zero_of_lt hn)]
  obtain ⟨t, ht⟩ := hgn.1
  have := congr_arg Matrix.GeneralLinearGroup.det ht.symm
  rw [Matrix.SpecialLinearGroup.det_mapGL, map_pow] at this
  simp [this]

instance IsArithmetic.isFiniteRelIndexSL (𝒢 : Subgroup (GL (Fin 2) ℝ)) [IsArithmetic 𝒢] :
    𝒢.IsFiniteRelIndex 𝒮ℒ :=
  ⟨IsArithmetic.is_commensurable.1⟩

instance IsArithmetic.inter {Γ Γ'} [IsArithmetic Γ] [IsArithmetic Γ'] : IsArithmetic (Γ ⊓ Γ') := by
  constructor
  constructor
  · apply relIndex_inf_ne_zero <;> exact IsArithmetic.is_commensurable.1
  · apply relIndex_ne_zero_trans (K := Γ) IsArithmetic.is_commensurable.2
    rw [relIndex_eq_one.mpr inf_le_left]
    simp

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

section adjoinNeg

variable {R : Type*} [Ring R]

/-- Given a subgroup `𝒢` of `GL n R`, this is the subgroup generated by `𝒢` and `-1`. -/
def Subgroup.adjoinNegOne (𝒢 : Subgroup (GL n R)) : Subgroup (GL n R) where
  carrier := {g | g ∈ 𝒢 ∨ -g ∈ 𝒢}
  mul_mem' ha hb := by
    rcases ha with ha | ha <;>
      rcases hb with hb | hb <;>
      · have := mul_mem ha hb
        aesop
  one_mem' := by simp
  inv_mem' ha := by
    rcases ha with (ha | ha) <;>
    · have := inv_mem ha
      aesop

@[simp] lemma Subgroup.mem_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} {g : GL n R} :
    g ∈ 𝒢.adjoinNegOne ↔ g ∈ 𝒢 ∨ -g ∈ 𝒢 :=
  Iff.rfl

lemma Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R)) : 𝒢 ≤ 𝒢.adjoinNegOne :=
  fun _ hg ↦ .inl hg

lemma Subgroup.negOne_mem_adjoinNegOne (𝒢 : Subgroup (GL n R)) : -1 ∈ 𝒢.adjoinNegOne :=
  by simp

@[simp] lemma Subgroup.adjoinNegOne_eq_self_iff {𝒢 : Subgroup (GL n R)} :
    𝒢.adjoinNegOne = 𝒢 ↔ -1 ∈ 𝒢 :=
  ⟨fun h ↦ h ▸ negOne_mem_adjoinNegOne 𝒢, fun hG ↦ 𝒢.le_adjoinNegOne.antisymm'
    fun g hg ↦ hg.elim id (fun h ↦ by simpa using mul_mem hG h)⟩

lemma Subgroup.relindex_adjoinNegOne_eq_two {𝒢 : Subgroup (GL n R)} (h𝒢 : -1 ∉ 𝒢) :
    𝒢.relIndex 𝒢.adjoinNegOne = 2 := by
  refine relIndex_eq_two_iff_exists_notMem_and.mpr ⟨_, 𝒢.negOne_mem_adjoinNegOne, h𝒢, ?_⟩
  simp [mem_adjoinNegOne_iff, or_comm]

lemma Subgroup.relIndex_adjoinNegOne_ne_zero (𝒢 : Subgroup (GL n R)) :
    𝒢.relIndex 𝒢.adjoinNegOne ≠ 0 := by
  by_cases hG : -1 ∈ 𝒢
  · simp [adjoinNegOne_eq_self_iff.mpr hG]
  · simp [𝒢.relindex_adjoinNegOne_eq_two hG]

instance (𝒢 : Subgroup (GL n R)) : Subgroup.IsFiniteRelIndex 𝒢 𝒢.adjoinNegOne :=
  ⟨𝒢.relIndex_adjoinNegOne_ne_zero⟩

lemma Subgroup.commensurable_adjoinNegOne_self (𝒢 : Subgroup (GL n R)) :
    Commensurable 𝒢.adjoinNegOne 𝒢 :=
  ⟨by simp [Subgroup.relIndex_eq_one.mpr 𝒢.le_adjoinNegOne], 𝒢.relIndex_adjoinNegOne_ne_zero⟩

instance [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (𝒢 : Subgroup (GL n R)) [DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.adjoinNegOne := by
  rwa [𝒢.commensurable_adjoinNegOne_self.discreteTopology_iff]

section CommRing

variable {R : Type*} [CommRing R]

@[simp] lemma Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} :
    𝒢.adjoinNegOne.HasDetPlusMinusOne ↔ 𝒢.HasDetPlusMinusOne := by
  refine ⟨fun _ ↦ ⟨fun {g} hg ↦ HasDetPlusMinusOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ ↦ ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetPlusMinusOne.det_eq hg
  · by_cases hn : Even (Fintype.card n)
    · convert HasDetPlusMinusOne.det_eq hg using 1 <;>
        simp [Units.ext_iff, det_neg, hn]
    · convert (HasDetPlusMinusOne.det_eq hg).symm using 1 <;>
        simp [Units.ext_iff, det_neg, Nat.not_even_iff_odd.mp hn, neg_eq_iff_eq_neg]

lemma Subgroup.hasDetOne_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} (hn : Even (Fintype.card n)) :
    𝒢.adjoinNegOne.HasDetOne ↔ 𝒢.HasDetOne := by
  refine ⟨fun _ ↦ ⟨fun {g} hg ↦ HasDetOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ ↦ ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetOne.det_eq hg
  · simpa [Units.ext_iff, det_neg, hn] using HasDetOne.det_eq hg

instance {𝒢 : Subgroup (GL n R)} [𝒢.HasDetPlusMinusOne] :
    𝒢.adjoinNegOne.HasDetPlusMinusOne :=
  Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff.2 ‹_›

instance {𝒢 : Subgroup (GL n R)} [𝒢.HasDetOne] [Fact (Even (Fintype.card n))] :
    𝒢.adjoinNegOne.HasDetOne :=
  (Subgroup.hasDetOne_adjoinNegOne_iff Fact.out).2 ‹_›

end CommRing

instance Subgroup.instIsArithmeticAdjoinNegOne {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] :
    𝒢.adjoinNegOne.IsArithmetic :=
  ⟨(𝒢.commensurable_adjoinNegOne_self).trans IsArithmetic.is_commensurable⟩

end adjoinNeg
