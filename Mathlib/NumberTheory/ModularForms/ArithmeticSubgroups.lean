/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

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
  refine ⟨fun h {g} hg ↦ h.abs_det hg, fun h ↦ ⟨?_⟩⟩
  simpa [-GeneralLinearGroup.val_det_apply, abs_eq zero_le_one] using @h

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

open scoped Pointwise in
instance (Γ : Subgroup (GL n R)) [HasDetOne Γ] (g : ConjAct <| GL n R) :
    HasDetOne (g • Γ) where
  det_eq {h} hh := by
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hh
    simpa [ConjAct.smul_def] using HasDetOne.det_eq hh

open scoped Pointwise in
instance (Γ : Subgroup (GL n R)) [HasDetPlusMinusOne Γ] (g : ConjAct <| GL n R) :
    HasDetPlusMinusOne (g • Γ) where
  det_eq {h} hh := by
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hh
    simpa [ConjAct.smul_def] using HasDetPlusMinusOne.det_eq hh

end det_typeclasses

section detOnePart

variable {R : Type*} [CommRing R]

/-- The determinant-one part of a subgroup of `GL(2, ℝ)`. -/
noncomputable def detOnePart (G : Subgroup (GL n R)) : Subgroup (GL n R) :=
  G ⊓ (Matrix.SpecialLinearGroup.toGL : SL n R →* GL n R).range

@[simp] lemma mem_detOnePart {G : Subgroup (GL n R)} {g : GL n R} :
    g ∈ G.detOnePart ↔ g ∈ G ∧ g.det = 1 := by
  simp only [detOnePart, mem_inf, MonoidHom.mem_range, and_congr_right_iff]
  intro hg
  constructor
  · grind [coeToGL_det]
  · simpa [Units.ext_iff, GeneralLinearGroup.val_det_apply] using fun hdet ↦ ⟨⟨g, hdet⟩, rfl⟩

lemma detOnePart_le (G : Subgroup (GL n R)) : G.detOnePart ≤ G := by
  simp [detOnePart]

instance (G : Subgroup (GL n R)) : G.detOnePart.HasDetOne where
  det_eq {g} := by grind [detOnePart, mem_inf, MonoidHom.mem_range, coeToGL_det]

end detOnePart

section SL2Z_in_GL2R

/-- The image of the modular group `SL(2, ℤ)`, as a subgroup of `GL(2, ℝ)`. -/
scoped[MatrixGroups] notation "𝒮ℒ" => MonoidHom.range (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)

/-- Coercion from subgroups of `SL(2, ℤ)` to subgroups of `GL(2, ℝ)` by mapping along the obvious
inclusion homomorphism. -/
instance : Coe (Subgroup SL(2, ℤ)) (Subgroup (GL (Fin 2) ℝ)) where
  coe := map (mapGL ℝ)

/-- A subgroup of `GL(2, ℝ)` is arithmetic if it is commensurable with the image of `SL(2, ℤ)`. -/
@[mk_iff]
class IsArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) : Prop where
  is_commensurable : Commensurable 𝒢 𝒮ℒ

/-- The image of `SL(2, ℤ)` in `GL(2, ℝ)` is arithmetic. -/
instance : IsArithmetic 𝒮ℒ where is_commensurable := .refl 𝒮ℒ

lemma isArithmetic_iff_finiteIndex {Γ : Subgroup SL(2, ℤ)} : IsArithmetic Γ ↔ Γ.FiniteIndex := by
  rw [isArithmetic_iff, MonoidHom.range_eq_map, Commensurable.map_injective_iff mapGL_injective,
    Commensurable.top_right_iff]

/-- Images in `GL(2, ℝ)` of finite-index subgroups of `SL(2, ℤ)` are arithmetic. -/
instance (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : IsArithmetic Γ :=
  isArithmetic_iff_finiteIndex.mpr ‹_›

/-- If `Γ` is arithmetic, its preimage in `SL(2, ℤ)` has finite index. -/
instance IsArithmetic.finiteIndex_comap (𝒢 : Subgroup (GL (Fin 2) ℝ)) [IsArithmetic 𝒢] :
    (𝒢.comap (mapGL (R := ℤ) ℝ)).FiniteIndex :=
  ⟨𝒢.index_comap (mapGL (R := ℤ) ℝ) ▸ is_commensurable.1.relIndex_ne_zero⟩

instance {Γ : Subgroup (GL (Fin 2) ℝ)} [h : Γ.IsArithmetic] : HasDetPlusMinusOne Γ := by
  rw [hasDetPlusMinusOne_iff_abs_det]
  intro g hg
  obtain ⟨n, hn, _, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    IsArithmetic.is_commensurable.2.relIndex_ne_zero hg
  suffices |(g.det ^ n).val| = 1 by simpa [← abs_pow, abs_pow_eq_one _ (Nat.ne_zero_of_lt hn)]
  obtain ⟨t, ht⟩ := hgn.1
  have := congr_arg Matrix.GeneralLinearGroup.det ht.symm
  rw [Matrix.SpecialLinearGroup.det_mapGL, map_pow] at this
  simp [this]

instance IsArithmetic.isFiniteRelIndex (G H : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [H.IsArithmetic] : G.IsFiniteRelIndex H :=
  (is_commensurable.trans is_commensurable.symm).1

instance IsArithmetic.inter {Γ Γ'} [IsArithmetic Γ] [IsArithmetic Γ'] : IsArithmetic (Γ ⊓ Γ') :=
  ⟨is_commensurable.inf_left is_commensurable⟩

/-- The determinant-one part of an arithmetic subgroup is arithmetic. -/
instance (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] : G.detOnePart.IsArithmetic := by
  let L := G ⊓ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))
  have hLK : L ≤ G.detOnePart := by
    rintro g ⟨hg, x, _, hx⟩
    exact ⟨hg, ⟨x, rfl⟩⟩
  have hLKfin : L.IsFiniteRelIndex G.detOnePart := isFiniteRelIndex_of_le_right _ G.detOnePart_le
  have hKLfin : G.detOnePart.IsFiniteRelIndex L := isFiniteRelIndex_of_le_right _ hLK
  exact ⟨.trans ⟨hKLfin, hLKfin⟩ IsArithmetic.is_commensurable⟩

open scoped Pointwise in
/-- Conjugation by an element of an arithmetic group preserves arithmeticity. -/
lemma isArithmetic_conj_of_mem {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] {r : GL (Fin 2) ℝ} (hr : r ∈ H) :
    (ConjAct.toConjAct r • K).IsArithmetic := by
  have hKH : K.Commensurable H := IsArithmetic.is_commensurable.trans
    IsArithmetic.is_commensurable.symm
  have hc : (ConjAct.toConjAct r • K).Commensurable H := by
    simpa only [conjAct_pointwise_smul_eq_self (H.le_normalizer hr)] using
      hKH.smul (ConjAct.toConjAct r)
  exact ⟨hc.trans IsArithmetic.is_commensurable⟩

end SL2Z_in_GL2R

end Subgroup

namespace Matrix.SpecialLinearGroup

/-- The image of `SL(n, ℤ)` in `GL(n, ℝ)` is discrete. -/
instance discreteSpecialLinearGroupIntRange : DiscreteTopology (mapGL (n := n) (R := ℤ) ℝ).range :=
  (isEmbedding_mapGL Real.isClosedEmbedding_intCast.1).toHomeomorph.discreteTopology

/-- The image of `SL(n, ℤ)` in `SL(n, ℝ)` is discrete. -/
instance discreteSpecialLinearGroupIntRangeSL :
    DiscreteTopology (SpecialLinearGroup.map (Int.castRingHom ℝ) (n := n)).range := by
  refine (Topology.IsEmbedding.toHomeomorph ?_).discreteTopology
  exact Real.isClosedEmbedding_intCast.specialLinearGroup_map.1

lemma isClosedEmbedding_mapGLInt : Topology.IsClosedEmbedding (mapGL ℝ : SL n ℤ → GL n ℝ) :=
  isClosedEmbedding_mapGL Real.isClosedEmbedding_intCast

end Matrix.SpecialLinearGroup

/-- Arithmetic subgroups of `GL(2, ℝ)` are discrete. -/
instance Subgroup.IsArithmetic.discreteTopology {𝒢 : Subgroup (GL (Fin 2) ℝ)} [IsArithmetic 𝒢] :
    DiscreteTopology 𝒢 := by
  rw [is_commensurable.discreteTopology_iff]
  infer_instance

section adjoinNeg

namespace Subgroup

variable {G : Type*} [Group G] [HasDistribNeg G]

/-- Given a subgroup `𝒢` of a group with compatible negation, this is the subgroup generated
by `𝒢` and `-1`. -/
def adjoinNegOne (𝒢 : Subgroup G) : Subgroup G where
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

@[simp] lemma mem_adjoinNegOne_iff {𝒢 : Subgroup G} {g : G} :
    g ∈ 𝒢.adjoinNegOne ↔ g ∈ 𝒢 ∨ -g ∈ 𝒢 :=
  Iff.rfl

lemma le_adjoinNegOne (𝒢 : Subgroup G) : 𝒢 ≤ 𝒢.adjoinNegOne :=
  fun _ hg ↦ .inl hg

lemma negOne_mem_adjoinNegOne (𝒢 : Subgroup G) : -1 ∈ 𝒢.adjoinNegOne := by simp

@[simp] lemma adjoinNegOne_eq_self_iff {𝒢 : Subgroup G} :
    𝒢.adjoinNegOne = 𝒢 ↔ -1 ∈ 𝒢 :=
  ⟨fun h ↦ h ▸ negOne_mem_adjoinNegOne 𝒢, fun hG ↦ 𝒢.le_adjoinNegOne.antisymm'
    fun g hg ↦ hg.elim id (fun h ↦ by simpa using mul_mem hG h)⟩

lemma relindex_adjoinNegOne_eq_two {𝒢 : Subgroup G} (h𝒢 : -1 ∉ 𝒢) :
    𝒢.relIndex 𝒢.adjoinNegOne = 2 := by
  refine relIndex_eq_two_iff_exists_notMem_and.mpr ⟨_, 𝒢.negOne_mem_adjoinNegOne, h𝒢, ?_⟩
  simp [mem_adjoinNegOne_iff, or_comm]

lemma relIndex_adjoinNegOne_ne_zero (𝒢 : Subgroup G) :
    𝒢.relIndex 𝒢.adjoinNegOne ≠ 0 := by
  by_cases hG : -1 ∈ 𝒢
  · simp [adjoinNegOne_eq_self_iff.mpr hG]
  · simp [𝒢.relindex_adjoinNegOne_eq_two hG]

instance (𝒢 : Subgroup G) : IsFiniteRelIndex 𝒢 𝒢.adjoinNegOne :=
  ⟨𝒢.relIndex_adjoinNegOne_ne_zero⟩

lemma commensurable_adjoinNegOne_self (𝒢 : Subgroup G) :
    Commensurable 𝒢.adjoinNegOne 𝒢 :=
  ⟨⟨by simp [relIndex_eq_one.mpr 𝒢.le_adjoinNegOne]⟩, ⟨𝒢.relIndex_adjoinNegOne_ne_zero⟩⟩

/-- Adjoining `-1` commutes with taking images under a homomorphism that preserves negation. -/
lemma map_adjoinNegOne {H : Type*} [Group H] [HasDistribNeg H]
    (𝒢 : Subgroup G) (f : G →* H) (hf : ∀ g, f (-g) = -f g) :
    𝒢.adjoinNegOne.map f = (𝒢.map f).adjoinNegOne := by
  ext
  grind [mem_map, mem_adjoinNegOne_iff, neg_neg]

/-- Adjoining `-1` preserves inclusion. -/
lemma adjoinNegOne_mono {𝒢 ℋ : Subgroup G} (h : 𝒢 ≤ ℋ) : 𝒢.adjoinNegOne ≤ ℋ.adjoinNegOne := by
  intro g
  aesop

open scoped Pointwise in
/-- Adjoining `-1` commutes with conjugation. -/
lemma adjoinNegOne_conj (𝒢 : Subgroup G) (g : ConjAct G) :
    (g • 𝒢).adjoinNegOne = g • 𝒢.adjoinNegOne := by
  ext
  simp [mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]

end Subgroup

variable {R : Type*} [Ring R]

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
    · convert! HasDetPlusMinusOne.det_eq hg using 1 <;>
        simp [Units.ext_iff, det_neg, hn]
    · convert! (HasDetPlusMinusOne.det_eq hg).symm using 1 <;>
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

lemma adjoinNegOne_detOnePart {G : Subgroup (GL n R)} (hn : Even (Fintype.card n)) :
    G.detOnePart.adjoinNegOne = G.adjoinNegOne.detOnePart := by
  ext
  simp [Units.ext_iff, det_neg, hn.neg_one_pow]
  grind

end CommRing

instance Subgroup.instIsArithmeticAdjoinNegOne {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] :
    𝒢.adjoinNegOne.IsArithmetic :=
  ⟨(𝒢.commensurable_adjoinNegOne_self).trans IsArithmetic.is_commensurable⟩

end adjoinNeg
