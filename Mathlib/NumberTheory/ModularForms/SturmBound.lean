/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.OrderChangeLevel
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Sturm bounds and finite-dimensionality

The Sturm bound `k * G.ratProjIndex / 12` bounds the total cusp order of a nonzero
modular form for an arithmetic determinant-one group. The proof uses the norm to level
one and restriction to a common arithmetic subgroup; the cusp counting is isolated in
`OrderChangeLevel.lean`.

The resulting bound on Fourier coefficients proves finite-dimensionality over `ℂ` for
determinant-one groups, and over `ℝ` for all arithmetic groups.
-/

@[expose] public section

open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped Pointwise
open OnePoint

open scoped MatrixGroups

open scoped Manifold ModularForm

namespace Subgroup

/-- The rational projective index of `G`, defined as `[SL(2, ℤ) : G''] / [G' : G'']`, where
`G' = G.adjoinNegOne` and `G'' = G' ⊓ SL(2, ℤ)`.

The intersections are implicit in `Subgroup.relIndex`. This ratio is zero if either relative
index is infinite, following the conventions for `Subgroup.relIndex` and division in `ℚ`. -/
noncomputable def ratProjIndex (G : Subgroup (GL (Fin 2) ℝ)) : ℚ :=
  (G.adjoinNegOne.relIndex 𝒮ℒ : ℚ) / relIndex 𝒮ℒ G.adjoinNegOne

/-- For a subgroup of `SL(2, ℤ)`, the rational projective index is the natural-number index
of the subgroup obtained by adjoining `-1`, viewed as a rational number. -/
lemma ratProjIndex_coe (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).ratProjIndex = (Γ.adjoinNegOne.index : ℚ) := by
  have hneg (γ : SL(2, ℤ)) : mapGL ℝ (-γ) = -mapGL ℝ γ := by
    ext i j
    simp [mapGL_coe_matrix]
  rw [ratProjIndex, ← Γ.map_adjoinNegOne (mapGL ℝ) hneg,
    relIndex_eq_one.mpr (Γ.adjoinNegOne.map_le_range _), Nat.cast_one, div_one,
    ← index_comap, comap_map_eq_self_of_injective mapGL_injective]

/-- The rational projective index scales by the index when both groups contain `-1`. -/
private lemma ratProjIndex_eq_relIndex_mul {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hGH : G ≤ H) (hG : -1 ∈ G) (hH : -1 ∈ H) :
    G.ratProjIndex = G.relIndex H * H.ratProjIndex := by
  have h₁ : G.relIndex (H ⊓ 𝒮ℒ) * H.relIndex 𝒮ℒ = (G ⊓ H).relIndex 𝒮ℒ :=
    relIndex_inf_mul_relIndex G H 𝒮ℒ
  rw [inf_of_le_left hGH] at h₁
  have h₂ : G.relIndex (𝒮ℒ ⊓ H) * (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex H =
      (G ⊓ 𝒮ℒ).relIndex H := relIndex_inf_mul_relIndex G 𝒮ℒ H
  rw [inf_comm 𝒮ℒ H, ← relIndex_mul_relIndex (G ⊓ 𝒮ℒ) G H inf_le_left hGH,
    inf_relIndex_left] at h₂
  have hn : G.relIndex (H ⊓ 𝒮ℒ) ≠ 0 := G.relIndex_ne_zero
  have hGn : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex G ≠ 0 :=
    (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex_ne_zero
  have hHn : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex H ≠ 0 :=
    (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex_ne_zero
  simp only [ratProjIndex, adjoinNegOne_eq_self_iff.mpr hG,
    adjoinNegOne_eq_self_iff.mpr hH]
  have h₁' : (G.relIndex (H ⊓ 𝒮ℒ) : ℚ) * H.relIndex 𝒮ℒ = G.relIndex 𝒮ℒ := mod_cast h₁
  have h₂' : (G.relIndex (H ⊓ 𝒮ℒ) : ℚ) * (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex H =
      (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex G * G.relIndex H := mod_cast h₂
  have hn' : (G.relIndex (H ⊓ 𝒮ℒ) : ℚ) ≠ 0 := mod_cast hn
  field_simp [hGn, hHn]
  apply mul_left_cancel₀ hn'
  linear_combination (G.relIndex 𝒮ℒ : ℚ) * h₂' -
    ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex G : ℚ) * (G.relIndex H : ℚ) * h₁'

/-- Adjoining `-1` does not change the projective index. -/
private lemma ratProjIndex_adjoinNegOne (G : Subgroup (GL (Fin 2) ℝ)) :
    G.adjoinNegOne.ratProjIndex = G.ratProjIndex := by
  simp only [ratProjIndex, adjoinNegOne_eq_self_iff.mpr G.negOne_mem_adjoinNegOne]

/-- The Sturm bound on the total cusp order of modular forms of level `G` and weight `k`. -/
noncomputable def sturmBound (G : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) : ℝ :=
  k * G.ratProjIndex / 12

lemma sturmBoundSL2Z (k : ℤ) : sturmBound 𝒮ℒ k = k / 12 := by
  have hindex : ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).ratProjIndex =
      ((⊤ : Subgroup SL(2, ℤ)).adjoinNegOne.index : ℚ) := ratProjIndex_coe ⊤
  rw [← MonoidHom.range_eq_map, adjoinNegOne_eq_self_iff.mpr (by simp), index_top] at hindex
  simp [sturmBound, hindex]

private lemma eq_zero_of_orderAtInfty_gt_sturmBound_SL2Z {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (hf : (sturmBound 𝒮ℒ k : EReal) < orderAtInfty f) : f = 0 := by
  rw [sturmBoundSL2Z, orderAtInfty_eq_qExpansion_order one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f), EReal.coe_one, div_one] at hf
  -- Negative weights vanish; for nonnegative weights, natural division rounds the bound down.
  rcases lt_or_ge k 0 with hk | hk
  · exact rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hk) f
  apply ModularForm.sturm_bound_levelOne
  rw [← ENat.toENNReal_lt, ← EReal.coe_ennreal_lt_coe_ennreal_iff]
  refine lt_of_le_of_lt ?_ hf
  simp only [ENat.toENNReal_coe, ← ENNReal.coe_natCast, EReal.coe_nnreal_eq_coe_real,
    NNReal.coe_natCast, EReal.coe_le_coe_iff]
  have hkcast : (k.toNat : ℝ) = (k : ℝ) := mod_cast Int.toNat_of_nonneg hk
  simpa only [hkcast, Nat.cast_ofNat] using (Nat.cast_div_le (α := ℝ) (m := k.toNat) (n := 12))

private lemma totalCuspOrder_le_sturmBound_of_le
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [G.HasDetOne]
    (hG : G ≤ 𝒮ℒ) (hneg : (-1 : GL (Fin 2) ℝ) ∈ G)
    {k : ℤ} (f : ModularForm G k) (hf : f ≠ 0) : totalCuspOrder G k f ≤ G.sturmBound k := by
  have hn : ModularForm.norm 𝒮ℒ f ≠ 0 := ModularForm.norm_ne_zero 𝒮ℒ (by simpa using hf)
  have hbound : orderAtInfty (ModularForm.norm 𝒮ℒ f) ≤ sturmBound 𝒮ℒ (k * G.relIndex 𝒮ℒ) :=
    le_of_not_gt fun h ↦ hn (eq_zero_of_orderAtInfty_gt_sturmBound_SL2Z _ h)
  have hrat : G.ratProjIndex = (G.relIndex 𝒮ℒ : ℚ) := by
    simp [ratProjIndex, adjoinNegOne_eq_self_iff.mpr hneg, relIndex_eq_one.mpr hG]
  rw [sturmBoundSL2Z] at hbound
  have hnorm : totalCuspOrder G k f ≤
      totalCuspOrder 𝒮ℒ (k * Nat.card (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)) (ModularForm.norm 𝒮ℒ f) :=
    totalCuspOrder_le_norm hG hneg f
  rw [totalCuspOrder_SL2Z] at hnorm
  simpa only [sturmBound, hrat, Rat.cast_natCast, Int.cast_mul,
    Int.cast_natCast] using hnorm.trans hbound

private lemma totalCuspOrder_le_sturmBound_of_negOne_mem
    (H : Subgroup (GL (Fin 2) ℝ)) [H.IsArithmetic] [H.HasDetOne]
    (hneg : (-1 : GL (Fin 2) ℝ) ∈ H) {k : ℤ} (f : ModularForm H k) (hf : f ≠ 0) :
    totalCuspOrder H k f ≤ H.sturmBound k := by
  let G := H ⊓ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))
  have hnegG : (-1 : GL (Fin 2) ℝ) ∈ G :=
    ⟨hneg, ⟨-1, by ext i j; simp [mapGL_coe_matrix]⟩⟩
  have hbound : totalCuspOrder G k (ModularForm.restrict inf_le_left f) ≤ G.sturmBound k :=
    totalCuspOrder_le_sturmBound_of_le inf_le_right hnegG _
      ((ModularForm.restrict_eq_zero_iff inf_le_left f).not.mpr hf)
  have hsum : (G.relIndex H : EReal) * totalCuspOrder H k f ≤ G.sturmBound k :=
    (relIndex_mul_totalCuspOrder_eq_restrict inf_le_left hnegG f).le.trans hbound
  have hrat : (G.ratProjIndex : ℝ) = G.relIndex H * (H.ratProjIndex : ℝ) := by
    exact_mod_cast ratProjIndex_eq_relIndex_mul inf_le_left hnegG hneg
  have hpos : (0 : EReal) < G.relIndex H := by
    exact_mod_cast Nat.pos_of_ne_zero G.relIndex_ne_zero
  rw [mul_comm, ← EReal.le_div_iff_mul_le hpos (EReal.natCast_ne_top _)] at hsum
  have hbudget : (G.sturmBound k : EReal) / G.relIndex H = H.sturmBound k := by
    rw [← EReal.coe_natCast, ← EReal.coe_div, EReal.coe_eq_coe_iff]
    simp only [sturmBound, hrat]
    have hd : (G.relIndex H : ℝ) ≠ 0 := by
      exact_mod_cast (show G.relIndex H ≠ 0 from G.relIndex_ne_zero)
    field_simp
  exact hsum.trans_eq hbudget

end Subgroup

namespace ModularForm

/-- The total cusp order of a nonzero modular form is at most the Sturm bound. -/
lemma totalCuspOrder_le_sturmBound
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [G.HasDetOne] {k : ℤ}
    (f : ModularForm G k) (hf : f ≠ 0) : totalCuspOrder G k f ≤ G.sturmBound k := by
  have hn : ModularForm.norm G.adjoinNegOne f ≠ 0 :=
    ModularForm.norm_ne_zero G.adjoinNegOne (by simpa using hf)
  have hbound : totalCuspOrder G.adjoinNegOne
      (k * Nat.card (G.adjoinNegOne ⧸ G.subgroupOf G.adjoinNegOne))
      (ModularForm.norm G.adjoinNegOne f) ≤
      G.adjoinNegOne.sturmBound (k * G.relIndex G.adjoinNegOne) :=
    Subgroup.totalCuspOrder_le_sturmBound_of_negOne_mem
    G.adjoinNegOne G.negOne_mem_adjoinNegOne (ModularForm.norm G.adjoinNegOne f) hn
  have hsum : (G.relIndex G.adjoinNegOne : EReal) * totalCuspOrder G k f ≤
      G.adjoinNegOne.sturmBound (k * G.relIndex G.adjoinNegOne) :=
    (relIndex_mul_totalCuspOrder_le_norm_adjoinNegOne f).trans hbound
  have hpos : (0 : EReal) < G.relIndex G.adjoinNegOne := by
    exact_mod_cast Nat.pos_of_ne_zero G.relIndex_ne_zero
  rw [mul_comm, ← EReal.le_div_iff_mul_le hpos (EReal.natCast_ne_top _)] at hsum
  have hbudget : (G.adjoinNegOne.sturmBound (k * G.relIndex G.adjoinNegOne) : EReal) /
      G.relIndex G.adjoinNegOne = G.sturmBound k := by
    rw [← EReal.coe_natCast, ← EReal.coe_div, EReal.coe_eq_coe_iff]
    simp only [Subgroup.sturmBound, Subgroup.ratProjIndex_adjoinNegOne,
      Int.cast_mul, Int.cast_natCast]
    field_simp [G.relIndex_ne_zero]
  exact hsum.trans_eq hbudget

/-- A form vanishes if its total cusp order exceeds the Sturm bound. -/
lemma eq_zero_of_totalCuspOrder_gt_sturmBound
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [G.HasDetOne] {k : ℤ}
    (f : ModularForm G k) (hf : (G.sturmBound k : EReal) < totalCuspOrder G k f) : f = 0 := by
  grind [totalCuspOrder_le_sturmBound]

/-- A form vanishes if its width-weighted order at infinity exceeds the Sturm bound. -/
lemma eq_zero_of_orderAtInfty_gt_sturmBound
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [G.HasDetOne] {k : ℤ}
    (f : ModularForm G k) (hf : (G.sturmBound k : EReal) < G.widthInfty * orderAtInfty f) :
    f = 0 := by
  apply eq_zero_of_totalCuspOrder_gt_sturmBound f
  have h : orderAtCuspOrbit G k ⟦⟨∞, (Fact.out : IsCusp ∞ G)⟩⟧ f ≤
      totalCuspOrder G k f :=
    orderAtCuspOrbit_le_totalCuspOrder G k ⟦⟨∞, (Fact.out : IsCusp ∞ G)⟩⟧ f
  rw [orderAtCuspOrbit_mk, orderAtCusp_infty G k Fact.out f] at h
  exact hf.trans_le h

/-- Finitely many Fourier coefficients determine a modular form. -/
instance finiteDimensional_complex (G : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [G.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (ModularForm G k) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, G.regularityFactorInfty * G.sturmBound k < N := exists_nat_gt _
  let L : ModularForm G k →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun f i := (qExpansion G.strictWidthInfty f).coeff i
      map_add' f g := by
        ext i
        simp [ModularForm.qExpansion_add G.strictWidthInfty_pos
          G.strictWidthInfty_mem_strictPeriods]
      map_smul' c f := by
        ext i
        simp [ModularForm.qExpansion_smul G.strictWidthInfty_pos
          G.strictWidthInfty_mem_strictPeriods] }
  apply FiniteDimensional.of_injective L
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  by_contra hne
  have horder : (N : ℕ∞) ≤ (qExpansion G.strictWidthInfty f).order :=
    PowerSeries.nat_le_order _ _ fun i hi ↦ congrFun hf ⟨i, hi⟩
  have horder' : (N : EReal) ≤ (qExpansion G.strictWidthInfty f).order := by
    have he : ((N : ℕ∞).toENNReal : EReal) ≤
        ((qExpansion G.strictWidthInfty f).order.toENNReal : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr (ENat.toENNReal_le.mpr horder)
    simpa only [ENat.toENNReal_coe, ← ENNReal.coe_natCast, EReal.coe_nnreal_eq_coe_real,
      NNReal.coe_natCast, EReal.coe_natCast] using he
  have hbound : (qExpansion G.strictWidthInfty f).order ≤
      (G.regularityFactorInfty : EReal) * (G.sturmBound k : EReal) :=
    (qExpansion_order_le_totalCuspOrder G k f).trans
    (mul_le_mul_of_nonneg_left (totalCuspOrder_le_sturmBound f hne) (by positivity))
  have hN' : (G.regularityFactorInfty : EReal) * (G.sturmBound k : EReal) < N := by
    exact_mod_cast hN
  exact hN'.not_ge (horder'.trans hbound)

/-- Modular forms at any arithmetic level form a finite-dimensional real vector space.
Restriction to the intersection with `SL(2, ℤ)` also covers determinant `-1`. -/
instance finiteDimensional_real (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] (k : ℤ) :
    FiniteDimensional ℝ (ModularForm G k) := by
  let K := G ⊓ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))
  let L : ModularForm G k →ₗ[ℝ] ModularForm K k :=
    { toFun := ModularForm.restrict inf_le_left
      map_add' f g := by ext z; rfl
      map_smul' c f := by ext z; rfl }
  exact FiniteDimensional.of_injective L (ModularForm.restrict_injective inf_le_left)

end ModularForm
