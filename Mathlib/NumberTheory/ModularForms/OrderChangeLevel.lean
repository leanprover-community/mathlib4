/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

import Mathlib.Data.EReal.BigOperators

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.OrderAtCusp

/-!
# Total cusp orders under change of level

This file studies how the `totalCuspOrder` of a modular form changes under maps relating different
levels `G ≤ H` (both assumed to be arithmetic subgroups of determinant 1).

* `relIndex_mul_totalCuspOrder_eq_restrict`: if `-1 ∈ G`, restriction from level `H` to level `G`
  multiplies total cusp order by the relative index.
* `totalCuspOrder_eq_norm`: if `-1 ∈ G`, the norm map from level `G` to level `H` preserves
  the total cusp order.
* `relIndex_mul_totalCuspOrder_le_norm_adjoinNegOne`: the comparison for adjoining `-1`,
  accounting for the central index.

These results are proved by a careful study of the fibres of the map on cusp orbits from G to H.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane OnePoint
open scoped Pointwise MatrixGroups Manifold ModularForm

namespace Subgroup

/-- Translation by an integral multiple of the strict width of `H`. -/
private noncomputable def translation (H : Subgroup (GL (Fin 2) ℝ)) (m : ℤ) : H :=
  ⟨Matrix.GeneralLinearGroup.upperRightHom (m * H.strictWidthInfty),
    H.mem_strictPeriods_iff.mp (by
      simpa only [zsmul_eq_mul] using
        H.strictPeriods.zsmul_mem H.strictWidthInfty_mem_strictPeriods m)⟩

/-- Strict widths multiply by a positive integer under inclusion. -/
private lemma strictWidthInfty_eq_nat_mul {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hGH : G ≤ H) :
    ∃ n : ℕ, 0 < n ∧ G.strictWidthInfty = n * H.strictWidthInfty := by
  have hw : G.strictWidthInfty ∈ H.strictPeriods :=
    H.mem_strictPeriods_iff.mpr
      (hGH (G.mem_strictPeriods_iff.mp G.strictWidthInfty_mem_strictPeriods))
  rw [strictPeriods_eq_zmultiples_strictWidthInfty] at hw
  obtain ⟨m, hm⟩ := hw
  simp only [zsmul_eq_mul] at hm
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := (mul_pos_iff_of_pos_right H.strictWidthInfty_pos).mp
      (hm.symm ▸ G.strictWidthInfty_pos)
    exact_mod_cast this
  have hmcast : (m.toNat : ℝ) = (m : ℝ) := mod_cast Int.toNat_of_nonneg hmpos.le
  grind

private lemma translation_pow (H : Subgroup (GL (Fin 2) ℝ)) (n : ℕ) :
    translation H 1 ^ n = translation H n := by
  ext
  simp [translation, ← AddChar.map_nsmul_eq_pow, -Matrix.GeneralLinearGroup.upperRightHom_apply]

private lemma translation_isPeriodicPt_iff {K H : Subgroup (GL (Fin 2) ℝ)} (r : H) (n : ℕ) :
    Function.IsPeriodicPt (fun q : H ⧸ K.subgroupOf H ↦ translation H 1 • q) n ⟦r⟧ ↔
      (translation H n : GL (Fin 2) ℝ) ∈ ConjAct.toConjAct (r : GL (Fin 2) ℝ) • K := by
  rw [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate_apply, translation_pow,
    MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq]
  simp only [smul_eq_mul, inv_inv, mul_assoc, mem_subgroupOf, coe_mul, coe_inv,
    mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
    ConjAct.ofConjAct_toConjAct]

private lemma minimalPeriod_translation {K H : Subgroup (GL (Fin 2) ℝ)} [H.IsArithmetic]
    (r : H) [(ConjAct.toConjAct (r : GL (Fin 2) ℝ) • K).IsArithmetic] {n : ℕ}
    (hw : (ConjAct.toConjAct (r : GL (Fin 2) ℝ) • K).strictWidthInfty =
      n * H.strictWidthInfty) :
    Function.minimalPeriod (fun q : H ⧸ K.subgroupOf H ↦ translation H 1 • q) ⟦r⟧ = n := by
  refine Nat.dvd_right_iff_eq.mp fun m ↦ ?_
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd, translation_isPeriodicPt_iff, translation,
    ← mem_strictPeriods_iff, strictPeriods_eq_zmultiples_strictWidthInfty, hw]
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ ⟨a, by grind [Int.cast_natCast]⟩⟩
  simp only [zsmul_eq_mul, ← mul_assoc, mul_left_inj' H.strictWidthInfty_pos.ne'] at ha
  exact Int.natCast_dvd_natCast.mp (Dvd.intro_left a (by exact_mod_cast ha))

/-- The cycles of the translation by the strict width of the larger group. -/
private abbrev TranslationCycles (K H : Subgroup (GL (Fin 2) ℝ)) :=
  MulAction.orbitRel.Quotient (zpowers (translation H 1)) (H ⧸ K.subgroupOf H)

/-- The class formula for the translation action gives the sum of cusp widths in the fiber.
The orbit representatives are read as inverse scaling matrices. -/
private lemma sum_strictWidthInfty_translationCycles {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] (hKH : K ≤ H) :
    let := Fintype.ofFinite (TranslationCycles K H)
    ∑ c : TranslationCycles K H,
        (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).strictWidthInfty =
      K.relIndex H * H.strictWidthInfty := by
  intro
  rw [relIndex, index_eq_sum_minimalPeriod _ (translation H 1), Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have := isArithmetic_conj_of_mem (K := K) c.out.out.property
  obtain ⟨n, -, hw⟩ := strictWidthInfty_eq_nat_mul <|
    (pointwise_smul_le_pointwise_smul_iff.mpr hKH).trans
      (conjAct_pointwise_smul_eq_self (H.le_normalizer c.out.out.property)).le
  rw [hw, ← minimalPeriod_translation c.out.out hw, Quotient.out_eq]

private lemma translation_zpow (H : Subgroup (GL (Fin 2) ℝ)) (m : ℤ) :
    translation H 1 ^ m = translation H m := by
  apply Subtype.ext
  simp only [translation, coe_zpow, Int.cast_one, one_mul]
  rw [← AddChar.map_zsmul_eq_zpow]
  simp only [zsmul_eq_mul]

private lemma exists_translation_or_neg_of_fixing_infty
    {H : Subgroup (GL (Fin 2) ℝ)} [H.IsArithmetic] [H.HasDetOne]
    (hneg : -1 ∈ H) (g : H) (hg : (g : GL (Fin 2) ℝ) • ∞ = (∞ : OnePoint ℝ)) :
    ∃ m : ℤ, (g : GL (Fin 2) ℝ) = translation H m ∨
      (g : GL (Fin 2) ℝ) = -translation H m := by
  have htri : (g : GL (Fin 2) ℝ) 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hg
  rcases H.eq_upperRightHom_or_neg_of_upperTriangular H.widthInfty_pos g.property htri with h | h
  · have hp : (g : GL (Fin 2) ℝ) 0 1 ∈ H.strictPeriods := by
      rw [mem_strictPeriods_iff, ← h]
      exact g.property
    rw [strictPeriods_eq_zmultiples_strictWidthInfty] at hp
    obtain ⟨m, hm⟩ := hp
    simp only [zsmul_eq_mul] at hm
    exact ⟨m, Or.inl (by simpa only [translation, zsmul_eq_mul, hm] using h)⟩
  · have hp : -(g : GL (Fin 2) ℝ) 0 1 ∈ H.strictPeriods := by
      rw [mem_strictPeriods_iff]
      have hn : -(g : GL (Fin 2) ℝ) ∈ H := by
        simpa only [neg_one_mul] using H.mul_mem hneg g.property
      rw [h, neg_neg] at hn
      exact hn
    rw [strictPeriods_eq_zmultiples_strictWidthInfty] at hp
    obtain ⟨m, hm⟩ := hp
    simp only [zsmul_eq_mul] at hm
    exact ⟨m, Or.inr (by simpa only [translation, zsmul_eq_mul, hm] using h)⟩

/-- A coset determines a cusp above infinity of the larger group. -/
private noncomputable def cosetCusp (G H : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [H.IsArithmetic] : (H ⧸ G.subgroupOf H) → CuspOrbits G :=
  Quotient.lift (fun r ↦ ⟦⟨(r : GL (Fin 2) ℝ)⁻¹ • ∞,
    ((show IsCusp ∞ H from Fact.out).smul_of_mem
      (H.inv_mem r.property)).of_isFiniteRelIndex⟩⟧) (by
    intro a b hab
    rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hab
    refine Quotient.eq.mpr ⟨⟨(a : GL (Fin 2) ℝ)⁻¹ * b, hab⟩, ?_⟩
    apply Subtype.ext
    exact show ((a : GL (Fin 2) ℝ)⁻¹ * b) • ((b : GL (Fin 2) ℝ)⁻¹ • (∞ : OnePoint ℝ)) =
        (a : GL (Fin 2) ℝ)⁻¹ • ∞ from by simp only [mul_smul, smul_inv_smul])

private lemma cosetCusp_translation (G H : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [H.IsArithmetic] (t : zpowers (translation H 1))
    (q : H ⧸ G.subgroupOf H) : cosetCusp G H (t • q) = cosetCusp G H q := by
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp t.property
  obtain ⟨t, ht⟩ := t
  dsimp only at hm
  subst t
  induction q using Quotient.inductionOn with | h r =>
  have hfix : (translation H m : GL (Fin 2) ℝ)⁻¹ • (∞ : OnePoint ℝ) = ∞ := by
    simp [translation, OnePoint.smul_infty_eq_ite]
  simp only [Subgroup.smul_def, translation_zpow, MulAction.Quotient.smul_mk,
    smul_eq_mul, cosetCusp, Quotient.lift_mk, coe_mul, mul_inv_rev, mul_smul, hfix]

/-- The cusp belonging to a translation cycle of the finite coset space. -/
private noncomputable def translationCycleCusp (K H : Subgroup (GL (Fin 2) ℝ))
    [K.IsArithmetic] [H.IsArithmetic] (c : TranslationCycles K H) : CuspOrbits K :=
  ⟦⟨(c.out.out : GL (Fin 2) ℝ)⁻¹ • ∞,
    ((show IsCusp ∞ H from Fact.out).smul_of_mem
      (H.inv_mem c.out.out.property)).of_isFiniteRelIndex⟩⟧

private lemma translationCycleCusp_mk {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] (r : H) :
    translationCycleCusp K H ⟦(⟦r⟧ : H ⧸ K.subgroupOf H)⟧ = cosetCusp K H ⟦r⟧ := by
  let c : TranslationCycles K H := ⟦(⟦r⟧ : H ⧸ K.subgroupOf H)⟧
  have hout : translationCycleCusp K H c = cosetCusp K H c.out :=
    congr(cosetCusp K H $(Quotient.out_eq c.out))
  obtain ⟨t, ht⟩ := Quotient.eq.mp (Quotient.out_eq c)
  rw [hout, ← ht, cosetCusp_translation]

private lemma translationCycleCusp_surjective_fiber {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] (hKH : K ≤ H) (c : CuspOrbits K)
    (hc : CuspOrbits.map hKH c = ⟦⟨∞, (Fact.out : IsCusp ∞ H)⟩⟧) :
    ∃ d : TranslationCycles K H, translationCycleCusp K H d = c := by
  induction c using Quotient.inductionOn with | h c =>
  obtain ⟨r, hr⟩ := Quotient.eq.mp hc
  have hr' : (r : GL (Fin 2) ℝ) • ∞ = c.val := congr(Subtype.val $hr)
  refine ⟨⟦(⟦r⁻¹⟧ : H ⧸ K.subgroupOf H)⟧, ?_⟩
  rw [translationCycleCusp_mk]
  simp only [cosetCusp, Quotient.lift_mk, coe_inv, inv_inv, hr']

/-- With `-1` in the smaller level, distinct translation cycles give inequivalent cusps. -/
private lemma translationCycleCusp_injective {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] [H.HasDetOne] (hKH : K ≤ H)
    (hneg : -1 ∈ K) :
    Function.Injective (translationCycleCusp K H) := by
  intro c d hcd
  obtain ⟨a, ha⟩ := Quotient.eq.mp hcd
  have ha' : (a : GL (Fin 2) ℝ) • ((d.out.out : GL (Fin 2) ℝ)⁻¹ • (∞ : OnePoint ℝ)) =
      (c.out.out : GL (Fin 2) ℝ)⁻¹ • ∞ := congr(Subtype.val $ha)
  let b : H := c.out.out * ⟨a, hKH a.property⟩ * d.out.out⁻¹
  have hb : (b : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) = ∞ := by
    dsimp only [b, coe_mul, coe_inv]
    rw [mul_smul, mul_smul, ha', smul_inv_smul]
  obtain ⟨m, hm⟩ := exists_translation_or_neg_of_fixing_infty (hKH hneg) b hb
  have hcos : (translation H 1 ^ m) • d.out = c.out := by
    rw [← Quotient.out_eq d.out, ← Quotient.out_eq c.out, translation_zpow,
      MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simp only [smul_eq_mul, mem_subgroupOf, coe_mul, coe_inv]
    rcases hm with hm | hm
    · have heq : (translation H m : GL (Fin 2) ℝ) =
          (c.out.out : GL (Fin 2) ℝ) * a * (d.out.out : GL (Fin 2) ℝ)⁻¹ := hm.symm
      rw [heq]
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
        mul_inv_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using
        K.inv_mem a.property
    · have heq : (translation H m : GL (Fin 2) ℝ) =
          -((c.out.out : GL (Fin 2) ℝ) * a * (d.out.out : GL (Fin 2) ℝ)⁻¹) := by
        simpa only [b, coe_mul, coe_inv, neg_neg] using congr(-$hm.symm)
      rw [heq]
      simpa only [mul_inv_rev, inv_inv, inv_neg, neg_mul, mul_neg, mul_assoc,
        inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel_right, inv_mul_cancel,
        mul_one, one_mul, neg_one_mul] using K.mul_mem hneg (K.inv_mem a.property)
  rw [← Quotient.out_eq c, ← Quotient.out_eq d]
  exact Quotient.eq.mpr ⟨⟨_, mem_zpowers_iff.mpr ⟨m, rfl⟩⟩, hcos⟩

/-- The factors represented by translations have the same order as the original form. -/
private lemma quotientFunc_translation_order {G H : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} (f : ModularForm G k) (m : ℤ) :
    orderAtInfty (SlashInvariantForm.quotientFunc f
      (⟦translation H m⟧ : H ⧸ G.subgroupOf H)) = orderAtInfty f := by
  simp [translation, orderAtInfty_slash_of_upperTriangular]

/-- Every translation cycle lies over the cusp at infinity of the larger group. -/
private lemma translationCycleCusp_map {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] (hKH : K ≤ H) (c : TranslationCycles K H) :
    CuspOrbits.map hKH (translationCycleCusp K H c) =
      ⟦⟨∞, (Fact.out : IsCusp ∞ H)⟩⟧ := by
  refine Quotient.eq.mpr ⟨c.out.out⁻¹, ?_⟩
  exact Subtype.ext rfl

open scoped Classical in
/-- Restriction counts the full degree in the fiber above infinity. -/
lemma relIndex_mul_orderAtCusp_infty_eq_sum_fiber_restrict
    {K H : Subgroup (GL (Fin 2) ℝ)} [K.IsArithmetic] [H.IsArithmetic]
    [H.HasDetOne] (hKH : K ≤ H) (hnegK : (-1 : GL (Fin 2) ℝ) ∈ K)
    {k : ℤ} (f : ModularForm H k) :
    let := Fintype.ofFinite (CuspOrbits K)
    (K.relIndex H : EReal) * orderAtCusp H k ∞ f =
      ∑ c with CuspOrbits.map hKH c = ⟦⟨∞, (Fact.out : IsCusp ∞ H)⟩⟧,
        orderAtCuspOrbit K k c (ModularForm.restrict hKH f) := by
  let := Fintype.ofFinite (CuspOrbits K)
  let := Fintype.ofFinite (TranslationCycles K H)
  let e : TranslationCycles K H ↪ CuspOrbits K :=
    ⟨translationCycleCusp K H, translationCycleCusp_injective hKH hnegK⟩
  have hsubset : Finset.univ.map e ⊆ Finset.univ.filter
      (fun c ↦ CuspOrbits.map hKH c = ⟦⟨∞, (Fact.out : IsCusp ∞ H)⟩⟧) := by
    intro c hc
    obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, translationCycleCusp_map hKH d⟩
  have hsets : Finset.univ.map e = Finset.univ.filter
      (fun c ↦ CuspOrbits.map hKH c = ⟦⟨∞, (Fact.out : IsCusp ∞ H)⟩⟧) := by
    refine hsubset.antisymm fun c hc ↦ ?_
    obtain ⟨d, hd⟩ := translationCycleCusp_surjective_fiber hKH c (Finset.mem_filter.mp hc).2
    exact Finset.mem_map.mpr ⟨d, Finset.mem_univ _, hd⟩
  have hsum : ∑ c ∈ Finset.univ.map e, orderAtCuspOrbit K k c (ModularForm.restrict hKH f) =
      ∑ c with CuspOrbits.map hKH c = ⟦⟨∞, (Fact.out : IsCusp ∞ H)⟩⟧,
        orderAtCuspOrbit K k c (ModularForm.restrict hKH f) := by
    rw [hsets]
  have horder (c : TranslationCycles K H) :
      orderAtCuspOrbit K k (e c) (ModularForm.restrict hKH f) =
        (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).widthInfty * orderAtInfty f := by
    have hc : IsCusp ((c.out.out : GL (Fin 2) ℝ)⁻¹ • ∞) K :=
      ((show IsCusp ∞ H from Fact.out).smul_of_mem
        (H.inv_mem c.out.out.property)).of_isFiniteRelIndex
    rw [show e c = ⟦⟨(c.out.out : GL (Fin 2) ℝ)⁻¹ • ∞,
      ((show IsCusp ∞ H from Fact.out).smul_of_mem
        (H.inv_mem c.out.out.property)).of_isFiniteRelIndex⟩⟧ from rfl,
      orderAtCuspOrbit_mk, orderAtCusp_eq K k hc _ (c.out.out : GL (Fin 2) ℝ)⁻¹ rfl]
    simp only [inv_inv, ModularForm.coe_restrict,
      SlashInvariantFormClass.slash_action_eq f _ (H.inv_mem c.out.out.property)]
  rw [Finset.sum_map] at hsum
  simp_rw [horder] at hsum
  rw [← EReal.sum_mul_of_nonneg (fun c _ ↦ EReal.coe_nonneg.mpr (widthInfty_nonneg _)),
    ← EReal.coe_finsetSum] at hsum
  have hwidth : ∑ c : TranslationCycles K H,
      (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).widthInfty =
        K.relIndex H * H.widthInfty := by
    simpa only [widthInfty, adjoinNegOne_conj, adjoinNegOne_eq_self_iff.mpr hnegK,
      adjoinNegOne_eq_self_iff.mpr (hKH hnegK)] using sum_strictWidthInfty_translationCycles hKH
  simpa only [hwidth, EReal.coe_mul, EReal.coe_natCast, mul_assoc,
    orderAtCusp_infty H k (Fact.out : IsCusp ∞ H) f] using hsum

private lemma sum_translationCycles {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (b : (H ⧸ G.subgroupOf H) → EReal)
    (hb : ∀ (t : zpowers (translation H 1)) q, b (t • q) = b q) :
    let := Fintype.ofFinite (TranslationCycles G H)
    let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
    ∑ c : TranslationCycles G H,
      (Function.minimalPeriod (fun q : H ⧸ G.subgroupOf H ↦ translation H 1 • q) c.out : EReal) *
        b c.out = ∑ q : H ⧸ G.subgroupOf H, b q := by
  let := Fintype.ofFinite (TranslationCycles G H)
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  let (c : TranslationCycles G H) :=
    Fintype.ofFinite (MulAction.orbit (zpowers (translation H 1)) c.out)
  have hval (c : TranslationCycles G H) (q : MulAction.orbit (zpowers (translation H 1)) c.out) :
      b q.val = b c.out := by
    obtain ⟨t, ht⟩ := q.property
    rw [← ht, hb]
  have heval (c : TranslationCycles G H)
      (q : MulAction.orbit (zpowers (translation H 1)) c.out) :
      (MulAction.selfEquivSigmaOrbits (zpowers (translation H 1)) (H ⧸ G.subgroupOf H)).symm
        ⟨c, q⟩ = q.val := rfl
  have hs := (MulAction.selfEquivSigmaOrbits (zpowers (translation H 1))
    (H ⧸ G.subgroupOf H)).symm.sum_comp b
  simpa only [Fintype.sum_sigma, heval, hval, Finset.sum_const, Finset.card_univ,
    EReal.nsmul_eq_mul, MulAction.minimalPeriod_eq_card, Nat.card_eq_fintype_card] using hs

private lemma quotientFunc_translationCycle_order {G H : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} (f : ModularForm G k) (t : zpowers (translation H 1)) (q : H ⧸ G.subgroupOf H) :
    orderAtInfty (SlashInvariantForm.quotientFunc f (t • q)) =
      orderAtInfty (SlashInvariantForm.quotientFunc f q) := by
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp t.property
  obtain ⟨t, ht⟩ := t
  dsimp only at hm
  subst t
  induction q using Quotient.inductionOn with | h r =>
  simp only [Subgroup.smul_def, translation_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
    SlashInvariantForm.quotientFunc_mk, coe_mul, mul_inv_rev, SlashAction.slash_mul]
  exact quotientFunc_translation_order (ModularForm.translate f (r : GL (Fin 2) ℝ)⁻¹) m

end Subgroup

namespace UpperHalfPlane

open Subgroup

open scoped Classical in
/-- The sum of cusp orders in a fiber of the map induced by an inclusion. -/
noncomputable def cuspOrderFiber {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] (hGH : G ≤ H) {k : ℤ} (f : ModularForm G k) (c : CuspOrbits H) : EReal :=
  let := Fintype.ofFinite (CuspOrbits G)
  ∑ d with CuspOrbits.map hGH d = c, orderAtCuspOrbit G k d f

/-- Summing over the fibers recovers the total cusp order. -/
lemma sum_cuspOrderFiber {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hGH : G ≤ H) {k : ℤ} (f : ModularForm G k) :
    let := Fintype.ofFinite (CuspOrbits H)
    ∑ c, cuspOrderFiber hGH f c = totalCuspOrder G k f := by
  classical
  let := Fintype.ofFinite (CuspOrbits G)
  let := Fintype.ofFinite (CuspOrbits H)
  exact Finset.sum_fiberwise Finset.univ (CuspOrbits.map hGH) (orderAtCuspOrbit G k · f)

/-- A change of cusp coordinates preserves the sum over a fiber. -/
lemma cuspOrderFiber_translate {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] (hGH : G ≤ H) {k : ℤ}
    (f : ModularForm G k) (c : CuspOrbits H) (g : GL (Fin 2) ℝ)
    [(ConjAct.toConjAct g⁻¹ • G).IsArithmetic] :
    cuspOrderFiber ((pointwise_smul_le_pointwise_smul_iff
      (a := ConjAct.toConjAct g⁻¹)).mpr hGH)
      (ModularForm.translate f g) (CuspOrbits.conj H g⁻¹ c) = cuspOrderFiber hGH f c := by
  exact (Finset.sum_bijective _ (CuspOrbits.conj_bijective G g⁻¹)
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, CuspOrbits.map_conj hGH g⁻¹,
      (CuspOrbits.conj_bijective H g⁻¹).injective.eq_iff, implies_true])
    fun d _ ↦ (orderAtCuspOrbit_translate G k d f g).symm).symm

/-- Restriction contributes the full relative index in each cusp fiber, when the smaller
level contains `-1`. -/
lemma relIndex_mul_orderAtCuspOrbit_eq_cuspOrderFiber_restrict
    {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [H.IsArithmetic]
    [H.HasDetOne] (hGH : G ≤ H) (hneg : -1 ∈ G)
    {k : ℤ} (f : ModularForm H k) (c : CuspOrbits H) :
    (G.relIndex H : EReal) * orderAtCuspOrbit H k c f =
      cuspOrderFiber hGH (ModularForm.restrict hGH f) c := by
  obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp
    ((IsArithmetic.isCusp_iff_isCusp_SL2Z H).mp c.out.property)
  let s := mapGL ℝ g
  have hs : s • ∞ = (c.out : OnePoint ℝ) := hg.symm
  let G' := ConjAct.toConjAct s⁻¹ • G
  let H' := ConjAct.toConjAct s⁻¹ • H
  have : G'.IsArithmetic := isArithmetic_conj_of_mem
    ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).inv_mem ⟨g, rfl⟩)
  have : H'.IsArithmetic := isArithmetic_conj_of_mem
    ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).inv_mem ⟨g, rfl⟩)
  have hle : G' ≤ H' := by simpa [G', H']
  have hneg' : (-1 : GL (Fin 2) ℝ) ∈ G' := by
    simpa only [G', mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
      mul_neg, mul_one, neg_mul, mul_inv_cancel] using hneg
  have hc : CuspOrbits.conj H s⁻¹ c = ⟦⟨∞, (Fact.out : IsCusp ∞ H')⟩⟧ := by
    rw [← Quotient.out_eq c, CuspOrbits.conj_mk]
    have heq : s⁻¹ • (c.out : OnePoint ℝ) = ∞ := inv_smul_eq_iff.mpr hs.symm
    simp only [heq]
  have hcoord : orderAtCusp H' k ∞ (ModularForm.translate f s) =
      orderAtCuspOrbit H k c f := by
    simpa only [hc, orderAtCuspOrbit_mk] using orderAtCuspOrbit_translate H k c f s
  have hre : ModularForm.restrict hle (ModularForm.translate f s) =
      ModularForm.translate (ModularForm.restrict hGH f) s := by simp [hGH]
  have hlocal : (G'.relIndex H' : EReal) *
      orderAtCusp H' k ∞ (ModularForm.translate f s) =
        cuspOrderFiber hle (ModularForm.restrict hle (ModularForm.translate f s))
          ⟦⟨∞, (Fact.out : IsCusp ∞ H')⟩⟧ :=
    relIndex_mul_orderAtCusp_infty_eq_sum_fiber_restrict hle hneg' (ModularForm.translate f s)
  rw [hre, ← hc, cuspOrderFiber_translate hGH (ModularForm.restrict hGH f) c s] at hlocal
  simpa only [G', H', relIndex_pointwise_smul, hcoord] using hlocal

/-- Restriction multiplies total cusp order by the relative index when `-1`
belongs to the smaller level. -/
lemma relIndex_mul_totalCuspOrder_eq_restrict {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic]
    [H.IsArithmetic] [H.HasDetOne] (hGH : G ≤ H) (hneg : -1 ∈ G)
    {k : ℤ} (f : ModularForm H k) :
    (G.relIndex H : EReal) * totalCuspOrder H k f =
      totalCuspOrder G k (ModularForm.restrict hGH f) := by
  classical
  let := Fintype.ofFinite (CuspOrbits H)
  rw [← sum_cuspOrderFiber hGH, totalCuspOrder, ← EReal.coe_natCast (n := G.relIndex H),
    EReal.mul_sum_of_nonneg_of_ne_top (by positivity) (by simp)]
  exact Finset.sum_congr rfl fun c _ ↦
    relIndex_mul_orderAtCuspOrbit_eq_cuspOrderFiber_restrict hGH hneg f c

/-- In the fiber above infinity, the widths exactly count the factors of a norm. -/
lemma cuspOrderFiber_infty_eq_sum_quotientFunc
    {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [H.IsArithmetic]
    [H.HasDetOne] (hGH : G ≤ H) (hneg : -1 ∈ G)
    {k : ℤ} (f : ModularForm G k) :
    let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
    cuspOrderFiber hGH f ⟦⟨∞, (Fact.out : IsCusp ∞ H)⟩⟧ = H.widthInfty *
      ∑ q : H ⧸ G.subgroupOf H, orderAtInfty (SlashInvariantForm.quotientFunc f q) := by
  intro
  classical
  let := Fintype.ofFinite (CuspOrbits G)
  let := Fintype.ofFinite (TranslationCycles G H)
  let e : TranslationCycles G H ↪ CuspOrbits G :=
    ⟨translationCycleCusp G H, translationCycleCusp_injective hGH hneg⟩
  have hsets : Finset.univ.map e = Finset.univ.filter
      (fun c ↦ CuspOrbits.map hGH c = ⟦⟨∞, (Fact.out : IsCusp ∞ H)⟩⟧) := Finset.ext fun c ↦ by
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨d, hd⟩ ↦ hd ▸ translationCycleCusp_map hGH d,
      translationCycleCusp_surjective_fiber hGH c⟩
  have horder (c : TranslationCycles G H) : orderAtCuspOrbit G k (e c) f = (H.widthInfty : EReal) *
      ((Function.minimalPeriod (fun q : H ⧸ G.subgroupOf H ↦ translation H 1 • q) c.out : EReal) *
        orderAtInfty (SlashInvariantForm.quotientFunc f c.out)) := by
    let r := c.out.out
    have := isArithmetic_conj_of_mem (K := G) r.property
    obtain ⟨n, -, hw⟩ := strictWidthInfty_eq_nat_mul <|
      (pointwise_smul_le_pointwise_smul_iff.mpr hGH).trans
        (conjAct_pointwise_smul_eq_self (H.le_normalizer r.property)).le
    have hp : Function.minimalPeriod
        (fun q : H ⧸ G.subgroupOf H ↦ translation H 1 • q) c.out = n := by
      simpa only [r, Quotient.out_eq] using minimalPeriod_translation r hw
    have hw' : (ConjAct.toConjAct (r : GL (Fin 2) ℝ) • G).widthInfty = H.widthInfty * n := by
      simpa only [widthInfty, adjoinNegOne_conj, adjoinNegOne_eq_self_iff.mpr hneg,
        adjoinNegOne_eq_self_iff.mpr (hGH hneg), mul_comm] using hw
    have hc : IsCusp ((r : GL (Fin 2) ℝ)⁻¹ • ∞) G :=
      ((show IsCusp ∞ H from Fact.out).smul_of_mem (H.inv_mem r.property)).of_isFiniteRelIndex
    rw [orderAtCuspOrbit_eq G k (e c) ⟨_, hc⟩ rfl, orderAtCusp_eq G k hc f (r : GL (Fin 2) ℝ)⁻¹ rfl,
      inv_inv, hw', hp, congr(SlashInvariantForm.quotientFunc f $(Quotient.out_eq c.out)).symm,
      SlashInvariantForm.quotientFunc_mk, EReal.coe_mul, EReal.coe_natCast, mul_assoc]
  rw [cuspOrderFiber, ← hsets, Finset.sum_map, Finset.sum_congr rfl fun c _ ↦ horder c,
    ← EReal.mul_sum_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr H.widthInfty_nonneg) (by simp),
    sum_translationCycles (fun q ↦
      orderAtInfty (SlashInvariantForm.quotientFunc f q)) (quotientFunc_translationCycle_order f)]

/-- Conjugation identifies the two coset spaces used in a norm. -/
private noncomputable def conjugateCosets (G H : Subgroup (GL (Fin 2) ℝ)) (s : GL (Fin 2) ℝ) :
    (H ⧸ G.subgroupOf H) ≃
      (↥(ConjAct.toConjAct s⁻¹ • H) ⧸
        (ConjAct.toConjAct s⁻¹ • G).subgroupOf (ConjAct.toConjAct s⁻¹ • H)) := by
  let e : H ≃ ↥(ConjAct.toConjAct s⁻¹ • H) :=
    { toFun r := ⟨ConjAct.toConjAct s⁻¹ • r.val, H.smul_mem_pointwise_smul _ _ r.property⟩
      invFun r := ⟨ConjAct.toConjAct s • r.val, by
        simpa only [ConjAct.toConjAct_inv, inv_inv] using
          H.mem_pointwise_smul_iff_inv_smul_mem.mp r.property⟩
      left_inv r := Subtype.ext (by simp [ConjAct.smul_def, mul_assoc])
      right_inv r := Subtype.ext (by simp [ConjAct.smul_def, mul_assoc]) }
  have he (r : H) : (e r : GL (Fin 2) ℝ) = s⁻¹ * r * s := rfl
  refine Quotient.congr e ?_
  intro a b
  constructor
  · intro h
    have hm : a⁻¹ * b ∈ G.subgroupOf H := QuotientGroup.leftRel_apply.mp h
    apply QuotientGroup.leftRel_apply.mpr
    have hm' : (a : GL (Fin 2) ℝ)⁻¹ * b ∈ G := hm
    suffices (e a : GL (Fin 2) ℝ)⁻¹ * e b ∈ ConjAct.toConjAct s⁻¹ • G from this
    rw [he a, he b, mem_pointwise_smul_iff_inv_smul_mem]
    simpa only [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct,
      inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_inv_cancel_right, mul_inv_cancel, mul_one] using hm'
  · intro h
    have hm : (e a)⁻¹ * e b ∈
        (ConjAct.toConjAct s⁻¹ • G).subgroupOf (ConjAct.toConjAct s⁻¹ • H) :=
      QuotientGroup.leftRel_apply.mp h
    have hm' : (e a : GL (Fin 2) ℝ)⁻¹ * e b ∈ ConjAct.toConjAct s⁻¹ • G := hm
    rw [he a, he b, mem_pointwise_smul_iff_inv_smul_mem] at hm'
    apply QuotientGroup.leftRel_apply.mpr
    simpa only [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct,
      inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_inv_cancel_right, mul_inv_cancel, mul_one, mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv] using hm'

private lemma conjugateCosets_mk (G H : Subgroup (GL (Fin 2) ℝ)) (s : GL (Fin 2) ℝ) (r : H) :
    conjugateCosets G H s ⟦r⟧ = ⟦⟨ConjAct.toConjAct s⁻¹ • r.val,
      H.smul_mem_pointwise_smul _ _ r.property⟩⟧ := rfl

private lemma quotientFunc_conjugateCosets
    {G H : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm G k)
    (s : GL (Fin 2) ℝ) (q : H ⧸ G.subgroupOf H) :
    SlashInvariantForm.quotientFunc (ModularForm.translate f s) (conjugateCosets G H s q) =
      SlashInvariantForm.quotientFunc f q ∣[k] s := by
  induction q using Quotient.inductionOn with | h r =>
  rw [conjugateCosets_mk G H s r, SlashInvariantForm.quotientFunc_mk,
    SlashInvariantForm.quotientFunc_mk]
  rw [ModularForm.coe_translate]
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
    mul_inv_rev, inv_inv, ← SlashAction.slash_mul, mul_assoc, mul_inv_cancel_left]

/-- The order of the norm in a determinant-one coordinate is the sum of the orders of its factors
in that coordinate. -/
lemma sum_orderAtInfty_slash_quotientFunc_eq_norm
    {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [H.IsArithmetic]
    {k : ℤ} (f : ModularForm G k) (g : SL(2, ℤ)) :
    let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
    ∑ q : H ⧸ G.subgroupOf H, orderAtInfty (SlashInvariantForm.quotientFunc f q ∣[k] mapGL ℝ g) =
      orderAtInfty ((ModularForm.norm H f : ℍ → ℂ) ∣[k * G.relIndex H] mapGL ℝ g) := by
  intro _
  have hprod : (ModularForm.norm H f : ℍ → ℂ) ∣[k * G.relIndex H] mapGL ℝ g =
      ∏ q : H ⧸ G.subgroupOf H, SlashInvariantForm.quotientFunc f q ∣[k] mapGL ℝ g := by
    simp [ModularForm.coe_norm, show G.relIndex H = Fintype.card (H ⧸ G.subgroupOf H) from
      Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash]
  have hq (q : H ⧸ G.subgroupOf H) : SlashInvariantForm.quotientFunc f q =
      (f : ℍ → ℂ) ∣[k] (q.out : GL (Fin 2) ℝ)⁻¹ := by
    rw [← SlashInvariantForm.quotientFunc_mk f q.out, Quotient.out_eq]
  simp only [hprod, hq]
  let K (q : H ⧸ G.subgroupOf H) := ConjAct.toConjAct (mapGL ℝ g)⁻¹ •
    (ConjAct.toConjAct (q.out : GL (Fin 2) ℝ) • G)
  have hK (q : H ⧸ G.subgroupOf H) : (K q).IsArithmetic :=
    have := isArithmetic_conj_of_mem (K := G) q.out.property
    isArithmetic_conj_of_mem <| (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).inv_mem ⟨g, rfl⟩
  let F (q : H ⧸ G.subgroupOf H) : ModularForm (K q) k :=
    ModularForm.translate (ModularForm.translate f (q.out : GL (Fin 2) ℝ)⁻¹) (mapGL ℝ g)
  exact (orderAtInfty_prod_of_holo (fun q _ ↦ strictWidthInfty_pos (K q))
    (fun q _ ↦ SlashInvariantFormClass.periodic_comp_ofComplex (F q)
      (K q).strictWidthInfty_mem_strictPeriods) (fun q _ ↦ (F q).holo')
    fun q _ ↦ ModularFormClass.bdd_at_infty (F q)).symm

/-- The order of a norm at a target cusp is the sum over the source cusp fiber. -/
lemma cuspOrderFiber_eq_orderAtCuspOrbit_norm {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic]
    [H.IsArithmetic] [H.HasDetOne] (hGH : G ≤ H) (hneg : -1 ∈ G)
    {k : ℤ} (f : ModularForm G k) (c : CuspOrbits H) :
    cuspOrderFiber hGH f c = orderAtCuspOrbit H (k * Nat.card (H ⧸ G.subgroupOf H)) c
      (ModularForm.norm H f) := by
  induction c using Quotient.inductionOn with | h d =>
  obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp ((IsArithmetic.isCusp_iff_isCusp_SL2Z H).mp d.property)
  let s := mapGL ℝ g
  let G' := ConjAct.toConjAct s⁻¹ • G
  let H' := ConjAct.toConjAct s⁻¹ • H
  have hsm := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).inv_mem ⟨g, rfl⟩
  have : G'.IsArithmetic := isArithmetic_conj_of_mem hsm
  have : H'.IsArithmetic := isArithmetic_conj_of_mem hsm
  have hle : G' ≤ H' := pointwise_smul_le_pointwise_smul_iff.mpr hGH
  have hneg' : -1 ∈ G' := by
    simpa [G', mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] using hneg
  have hc : CuspOrbits.conj H s⁻¹ ⟦d⟧ = ⟦⟨∞, (Fact.out : IsCusp ∞ H')⟩⟧ := by
    simp only [CuspOrbits.conj_mk, show s⁻¹ • (d : OnePoint ℝ) = ∞ from inv_smul_eq_iff.mpr hg]
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  let := Fintype.ofFinite (H' ⧸ G'.subgroupOf H')
  rw [← cuspOrderFiber_translate hGH f ⟦d⟧ s, hc,
    cuspOrderFiber_infty_eq_sum_quotientFunc hle hneg' (ModularForm.translate f s),
    ← (conjugateCosets G H s).sum_comp _, orderAtCuspOrbit_mk,
    orderAtCusp_eq H _ d.property _ s hg.symm]
  simp only [quotientFunc_conjugateCosets f s]
  exact congrArg _ (sum_orderAtInfty_slash_quotientFunc_eq_norm f g)

/-- Norm preserves total cusp order when the smaller level contains `-1`. -/
lemma totalCuspOrder_eq_norm {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [H.IsArithmetic]
    [H.HasDetOne] (hGH : G ≤ H) (hneg : -1 ∈ G) {k : ℤ} (f : ModularForm G k) :
    totalCuspOrder G k f = totalCuspOrder H (k * Nat.card (H ⧸ G.subgroupOf H))
      (ModularForm.norm H f) := by
  let := Fintype.ofFinite (CuspOrbits H)
  rw [← sum_cuspOrderFiber hGH, totalCuspOrder]
  exact Finset.sum_congr rfl fun c _ ↦ cuspOrderFiber_eq_orderAtCuspOrbit_norm hGH hneg f c

/-- Adjoining `-1` multiplies total cusp order by at least the degree of the norm.
The map on cusp orbits is a bijection, and the extra norm factors differ only by signs. -/
lemma relIndex_mul_totalCuspOrder_le_norm_adjoinNegOne
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic]
    {k : ℤ} (f : ModularForm G k) :
    (G.relIndex G.adjoinNegOne : EReal) * totalCuspOrder G k f ≤
      totalCuspOrder G.adjoinNegOne (k * Nat.card (G.adjoinNegOne ⧸ G.subgroupOf G.adjoinNegOne))
        (ModularForm.norm G.adjoinNegOne f) := by
  let := Fintype.ofFinite (CuspOrbits G)
  let := Fintype.ofFinite (CuspOrbits G.adjoinNegOne)
  rw [totalCuspOrder, ← EReal.coe_natCast,
    EReal.mul_sum_of_nonneg_of_ne_top (by positivity) (by simp)]
  refine (Finset.sum_le_sum fun c _ ↦ ?_).trans_eq <|
    Fintype.sum_bijective _ (CuspOrbits.map_adjoinNegOne_bijective G) _ _ fun _ ↦ rfl
  induction c using Quotient.inductionOn with | h d =>
  obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp ((IsArithmetic.isCusp_iff_isCusp_SL2Z G).mp d.property)
  have hq (q : G.adjoinNegOne ⧸ G.subgroupOf G.adjoinNegOne) :
      orderAtInfty (SlashInvariantForm.quotientFunc f q ∣[k] mapGL ℝ g) =
        orderAtInfty ((f : ℍ → ℂ) ∣[k] mapGL ℝ g) := by
    induction q using Quotient.inductionOn with | h r =>
    rw [SlashInvariantForm.quotientFunc_mk]
    rcases G.adjoinNegOne.inv_mem r.property with h | h
    · rw [SlashInvariantFormClass.slash_action_eq f _ h]
    · rw [← neg_neg ((r : GL (Fin 2) ℝ)⁻¹), ← SlashAction.slash_mul, neg_mul,
        orderAtInfty_slash_neg, SlashAction.slash_mul,
        SlashInvariantFormClass.slash_action_eq f _ h]
  have hnorm := sum_orderAtInfty_slash_quotientFunc_eq_norm (H := G.adjoinNegOne) f g
  simp only [hq, Finset.sum_const, Finset.card_univ, EReal.nsmul_eq_mul,
    ← Nat.card_eq_fintype_card] at hnorm
  rw [orderAtCuspOrbit_mk, CuspOrbits.map_mk, orderAtCuspOrbit_mk,
    orderAtCusp_eq G k d.property f _ hg.symm,
    orderAtCusp_eq G.adjoinNegOne _ (d.property.mono G.le_adjoinNegOne) _ _ hg.symm, mul_left_comm]
  simp only [widthInfty, adjoinNegOne_conj, adjoinNegOne_eq_self_iff.mpr G.neg_one_mem_adjoinNegOne]
  exact mul_le_mul_of_nonneg_left hnorm.le (EReal.coe_nonneg.mpr (strictWidthInfty_nonneg _))

end UpperHalfPlane
