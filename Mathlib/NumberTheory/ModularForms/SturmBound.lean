/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.OrderAtInfty
public import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Sturm bounds

For a subgroup `G` of `GL(2, ℝ)`, let `G' = G.adjoinNegOne` and `G'' = G' ⊓ SL(2, ℤ)`,
where `SL(2, ℤ)` is viewed as a subgroup of `GL(2, ℝ)`.

* `Subgroup.ratProjIndex`: the rational ratio `[SL(2, ℤ) : G''] / [G' : G'']`.
* `Subgroup.sturmBound`: the bound `k * G.ratProjIndex / (12 * G.widthInfty)` on the
  normalized order at infinity of a nonzero modular form of level `G` and weight `k`.

For arithmetic inclusions `G ≤ H`, we compare the defects of a form and its norm to `H`,
counting the norm factors represented by signed translations. This accounts for both cusp
widths and the projective index, without requiring either group to contain `-1` or have
determinant one. Specializing the target to `SL(2, ℤ)` proves the bound for its finite-index
subgroups.

For general arithmetic groups of determinant one, we restrict to the intersection with
`SL(2, ℤ)` and apply a simultaneous cusp bound. The cycles of a cusp translation on the finite
coset space give the cusps above infinity; their lengths determine the cusp widths and sum
to the relative index. Thus the total contribution above infinity scales by the same degree
as the global Sturm budget. The final result is `sturmBoundTheorem_arithmetic`.

For a Sturm bound allowing determinant `-1`, the proposed normalization is the bound of the
determinant-one subgroup `G⁺`, rather than `G` itself: adjoining orientation-reversing elements
can halve `ratProjIndex` without changing the order of vanishing. The norm comparison below
uses the present normalization and is valid for either determinant.
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

/-- The Sturm bound on the normalized order at infinity of modular forms of level `G`
and weight `k`. -/
noncomputable def sturmBound (G : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) : ℝ :=
  k * G.ratProjIndex / (12 * G.widthInfty)

lemma sturmBoundSL2Z (k : ℤ) : sturmBound 𝒮ℒ k = k / 12 := by
  have hindex : ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).ratProjIndex =
      ((⊤ : Subgroup SL(2, ℤ)).adjoinNegOne.index : ℚ) := ratProjIndex_coe ⊤
  rw [← MonoidHom.range_eq_map, adjoinNegOne_eq_self_iff.mpr (by simp), index_top] at hindex
  have hneg : (-1 : GL (Fin 2) ℝ) ∈ 𝒮ℒ := by
    exact ⟨-1, by ext i j; simp [mapGL_coe_matrix]⟩
  simp [sturmBound, widthInfty, adjoinNegOne_eq_self_iff.mpr hneg,
    strictWidthInfty_SL2Z, hindex]

/-- The cusp width times the difference between the Sturm bound and the order at infinity.
For arithmetic `G`, the zero form has defect `-∞`; the Sturm bound asserts that every nonzero
form has nonnegative defect. -/
private noncomputable def sturmDefect (G : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (f : ModularForm G k) : EReal :=
  G.widthInfty * ((sturmBound G k : EReal) - orderAtInfty f)

private lemma sturmDefect_nonneg_iff {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] {k : ℤ}
    (f : ModularForm G k) : 0 ≤ sturmDefect G k f ↔ orderAtInfty f ≤ sturmBound G k := by
  have hw : (0 : EReal) < G.widthInfty := EReal.coe_pos.mpr G.widthInfty_pos
  rw [sturmDefect, EReal.mul_nonneg_iff]
  simp only [hw.le, hw.not_ge, true_and, false_and, or_false]
  exact EReal.sub_nonneg (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))

private def SturmBoundTheorem (G : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) : Prop :=
  ∀ f : ModularForm G k, f ≠ 0 → 0 ≤ sturmDefect G k f

private lemma sturmBoundTheorem_iff (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] (k : ℤ) :
    SturmBoundTheorem G k ↔ ∀ f : ModularForm G k,
      (sturmBound G k : EReal) < orderAtInfty f → f = 0 := by
  simp only [SturmBoundTheorem, sturmDefect_nonneg_iff]
  constructor
  · intro h f hf
    by_contra hne
    exact (h f hne).not_gt hf
  · intro h f hne
    exact le_of_not_gt fun hf ↦ hne (h f hf)

private lemma sturmBoundTheoremSL2Z (k : ℤ) : SturmBoundTheorem 𝒮ℒ k := by
  rw [sturmBoundTheorem_iff]
  intro f hf
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
  have hkcast : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  simpa only [hkcast, Nat.cast_ofNat] using (Nat.cast_div_le (α := ℝ) (m := k.toNat) (n := 12))

local instance arithmeticIsFiniteRelIndex (G H : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [H.IsArithmetic] : G.IsFiniteRelIndex H :=
  (IsArithmetic.is_commensurable.trans
    (IsArithmetic.is_commensurable (𝒢 := H)).symm).1

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
  refine ⟨m.toNat, by omega, ?_⟩
  have hmcast : (m.toNat : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hmpos.le
  rw [hmcast]
  exact hm.symm

/-- Translations by multiples of the larger group's width give distinct cosets. -/
private lemma translationCosets_injective (G H : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [H.IsArithmetic] {n : ℕ}
    (hw : G.strictWidthInfty = n * H.strictWidthInfty) :
    Function.Injective (fun i : Fin n ↦ (⟦translation H i⟧ : H ⧸ G.subgroupOf H)) := by
  intro i j hij
  rw [QuotientGroup.eq] at hij
  have hmem : (translation H i : GL (Fin 2) ℝ)⁻¹ * translation H j ∈ G := hij
  dsimp only [translation] at hmem
  rw [← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul] at hmem
  have hp : -((i : ℝ) * H.strictWidthInfty) + j * H.strictWidthInfty ∈ G.strictPeriods :=
    G.mem_strictPeriods_iff.mpr hmem
  rw [strictPeriods_eq_zmultiples_strictWidthInfty, hw] at hp
  obtain ⟨m, hm⟩ := hp
  simp only [zsmul_eq_mul] at hm
  have hmreal : (m : ℝ) * n = -(i : ℝ) + j := by
    apply mul_right_cancel₀ H.strictWidthInfty_pos.ne'
    linear_combination hm
  have hm' : m * (n : ℤ) = -(i : ℤ) + j := by exact_mod_cast hmreal
  apply Fin.ext
  have hi : (i : ℤ) < n := by exact_mod_cast i.isLt
  have hj : (j : ℤ) < n := by exact_mod_cast j.isLt
  have hmod : Int.ModEq n (i : ℤ) j := Int.modEq_iff_dvd.mpr ⟨m, by linarith⟩
  have hij' : (i : ℤ) = j := by
    simpa [Int.ModEq, Int.emod_eq_of_lt (by positivity) hi,
      Int.emod_eq_of_lt (by positivity) hj] using hmod
  exact_mod_cast hij'

private lemma translation_pow (H : Subgroup (GL (Fin 2) ℝ)) (n : ℕ) :
    translation H 1 ^ n = translation H n := by
  apply Subtype.ext
  simp only [translation, coe_pow, Int.cast_one, one_mul, Int.cast_natCast]
  rw [← AddChar.map_nsmul_eq_pow]
  simp only [nsmul_eq_mul]
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
  have hiff (m : ℕ) : Function.IsPeriodicPt
      (fun q : H ⧸ K.subgroupOf H ↦ translation H 1 • q) m ⟦r⟧ ↔ n ∣ m := by
    rw [translation_isPeriodicPt_iff]
    simp only [translation, Int.cast_natCast]
    rw [← mem_strictPeriods_iff, strictPeriods_eq_zmultiples_strictWidthInfty, hw]
    constructor
    · rintro ⟨a, ha⟩
      simp only [zsmul_eq_mul] at ha
      have ha' : (a : ℝ) * n = m := by
        apply mul_right_cancel₀ H.strictWidthInfty_pos.ne'
        simpa only [mul_assoc] using ha
      have hint : (m : ℤ) = (n : ℤ) * a := by
        exact_mod_cast (by linarith : (m : ℝ) = n * a)
      exact Int.natCast_dvd_natCast.mp ⟨a, hint⟩
    · rintro ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      simp only [zsmul_eq_mul, Nat.cast_mul, Int.cast_natCast]
      ring
  exact Nat.dvd_antisymm
    (Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ((hiff n).mpr dvd_rfl))
    ((hiff _).mp (Function.isPeriodicPt_minimalPeriod _ _))

/-- Conjugation by an element of an arithmetic group preserves arithmeticity. -/
private lemma isArithmetic_conj_of_mem {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] (r : H) :
    (ConjAct.toConjAct (r : GL (Fin 2) ℝ) • K).IsArithmetic := by
  have hKH : K.Commensurable H := IsArithmetic.is_commensurable.trans
    (IsArithmetic.is_commensurable (𝒢 := H)).symm
  have hc : (ConjAct.toConjAct (r : GL (Fin 2) ℝ) • K).Commensurable H := by
    simpa only [conjAct_pointwise_smul_eq_self (H.le_normalizer r.property)] using
      hKH.smul (ConjAct.toConjAct (r : GL (Fin 2) ℝ))
  exact ⟨hc.trans IsArithmetic.is_commensurable⟩

/-- The cycles of the translation by the strict width of the larger group. -/
private abbrev translationCycles (K H : Subgroup (GL (Fin 2) ℝ)) :=
  MulAction.orbitRel.Quotient (zpowers (translation H 1)) (H ⧸ K.subgroupOf H)

/-- The class formula for the translation action gives the sum of cusp widths in the fiber.
The orbit representatives are read as inverse scaling matrices. -/
private lemma sum_strictWidthInfty_translationCycles {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] (hKH : K ≤ H) :
    let := Fintype.ofFinite (translationCycles K H)
    ∑ c : translationCycles K H,
        (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).strictWidthInfty =
      K.relIndex H * H.strictWidthInfty := by
  classical
  let := Fintype.ofFinite (translationCycles K H)
  dsimp only
  have hc (c : translationCycles K H) :
      (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).strictWidthInfty =
        Function.minimalPeriod (fun q : H ⧸ K.subgroupOf H ↦ translation H 1 • q) c.out *
          H.strictWidthInfty := by
    have : (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).IsArithmetic :=
      isArithmetic_conj_of_mem c.out.out
    have hle : ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K ≤ H := by
      simpa only [conjAct_pointwise_smul_eq_self (H.le_normalizer c.out.out.property)] using
        (pointwise_smul_le_pointwise_smul_iff
          (a := ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ))).mpr hKH
    obtain ⟨n, hn, hw⟩ : ∃ n : ℕ, 0 < n ∧
        (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).strictWidthInfty =
          n * H.strictWidthInfty := strictWidthInfty_eq_nat_mul hle
    have hp : Function.minimalPeriod
        (fun q : H ⧸ K.subgroupOf H ↦ translation H 1 • q) c.out = n := by
      simpa only [Quotient.out_eq] using minimalPeriod_translation c.out.out hw
    rw [hp, hw]
  simp only [hc, ← Finset.sum_mul, ← Nat.cast_sum,
    ← index_eq_sum_minimalPeriod (K.subgroupOf H) (translation H 1)]
  rfl

private lemma translation_zpow (H : Subgroup (GL (Fin 2) ℝ)) (m : ℤ) :
    translation H 1 ^ m = translation H m := by
  apply Subtype.ext
  simp only [translation, coe_zpow, Int.cast_one, one_mul]
  rw [← AddChar.map_zsmul_eq_zpow]
  simp only [zsmul_eq_mul]

private lemma exists_translation_or_neg_of_fixing_infty
    {H : Subgroup (GL (Fin 2) ℝ)} [H.IsArithmetic] [H.HasDetOne]
    (hneg : (-1 : GL (Fin 2) ℝ) ∈ H) (g : H) (hg : (g : GL (Fin 2) ℝ) • ∞ = (∞ : OnePoint ℝ)) :
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

/-- The cusp belonging to a translation cycle of the finite coset space. -/
private noncomputable def translationCycleCusp (K H : Subgroup (GL (Fin 2) ℝ))
    [K.IsArithmetic] [H.IsArithmetic] (c : translationCycles K H) : CuspOrbits K :=
  ⟦⟨(c.out.out : GL (Fin 2) ℝ)⁻¹ • ∞,
    ((show IsCusp ∞ H from Fact.out).smul_of_mem
      (H.inv_mem c.out.out.property)).of_isFiniteRelIndex⟩⟧

/-- With `-1` in the smaller level, distinct translation cycles give inequivalent cusps. -/
private lemma translationCycleCusp_injective {K H : Subgroup (GL (Fin 2) ℝ)}
    [K.IsArithmetic] [H.IsArithmetic] [H.HasDetOne] (hKH : K ≤ H)
    (hneg : (-1 : GL (Fin 2) ℝ) ∈ K) :
    Function.Injective (translationCycleCusp K H) := by
  intro c d hcd
  obtain ⟨a, ha⟩ := Quotient.eq.mp hcd
  have ha' : (a : GL (Fin 2) ℝ) • ((d.out.out : GL (Fin 2) ℝ)⁻¹ • (∞ : OnePoint ℝ)) =
      (c.out.out : GL (Fin 2) ℝ)⁻¹ • ∞ := congrArg Subtype.val ha
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
        simpa only [b, coe_mul, coe_inv, neg_neg] using congrArg Neg.neg hm.symm
      rw [heq]
      simpa only [mul_inv_rev, inv_inv, inv_neg, neg_mul, mul_neg, mul_assoc,
        inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel_right, inv_mul_cancel,
        mul_one, one_mul, neg_one_mul] using K.mul_mem hneg (K.inv_mem a.property)
  rw [← Quotient.out_eq c, ← Quotient.out_eq d]
  exact Quotient.eq.mpr ⟨⟨_, mem_zpowers_iff.mpr ⟨m, rfl⟩⟩, hcos⟩

/-- Every factor of the norm is bounded at infinity, for any arithmetic target group. -/
private lemma quotientFunc_bounded {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] {k : ℤ} (f : ModularForm G k)
    (q : H ⧸ G.subgroupOf H) :
    IsBoundedAtImInfty (SlashInvariantForm.quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h g =>
    have hc : IsCusp ∞ (ConjAct.toConjAct (g : GL (Fin 2) ℝ) • G) :=
      (show IsCusp ∞ H from Fact.out).of_isFiniteRelIndex_conj (𝒢 := G) g.property
    let : Fact (IsCusp ∞
        (ConjAct.toConjAct (g : GL (Fin 2) ℝ)⁻¹⁻¹ • G)) := ⟨by simpa using hc⟩
    exact ModularFormClass.bdd_at_infty (ModularForm.translate f (g : GL (Fin 2) ℝ)⁻¹)

/-- The cusp of a factor in the norm to level one. -/
private noncomputable def normCusp (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] :
    (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ) → CuspOrbits G :=
  Quotient.lift (fun g ↦ ⟦⟨(g : GL (Fin 2) ℝ)⁻¹ • ∞,
    (IsArithmetic.isCusp_iff_isCusp_SL2Z G).mpr
      ((show IsCusp ∞ 𝒮ℒ from Fact.out).smul_of_mem
        ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).inv_mem g.property))⟩⟧)
    (fun a b hab ↦ by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hab
      have hmem : (a : GL (Fin 2) ℝ)⁻¹ * b ∈ G := by
        simpa only [mem_subgroupOf, coe_mul, coe_inv] using hab
      refine Quotient.eq.mpr ⟨(⟨_, hmem⟩ : G), ?_⟩
      apply Subtype.ext
      exact show ((a : GL (Fin 2) ℝ)⁻¹ * b) •
          ((b : GL (Fin 2) ℝ)⁻¹ • (∞ : OnePoint ℝ)) = (a : GL (Fin 2) ℝ)⁻¹ • ∞ from by
        simp only [mul_smul, smul_inv_smul])

/-- The contribution of one cusp to the order of the norm to level one.
This is expressed as a sum over the cosets in the cusp fiber, so it does not require choosing
scaling matrices or a system of cusp representatives. -/
private noncomputable def normCuspOrder {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic]
    {k : ℤ} (f : ModularForm G k) (c : CuspOrbits G) : EReal := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)
  exact ∑ q with normCusp G q = c, orderAtInfty (SlashInvariantForm.quotientFunc f q)

private lemma normCuspOrder_nonneg {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic]
    {k : ℤ} (f : ModularForm G k) (c : CuspOrbits G) : 0 ≤ normCuspOrder f c := by
  classical
  apply Finset.sum_nonneg
  intro q hq
  exact (quotientFunc_bounded f q).orderAtInfty_nonneg

/-- Grouping the factors of the norm by cusp counts each factor exactly once. -/
private lemma sum_normCuspOrder {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic]
    {k : ℤ} (f : ModularForm G k) :
    let := Fintype.ofFinite (CuspOrbits G)
    let := Fintype.ofFinite (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)
    ∑ c, normCuspOrder f c =
      ∑ q : 𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ, orderAtInfty (SlashInvariantForm.quotientFunc f q) := by
  classical
  let := Fintype.ofFinite (CuspOrbits G)
  let := Fintype.ofFinite (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)
  exact Finset.sum_fiberwise Finset.univ (normCusp G)
    (fun q ↦ orderAtInfty (SlashInvariantForm.quotientFunc f q))

/-- The simultaneous cusp bound supplied by the norm. This holds for every arithmetic level,
with the ordinary relative index in the bound. -/
private lemma sum_normCuspOrder_le {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic]
    {k : ℤ} (f : ModularForm G k) (hf : f ≠ 0) :
    let := Fintype.ofFinite (CuspOrbits G)
    ∑ c, normCuspOrder f c ≤ ((k * (G.relIndex 𝒮ℒ : ℝ) / 12 : ℝ) : EReal) := by
  classical
  let := Fintype.ofFinite (CuspOrbits G)
  let := Fintype.ofFinite (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)
  dsimp only
  rw [sum_normCuspOrder]
  have hnorm : orderAtInfty (ModularForm.norm 𝒮ℒ f) ≤
      sturmBound 𝒮ℒ (k * G.relIndex 𝒮ℒ) :=
    (sturmDefect_nonneg_iff _).mp
      (sturmBoundTheoremSL2Z _ _ (ModularForm.norm_ne_zero 𝒮ℒ (by simpa using hf)))
  rw [sturmBoundSL2Z] at hnorm
  have hprod : (∑ q : 𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ,
      orderAtInfty (SlashInvariantForm.quotientFunc f q)) ≤
      orderAtInfty (ModularForm.norm 𝒮ℒ f) := by
    simpa only [ModularForm.coe_norm, Finset.prod_fn] using
      orderAtInfty_prod Finset.univ (SlashInvariantForm.quotientFunc f)
  simpa only [Int.cast_mul, Int.cast_natCast] using hprod.trans hnorm

/-- The simultaneous bound also applies to any chosen subset of cusps. -/
private lemma sum_normCuspOrder_subset_le {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic]
    {k : ℤ} (f : ModularForm G k) (hf : f ≠ 0) (S : Finset (CuspOrbits G)) :
    ∑ c ∈ S, normCuspOrder f c ≤ ((k * (G.relIndex 𝒮ℒ : ℝ) / 12 : ℝ) : EReal) := by
  classical
  let := Fintype.ofFinite (CuspOrbits G)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun c _ _ ↦ normCuspOrder_nonneg f c)).trans (sum_normCuspOrder_le f hf)

/-- The factors represented by translations have the same order as the original form. -/
private lemma quotientFunc_translation_order {G H : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} (f : ModularForm G k) (m : ℤ) :
    orderAtInfty (SlashInvariantForm.quotientFunc f
      (⟦translation H m⟧ : H ⧸ G.subgroupOf H)) = orderAtInfty f := by
  rw [SlashInvariantForm.quotientFunc_mk]
  have heq : (f : ℍ → ℂ) ∣[k] (translation H m : GL (Fin 2) ℝ)⁻¹ =
      fun τ ↦ f (-(m * H.strictWidthInfty) +ᵥ τ) := by
    dsimp only [translation]
    rw [← AddChar.map_neg_eq_inv]
    ext τ
    have ha : Matrix.GeneralLinearGroup.upperRightHom (-(m * H.strictWidthInfty)) • τ =
        -(m * H.strictWidthInfty) +ᵥ τ := by
      ext
      simp [σ, num, denom, coe_vadd, coe_smul, add_comm]
    rw [ModularForm.slash_apply, ha]
    simp [σ, denom]
  rw [heq, orderAtInfty_vadd]

/-- Adjoining `-1` preserves inclusion. -/
private lemma adjoinNegOne_mono {G H : Subgroup (GL (Fin 2) ℝ)} (h : G ≤ H) :
    G.adjoinNegOne ≤ H.adjoinNegOne := by
  intro g hg
  exact hg.imp (fun hx ↦ h hx) (fun hx ↦ h hx)

/-- A representative in `H` of a translation in its projective image. -/
private noncomputable def signedTranslation (H : Subgroup (GL (Fin 2) ℝ)) (m : ℤ) : H := by
  classical
  let t := translation H.adjoinNegOne m
  exact if ht : (t : GL (Fin 2) ℝ) ∈ H then ⟨t, ht⟩ else
    ⟨-t, t.property.resolve_left ht⟩

private lemma signedTranslation_eq (H : Subgroup (GL (Fin 2) ℝ)) (m : ℤ) :
    (signedTranslation H m : GL (Fin 2) ℝ) = translation H.adjoinNegOne m ∨
      (signedTranslation H m : GL (Fin 2) ℝ) = -translation H.adjoinNegOne m := by
  classical
  dsimp only [signedTranslation]
  split_ifs <;> simp

private lemma quotientFunc_signedTranslation_order {G H : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} (f : ModularForm G k) (m : ℤ) :
    orderAtInfty (SlashInvariantForm.quotientFunc f
      (⟦signedTranslation H m⟧ : H ⧸ G.subgroupOf H)) = orderAtInfty f := by
  rw [SlashInvariantForm.quotientFunc_mk]
  rcases signedTranslation_eq H m with h | h <;> rw [h]
  · exact quotientFunc_translation_order f m
  · rw [inv_neg, orderAtInfty_slash_neg]
    exact quotientFunc_translation_order f m

/-- Equality of signed translation cosets implies equality of their translation parameters. -/
private lemma signedTranslation_index_eq {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] {n : ℕ}
    (hw : G.widthInfty = n * H.widthInfty) (i j : Fin n)
    {a b : GL (Fin 2) ℝ}
    (ha : a = signedTranslation H i ∨ a = -signedTranslation H i)
    (hb : b = signedTranslation H j ∨ b = -signedTranslation H j)
    (hab : a⁻¹ * b ∈ G) : i = j := by
  apply translationCosets_injective G.adjoinNegOne H.adjoinNegOne hw
  rw [QuotientGroup.eq]
  simp only [mem_subgroupOf, coe_mul, coe_inv]
  rcases signedTranslation_eq H i with hi | hi <;>
    rcases signedTranslation_eq H j with hj | hj <;>
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [hi, hj, inv_neg, neg_mul, mul_neg, neg_neg] at hab <;>
    first | exact Or.inl hab | exact Or.inr hab

/-- The normalized order at a cusp is bounded by the contribution of that cusp to the norm.
This is the local input to the simultaneous cusp bound. -/
private lemma width_mul_orderAtInfty_slash_le_normCuspOrder
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] (hG : G ≤ 𝒮ℒ)
    {k : ℤ} (f : ModularForm G k) (g : 𝒮ℒ) :
    (ConjAct.toConjAct (g : GL (Fin 2) ℝ)⁻¹ • G).widthInfty *
        orderAtInfty ((f : ℍ → ℂ) ∣[k] (g : GL (Fin 2) ℝ)) ≤
      normCuspOrder f (normCusp G (⟦g⁻¹⟧ : 𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)) := by
  classical
  let K := ConjAct.toConjAct (g : GL (Fin 2) ℝ)⁻¹ • G
  have : K.IsArithmetic := isArithmetic_conj_of_mem g⁻¹
  have hK : K ≤ 𝒮ℒ := by
    dsimp only [K]
    simpa only [conjAct_pointwise_smul_eq_self
      ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).le_normalizer
        ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).inv_mem g.property))]
      using (pointwise_smul_le_pointwise_smul_iff (a := ConjAct.toConjAct
        (g : GL (Fin 2) ℝ)⁻¹)).mpr hG
  have hnegSL : (-1 : GL (Fin 2) ℝ) ∈ 𝒮ℒ := by
    exact ⟨-1, by ext i j; simp [mapGL_coe_matrix]⟩
  obtain ⟨n, hn, hw⟩ : ∃ n : ℕ, 0 < n ∧ K.widthInfty = n * (𝒮ℒ :
      Subgroup (GL (Fin 2) ℝ)).widthInfty :=
    strictWidthInfty_eq_nat_mul (adjoinNegOne_mono hK)
  let e : Fin n ↪ (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ) :=
    ⟨fun i ↦ ⟦signedTranslation 𝒮ℒ i * g⁻¹⟧, by
      intro i j hij
      rw [QuotientGroup.eq] at hij
      have hmem : (signedTranslation 𝒮ℒ i : GL (Fin 2) ℝ)⁻¹ *
          signedTranslation 𝒮ℒ j ∈ K := by
        rw [mem_pointwise_smul_iff_inv_smul_mem]
        simpa only [mem_subgroupOf, ConjAct.smul_def, ConjAct.ofConjAct_inv,
          ConjAct.ofConjAct_toConjAct, inv_inv, mul_inv_rev, coe_mul, coe_inv, mul_assoc]
          using hij
      exact signedTranslation_index_eq hw i j (Or.inl rfl) (Or.inl rfl) hmem⟩
  have he (i : Fin n) : orderAtInfty (SlashInvariantForm.quotientFunc f (e i)) =
      orderAtInfty ((f : ℍ → ℂ) ∣[k] (g : GL (Fin 2) ℝ)) := by
    rw [show e i = ⟦signedTranslation 𝒮ℒ i * g⁻¹⟧ from rfl,
      SlashInvariantForm.quotientFunc_mk]
    simp only [mul_inv_rev, inv_inv, coe_mul, coe_inv, SlashAction.slash_mul]
    exact quotientFunc_signedTranslation_order (ModularForm.translate f (g : GL (Fin 2) ℝ)) i
  have hc (i : Fin n) : normCusp G (e i) = normCusp G (⟦g⁻¹⟧ :
      𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ) := by
    rw [show e i = ⟦signedTranslation 𝒮ℒ i * g⁻¹⟧ from rfl]
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    have ht : (signedTranslation 𝒮ℒ i : GL (Fin 2) ℝ)⁻¹ • (∞ : OnePoint ℝ) = ∞ := by
      rcases signedTranslation_eq 𝒮ℒ i with h | h <;>
        simp [h, translation, OnePoint.smul_infty_eq_ite]
    simp only [coe_mul, coe_inv, mul_inv_rev, inv_inv, mul_smul, ht]
  let := Fintype.ofFinite (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)
  have hsubset : Finset.univ.map e ⊆ Finset.univ.filter (fun q ↦
      normCusp G q = normCusp G (⟦g⁻¹⟧ : 𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)) := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc i⟩
  have hs : ∑ q ∈ Finset.univ.map e, orderAtInfty (SlashInvariantForm.quotientFunc f q) ≤
      normCuspOrder f (normCusp G (⟦g⁻¹⟧ : 𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q _ _ ↦ (quotientFunc_bounded f q).orderAtInfty_nonneg)
  have hwSL : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).widthInfty = 1 := by
    rw [widthInfty, adjoinNegOne_eq_self_iff.mpr hnegSL, strictWidthInfty_SL2Z]
  have hw' : (ConjAct.toConjAct (g : GL (Fin 2) ℝ)⁻¹ • G).widthInfty = (n : ℝ) := by
    simpa only [hwSL, mul_one] using hw
  simpa only [Finset.sum_map, he, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, EReal.nsmul_eq_mul, hw', EReal.coe_natCast] using hs

/-- Simultaneous Sturm bound at any finite family of inequivalent cusps of a level contained
in `SL(2, ℤ)`. Each cusp is weighted by its width in the chosen coordinate. -/
private lemma sum_width_mul_orderAtInfty_slash_le
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] (hG : G ≤ 𝒮ℒ)
    {k : ℤ} (f : ModularForm G k) (hf : f ≠ 0) {ι : Type*} [Fintype ι]
    (g : ι → 𝒮ℒ)
    (hg : Function.Injective (fun i ↦ normCusp G
      (⟦(g i)⁻¹⟧ : 𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ))) :
    ∑ i, (ConjAct.toConjAct (g i : GL (Fin 2) ℝ)⁻¹ • G).widthInfty *
        orderAtInfty ((f : ℍ → ℂ) ∣[k] (g i : GL (Fin 2) ℝ)) ≤
      ((k * (G.relIndex 𝒮ℒ : ℝ) / 12 : ℝ) : EReal) := by
  classical
  let e : ι ↪ CuspOrbits G := ⟨_, hg⟩
  have hs : ∑ i, (ConjAct.toConjAct (g i : GL (Fin 2) ℝ)⁻¹ • G).widthInfty *
        orderAtInfty ((f : ℍ → ℂ) ∣[k] (g i : GL (Fin 2) ℝ)) ≤
      ∑ i, normCuspOrder f (e i) :=
    Finset.sum_le_sum fun i _ ↦ width_mul_orderAtInfty_slash_le_normCuspOrder hG f (g i)
  have hbound : ∑ i, normCuspOrder f (e i) ≤
      ((k * (G.relIndex 𝒮ℒ : ℝ) / 12 : ℝ) : EReal) := by
    simpa only [Finset.sum_map] using sum_normCuspOrder_subset_le f hf (Finset.univ.map e)
  exact hs.trans hbound

/-- With `-1` in the level, the simultaneous cusp bound has precisely the projective
normalization used by `sturmDefect`. -/
private lemma sum_width_mul_orderAtInfty_slash_le_projective
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] (hG : G ≤ 𝒮ℒ)
    (hneg : (-1 : GL (Fin 2) ℝ) ∈ G) {k : ℤ}
    (f : ModularForm G k) (hf : f ≠ 0) {ι : Type*} [Fintype ι] (g : ι → 𝒮ℒ)
    (hg : Function.Injective (fun i ↦ normCusp G
      (⟦(g i)⁻¹⟧ : 𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ))) :
    ∑ i, (ConjAct.toConjAct (g i : GL (Fin 2) ℝ)⁻¹ • G).widthInfty *
        orderAtInfty ((f : ℍ → ℂ) ∣[k] (g i : GL (Fin 2) ℝ)) ≤
      ((G.widthInfty * sturmBound G k : ℝ) : EReal) := by
  have hrat : (G.ratProjIndex : ℝ) = G.relIndex 𝒮ℒ := by
    simp [ratProjIndex, adjoinNegOne_eq_self_iff.mpr hneg, relIndex_eq_one.mpr hG]
  have hbound : G.widthInfty * sturmBound G k = k * (G.relIndex 𝒮ℒ : ℝ) / 12 := by
    rw [sturmBound, hrat]
    field_simp [G.widthInfty_pos.ne']
  rw [hbound]
  exact sum_width_mul_orderAtInfty_slash_le hG f hf g hg

/-- Any collection of distinct norm factors having the original order gives an order bound. -/
private lemma card_mul_orderAtInfty_le_norm {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] {k : ℤ} (f : ModularForm G k)
    {ι : Type*} [Fintype ι] (e : ι ↪ (H ⧸ G.subgroupOf H))
    (he : ∀ i, orderAtInfty (SlashInvariantForm.quotientFunc f (e i)) = orderAtInfty f) :
    (Fintype.card ι : EReal) * orderAtInfty f ≤ orderAtInfty (ModularForm.norm H f) := by
  classical
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  have hs : (Fintype.card ι : EReal) * orderAtInfty f =
      ∑ i, orderAtInfty (SlashInvariantForm.quotientFunc f (e i)) := by
    simp [he, EReal.nsmul_eq_mul]
  rw [hs]
  have hsum : ∑ q ∈ Finset.univ.map e, orderAtInfty (SlashInvariantForm.quotientFunc f q) ≤
      ∑ q : H ⧸ G.subgroupOf H, orderAtInfty (SlashInvariantForm.quotientFunc f q) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (Finset.univ.map e))
      (fun q _ _ ↦ (quotientFunc_bounded f q).orderAtInfty_nonneg)
  simp only [Finset.sum_map] at hsum
  simpa only [ModularForm.coe_norm, Finset.prod_fn] using
    hsum.trans (orderAtInfty_prod Finset.univ (SlashInvariantForm.quotientFunc f))

private lemma width_mul_orderAtInfty_le_norm {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] {k : ℤ} (f : ModularForm G k) {n : ℕ}
    (hw : G.widthInfty = n * H.widthInfty) :
    (n : EReal) * orderAtInfty f ≤ orderAtInfty (ModularForm.norm H f) := by
  let e : Fin n ↪ (H ⧸ G.subgroupOf H) :=
    ⟨fun i ↦ ⟦signedTranslation H i⟧, by
      intro i j hij
      rw [QuotientGroup.eq] at hij
      exact signedTranslation_index_eq hw i j (Or.inl rfl) (Or.inl rfl) hij⟩
  simpa using card_mul_orderAtInfty_le_norm f e (fun i ↦ quotientFunc_signedTranslation_order f i)

private lemma two_width_mul_orderAtInfty_le_norm {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hG : -1 ∉ G) (hH : -1 ∈ H)
    {k : ℤ} (f : ModularForm G k) {n : ℕ} (hw : G.widthInfty = n * H.widthInfty) :
    ((2 * n : ℕ) : EReal) * orderAtInfty f ≤ orderAtInfty (ModularForm.norm H f) := by
  classical
  let t (i : Fin 2 × Fin n) : H :=
    if i.1 = 0 then signedTranslation H i.2 else
      ⟨-signedTranslation H i.2, by simpa using H.mul_mem hH (signedTranslation H i.2).property⟩
  have ht (i : Fin 2 × Fin n) : (t i : GL (Fin 2) ℝ) = signedTranslation H i.2 ∨
      (t i : GL (Fin 2) ℝ) = -signedTranslation H i.2 := by
    dsimp [t]; split_ifs <;> simp
  let e : (Fin 2 × Fin n) ↪ (H ⧸ G.subgroupOf H) := ⟨fun i ↦ ⟦t i⟧, by
    rintro ⟨a, i⟩ ⟨b, j⟩ hij
    rw [QuotientGroup.eq] at hij
    have hmem : (t (a, i) : GL (Fin 2) ℝ)⁻¹ * t (b, j) ∈ G := by
      simpa only [mem_subgroupOf, coe_mul, coe_inv] using hij
    have hidx : i = j := signedTranslation_index_eq hw i j (ht (a, i)) (ht (b, j)) hmem
    obtain rfl := hidx
    have hab : a = b := by
      fin_cases a <;> fin_cases b <;> try rfl
      all_goals exfalso; apply hG; simpa [t] using hmem
    subst b
    rfl⟩
  have he (i : Fin 2 × Fin n) :
      orderAtInfty (SlashInvariantForm.quotientFunc f (e i)) = orderAtInfty f := by
    have hei : e i = ⟦t i⟧ := rfl
    rw [hei, SlashInvariantForm.quotientFunc_mk]
    rcases ht i with h | h <;> rw [h]
    · exact quotientFunc_signedTranslation_order f i.2
    · rw [inv_neg, orderAtInfty_slash_neg]
      exact quotientFunc_signedTranslation_order f i.2
  simpa using card_mul_orderAtInfty_le_norm f e he

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
  have h₁' : (G.relIndex (H ⊓ 𝒮ℒ) : ℚ) * H.relIndex 𝒮ℒ = G.relIndex 𝒮ℒ := by
    exact_mod_cast h₁
  have h₂' : (G.relIndex (H ⊓ 𝒮ℒ) : ℚ) * (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex H =
      (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex G * G.relIndex H := by exact_mod_cast h₂
  have hn' : (G.relIndex (H ⊓ 𝒮ℒ) : ℚ) ≠ 0 := by exact_mod_cast hn
  field_simp [hGn, hHn]
  apply mul_left_cancel₀ hn'
  linear_combination (G.relIndex 𝒮ℒ : ℚ) * h₂' -
    ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).relIndex G : ℚ) * (G.relIndex H : ℚ) * h₁'

/-- Adjoining `-1` does not change the projective index. -/
private lemma ratProjIndex_adjoinNegOne (G : Subgroup (GL (Fin 2) ℝ)) :
    G.adjoinNegOne.ratProjIndex = G.ratProjIndex := by
  simp only [ratProjIndex, adjoinNegOne_eq_self_iff.mpr G.negOne_mem_adjoinNegOne]

/-- The projective index scales by the degree of the map of modular curves. -/
private lemma ratProjIndex_eq_projective_relIndex_mul {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hGH : G ≤ H) :
    G.ratProjIndex = G.adjoinNegOne.relIndex H.adjoinNegOne * H.ratProjIndex := by
  simpa only [ratProjIndex_adjoinNegOne] using
    ratProjIndex_eq_relIndex_mul (adjoinNegOne_mono hGH)
      G.negOne_mem_adjoinNegOne H.negOne_mem_adjoinNegOne

/-- Restriction preserves the function, but multiplies the global budget by the projective
degree and the contribution at infinity by the ratio of cusp widths. In particular, the
single-cusp defect does not simply scale by the degree. -/
private lemma sturmDefect_restrict {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hGH : G ≤ H) (k : ℤ)
    (f : ModularForm H k) (hf : f ≠ 0) :
    sturmDefect G k (ModularForm.restrict hGH f) =
      (G.adjoinNegOne.relIndex H.adjoinNegOne : ℝ) * sturmDefect H k f +
        ((G.adjoinNegOne.relIndex H.adjoinNegOne : ℝ) * H.widthInfty - G.widthInfty) *
          orderAtInfty f := by
  have htop : orderAtInfty f ≠ ⊤ := by
    intro h
    exact hf (DFunLike.coe_injective ((orderAtInfty_eq_top_iff_eq_zero H.strictWidthInfty_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f H.strictWidthInfty_mem_strictPeriods)
      f.holo' (ModularFormClass.bdd_at_infty f)).mp h))
  have hbot : orderAtInfty f ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (ModularFormClass.bdd_at_infty f).orderAtInfty_nonneg
  have hrat : (G.ratProjIndex : ℝ) =
      (G.adjoinNegOne.relIndex H.adjoinNegOne : ℝ) * H.ratProjIndex := by
    exact_mod_cast ratProjIndex_eq_projective_relIndex_mul hGH
  simp only [sturmDefect, ModularForm.coe_restrict]
  rw [← EReal.coe_toReal htop hbot]
  simp only [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  simp only [sturmBound, hrat]
  field_simp [G.widthInfty_pos.ne', H.widthInfty_pos.ne']
  ring

open scoped Classical in
/-- The extra multiplicity from the kernel of the action on the upper half plane. -/
private noncomputable def centralMultiplicity (G H : Subgroup (GL (Fin 2) ℝ)) : ℕ :=
  if -1 ∈ H ∧ -1 ∉ G then 2 else 1

/-- The ordinary index differs from the projective index by the central multiplicity. -/
private lemma ratProjIndex_mul_centralMultiplicity {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hGH : G ≤ H) :
    G.ratProjIndex * centralMultiplicity G H = G.relIndex H * H.ratProjIndex := by
  have hrat : G.ratProjIndex = G.adjoinNegOne.relIndex H.adjoinNegOne * H.ratProjIndex :=
    ratProjIndex_eq_projective_relIndex_mul hGH
  have ht : G.relIndex G.adjoinNegOne * G.adjoinNegOne.relIndex H.adjoinNegOne =
      G.relIndex H * H.relIndex H.adjoinNegOne :=
    (relIndex_mul_relIndex G G.adjoinNegOne H.adjoinNegOne G.le_adjoinNegOne
      (adjoinNegOne_mono hGH)).trans
      (relIndex_mul_relIndex G H H.adjoinNegOne hGH H.le_adjoinNegOne).symm
  have hidx : centralMultiplicity G H * G.adjoinNegOne.relIndex H.adjoinNegOne =
      G.relIndex H := by
    by_cases hH : -1 ∈ H
    · by_cases hG : -1 ∈ G
      · simp [centralMultiplicity, hG, hH, adjoinNegOne_eq_self_iff.mpr hG,
          adjoinNegOne_eq_self_iff.mpr hH]
      · simpa only [centralMultiplicity, hH, hG, not_false_eq_true, and_self,
          ↓reduceIte, relindex_adjoinNegOne_eq_two hG,
          adjoinNegOne_eq_self_iff.mpr hH, relIndex_self, mul_one] using ht
    · have hG : -1 ∉ G := fun h ↦ hH (hGH h)
      rw [relindex_adjoinNegOne_eq_two hG, relindex_adjoinNegOne_eq_two hH] at ht
      simp only [centralMultiplicity, hH, false_and, ↓reduceIte, one_mul]
      omega
  rw [hrat]
  have hidx' : (centralMultiplicity G H : ℚ) * G.adjoinNegOne.relIndex H.adjoinNegOne =
      G.relIndex H := by exact_mod_cast hidx
  linear_combination H.ratProjIndex * hidx'

/-- The norm comparison for arbitrary arithmetic inclusions. Weighting the defect by the
cusp width leaves only the central multiplicity: `1`, or `2` when `-1 ∈ H` but `-1 ∉ G`.

This comparison also allows determinant `-1`; the normalization of `sturmBound` itself must
be changed before asserting a Sturm bound for groups containing such elements. -/
private lemma sturmDefect_norm_le {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hGH : G ≤ H) (k : ℤ) (f : ModularForm G k) :
    sturmDefect H (k * G.relIndex H) (ModularForm.norm H f) ≤
      (centralMultiplicity G H : ℝ) * sturmDefect G k f := by
  classical
  obtain ⟨n, hn, hw⟩ : ∃ n : ℕ, 0 < n ∧ G.widthInfty = n * H.widthInfty :=
    strictWidthInfty_eq_nat_mul (adjoinNegOne_mono hGH)
  have horder : ((centralMultiplicity G H * n : ℕ) : EReal) * orderAtInfty f ≤
      orderAtInfty (ModularForm.norm H f) := by
    by_cases hc : -1 ∈ H ∧ -1 ∉ G
    · simpa [centralMultiplicity, hc] using two_width_mul_orderAtInfty_le_norm hc.2 hc.1 f hw
    · simpa [centralMultiplicity, hc] using width_mul_orderAtInfty_le_norm f hw
  have hrat : (G.ratProjIndex : ℝ) * centralMultiplicity G H =
      G.relIndex H * (H.ratProjIndex : ℝ) := by
    exact_mod_cast ratProjIndex_mul_centralMultiplicity hGH
  have hbound : H.widthInfty * H.sturmBound (k * G.relIndex H) =
      (centralMultiplicity G H : ℝ) * (G.widthInfty * G.sturmBound k) := by
    simp only [sturmBound, Int.cast_mul, Int.cast_natCast]
    rw [mul_assoc (k : ℝ), ← hrat]
    field_simp [G.widthInfty_pos.ne', H.widthInfty_pos.ne']
  have hweighted : (centralMultiplicity G H : ℝ) *
      (G.widthInfty * orderAtInfty f) ≤
      H.widthInfty * orderAtInfty (ModularForm.norm H f) := by
    convert mul_le_mul_of_nonneg_left horder
      (EReal.coe_nonneg.mpr H.widthInfty_nonneg) using 1
    simp only [hw, EReal.coe_mul, EReal.natCast_mul, EReal.coe_coe_eq_natCast]
    ac_rfl
  simp only [sturmDefect]
  rw [EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr H.widthInfty_nonneg)
    (EReal.coe_ne_top _),
    EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr G.widthInfty_nonneg)
      (EReal.coe_ne_top _),
    EReal.mul_sub_of_nonneg_of_ne_top (by positivity) (EReal.coe_ne_top _)]
  simp only [← EReal.coe_mul]
  rw [hbound]
  exact EReal.sub_le_sub le_rfl hweighted

/-- Multiplication by a positive real number preserves strict inequalities in `EReal`. -/
private lemma coe_mul_lt_mul {a b : EReal} {c : ℝ} (hc : 0 < c) (hab : a < b) :
    (c : EReal) * a < (c : EReal) * b := by
  refine (mul_le_mul_of_nonneg_left hab.le (EReal.coe_nonneg.mpr hc.le)).lt_of_ne ?_
  intro heq
  apply hab.ne
  have hinv : (c⁻¹ : ℝ) * ((c : EReal) * a) = (c⁻¹ : ℝ) * ((c : EReal) * b) :=
    congrArg (fun x : EReal ↦ (c⁻¹ : ℝ) * x) heq
  simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one,
    one_mul] using hinv

/-- A Sturm bound for an arithmetic group implies the bound for each arithmetic subgroup. -/
private lemma sturmBoundTheorem_of_norm {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [H.IsArithmetic] (hGH : G ≤ H) (k : ℤ)
    (hH : SturmBoundTheorem H (k * G.relIndex H)) : SturmBoundTheorem G k := by
  intro f hf
  have hnorm : 0 ≤ sturmDefect H (k * G.relIndex H) (ModularForm.norm H f) :=
    hH (ModularForm.norm H f) (ModularForm.norm_ne_zero H (by simpa using hf))
  have hle : sturmDefect H (k * G.relIndex H) (ModularForm.norm H f) ≤
      (centralMultiplicity G H : ℝ) * sturmDefect G k f := sturmDefect_norm_le hGH k f
  have hpos : (0 : ℝ) < centralMultiplicity G H := by
    unfold centralMultiplicity
    split_ifs <;> norm_num
  by_contra! h
  exact (coe_mul_lt_mul hpos h).not_ge (by simpa using hnorm.trans hle)

/-- The Sturm bound holds for every arithmetic subgroup contained in the real modular group. -/
private lemma sturmBoundTheorem_of_le (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic]
    (hG : G ≤ 𝒮ℒ) (k : ℤ) : SturmBoundTheorem G k :=
  sturmBoundTheorem_of_norm hG k (sturmBoundTheoremSL2Z _)

/-- The Sturm bound holds for finite-index subgroups of `SL(2, ℤ)`. -/
private lemma sturmBoundTheorem_coe (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) :
    SturmBoundTheorem (Γ : Subgroup (GL (Fin 2) ℝ)) k :=
  sturmBoundTheorem_of_le _ (Γ.map_le_range (mapGL ℝ)) k

private lemma coe_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ((∑ i ∈ s, a i : ℝ) : EReal) = ∑ i ∈ s, (a i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, EReal.coe_add, ih]

/-- Descend the simultaneous cusp bound along an arithmetic inclusion. The translation cycles
parametrize the cusps of the smaller group above infinity of the larger group. -/
private lemma sturmBoundTheorem_of_subgroup_le_SL2Z
    {K H : Subgroup (GL (Fin 2) ℝ)} [K.IsArithmetic] [H.IsArithmetic] [H.HasDetOne]
    (hKH : K ≤ H) (hKSL : K ≤ 𝒮ℒ) (hnegK : (-1 : GL (Fin 2) ℝ) ∈ K) (k : ℤ) :
    SturmBoundTheorem H k := by
  classical
  intro f hf
  let F := ModularForm.restrict hKH f
  let := Fintype.ofFinite (translationCycles K H)
  have hnegH : (-1 : GL (Fin 2) ℝ) ∈ H := hKH hnegK
  have htop : orderAtInfty f ≠ ⊤ := by
    intro h
    exact hf (DFunLike.coe_injective ((orderAtInfty_eq_top_iff_eq_zero H.strictWidthInfty_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f H.strictWidthInfty_mem_strictPeriods)
      f.holo' (ModularFormClass.bdd_at_infty f)).mp h))
  have hbot : orderAtInfty f ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (ModularFormClass.bdd_at_infty f).orderAtInfty_nonneg
  have hfinite : ((orderAtInfty f).toReal : EReal) = orderAtInfty f := EReal.coe_toReal htop hbot
  have hex (c : translationCycles K H) : ∃ g : 𝒮ℒ,
      (g : GL (Fin 2) ℝ) • ∞ = (c.out.out : GL (Fin 2) ℝ)⁻¹ • (∞ : OnePoint ℝ) := by
    have hc : IsCusp ((c.out.out : GL (Fin 2) ℝ)⁻¹ • ∞) K :=
      ((show IsCusp ∞ H from Fact.out).smul_of_mem
        (H.inv_mem c.out.out.property)).of_isFiniteRelIndex
    obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp ((IsArithmetic.isCusp_iff_isCusp_SL2Z K).mp hc)
    exact ⟨⟨mapGL ℝ g, ⟨g, rfl⟩⟩, hg.symm⟩
  choose s hs using hex
  have hsc (c : translationCycles K H) : normCusp K
      (⟦(s c)⁻¹⟧ : 𝒮ℒ ⧸ K.subgroupOf 𝒮ℒ) = translationCycleCusp K H c := by
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    simpa only [coe_inv, inv_inv] using hs c
  have hsinj : Function.Injective (fun c ↦ normCusp K
      (⟦(s c)⁻¹⟧ : 𝒮ℒ ⧸ K.subgroupOf 𝒮ℒ)) := by
    simpa only [hsc] using translationCycleCusp_injective hKH hnegK
  have hcoord (c : translationCycles K H) :
      (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).widthInfty * orderAtInfty f =
        (ConjAct.toConjAct (s c : GL (Fin 2) ℝ)⁻¹ • K).widthInfty *
          orderAtInfty ((F : ℍ → ℂ) ∣[k] (s c : GL (Fin 2) ℝ)) := by
    have : (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).IsArithmetic :=
      isArithmetic_conj_of_mem c.out.out
    have hw : 0 < (ConjAct.toConjAct ((c.out.out : GL (Fin 2) ℝ)⁻¹)⁻¹ • K).widthInfty := by
      simpa only [inv_inv] using
        (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).widthInfty_pos
    have hd : 0 < ((c.out.out : GL (Fin 2) ℝ)⁻¹).det.val := by
      rw [HasDetOne.det_eq (H.inv_mem c.out.out.property)]
      norm_num
    have hds : 0 < (s c : GL (Fin 2) ℝ).det.val := by
      rw [HasDetOne.det_eq (s c).property]
      norm_num
    have hfslash : ((F : ℍ → ℂ) ∣[k] (c.out.out : GL (Fin 2) ℝ)⁻¹) = f :=
      f.slash_action_eq' _ (H.inv_mem c.out.out.property)
    simpa only [inv_inv, hfslash] using
      width_mul_orderAtInfty_slash_eq_of_smul_infty_eq K F k
        (c.out.out : GL (Fin 2) ℝ)⁻¹ (s c : GL (Fin 2) ℝ) hw (hs c).symm hd hds
  have hglobal := sum_width_mul_orderAtInfty_slash_le_projective hKSL hnegK F
    ((ModularForm.restrict_eq_zero_iff hKH f).not.mpr hf) s hsinj
  simp_rw [← hcoord] at hglobal
  rw [← hfinite] at hglobal
  simp only [← EReal.coe_mul] at hglobal
  rw [← coe_finset_sum, EReal.coe_le_coe_iff, ← Finset.sum_mul] at hglobal
  have hwidth : ∑ c : translationCycles K H,
      (ConjAct.toConjAct (c.out.out : GL (Fin 2) ℝ) • K).widthInfty =
        K.relIndex H * H.widthInfty := by
    simpa only [widthInfty, adjoinNegOne_conj, adjoinNegOne_eq_self_iff.mpr hnegK,
      adjoinNegOne_eq_self_iff.mpr hnegH] using sum_strictWidthInfty_translationCycles hKH
  have hrat : (K.ratProjIndex : ℝ) = (K.relIndex H : ℝ) * H.ratProjIndex := by
    exact_mod_cast ratProjIndex_eq_relIndex_mul hKH hnegK hnegH
  have hbudget : K.widthInfty * sturmBound K k =
      (K.relIndex H : ℝ) * H.widthInfty * sturmBound H k := by
    simp only [sturmBound, hrat]
    field_simp [K.widthInfty_pos.ne', H.widthInfty_pos.ne']
  rw [hwidth, hbudget] at hglobal
  have hpos : 0 < (K.relIndex H : ℝ) * H.widthInfty :=
    mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero K.relIndex_ne_zero)) H.widthInfty_pos
  apply (sturmDefect_nonneg_iff f).mpr
  rw [← hfinite, EReal.coe_le_coe_iff]
  exact (mul_le_mul_iff_of_pos_left hpos).mp hglobal

/-- The Sturm bound for an arithmetic determinant-one group containing `-1`. -/
private lemma sturmBoundTheorem_of_negOne_mem (G : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [G.HasDetOne] (hneg : (-1 : GL (Fin 2) ℝ) ∈ G) (k : ℤ) :
    SturmBoundTheorem G k := by
  have hnegSL : (-1 : GL (Fin 2) ℝ) ∈ 𝒮ℒ := by
    exact ⟨-1, by ext i j; simp [mapGL_coe_matrix]⟩
  exact sturmBoundTheorem_of_subgroup_le_SL2Z (K := G ⊓ 𝒮ℒ)
    inf_le_left inf_le_right ⟨hneg, hnegSL⟩ k

/-- The Sturm bound holds for every arithmetic subgroup of determinant one. -/
private lemma sturmBoundTheorem_arithmetic (G : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [G.HasDetOne] (k : ℤ) : SturmBoundTheorem G k :=
  sturmBoundTheorem_of_norm G.le_adjoinNegOne k
    (sturmBoundTheorem_of_negOne_mem G.adjoinNegOne G.negOne_mem_adjoinNegOne _)

end Subgroup

namespace ModularForm

/-- A modular form for an arithmetic determinant-one group vanishes if its order at infinity
exceeds the Sturm bound. -/
lemma eq_zero_of_orderAtInfty_gt_sturmBound
    {G : Subgroup (GL (Fin 2) ℝ)} [G.IsArithmetic] [G.HasDetOne] {k : ℤ}
    (f : ModularForm G k) (hf : (G.sturmBound k : EReal) < orderAtInfty f) : f = 0 :=
  (Subgroup.sturmBoundTheorem_iff G k).mp (Subgroup.sturmBoundTheorem_arithmetic G k) f hf

/-- Finitely many Fourier coefficients determine a modular form at an arithmetic
determinant-one level. -/
instance finiteDimensional_complex (G : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [G.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (ModularForm G k) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, G.strictWidthInfty * G.sturmBound k < N := exists_nat_gt _
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
  have horder : (N : ℕ∞) ≤ (qExpansion G.strictWidthInfty f).order := by
    apply PowerSeries.nat_le_order
    intro i hi
    exact congrFun hf ⟨i, hi⟩
  apply eq_zero_of_orderAtInfty_gt_sturmBound f
  rw [orderAtInfty_eq_qExpansion_order G.strictWidthInfty_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f G.strictWidthInfty_mem_strictPeriods)
    f.holo' (ModularFormClass.bdd_at_infty f)]
  have horder' : (N : EReal) ≤ (qExpansion G.strictWidthInfty f).order := by
    have he : ((N : ℕ∞).toENNReal : EReal) ≤
        ((qExpansion G.strictWidthInfty f).order.toENNReal : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr (ENat.toENNReal_le.mpr horder)
    simpa only [ENat.toENNReal_coe, ← ENNReal.coe_natCast, EReal.coe_nnreal_eq_coe_real,
      NNReal.coe_natCast, EReal.coe_natCast] using he
  have hN' : (G.sturmBound k : EReal) < (N : ℝ) / (G.strictWidthInfty : EReal) := by
    rw [← EReal.coe_div, EReal.coe_lt_coe_iff]
    exact (lt_div_iff₀ G.strictWidthInfty_pos).mpr (by simpa [mul_comm] using hN)
  exact hN'.trans_le (EReal.div_le_div_right_of_nonneg
    (EReal.coe_nonneg.mpr G.strictWidthInfty_pos.le) horder')

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
