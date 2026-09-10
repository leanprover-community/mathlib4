/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Cusps

We define the cusps of a subgroup of `GL(2, ℝ)` as the fixed points of parabolic elements.
-/

@[expose] public section

open Matrix SpecialLinearGroup GeneralLinearGroup Filter Polynomial OnePoint

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace OnePoint

variable {K : Type*} [Field K] [DecidableEq K]

/-- The modular group `SL(2, A)` acts transitively on `OnePoint K`, if `A` is a PID whose fraction
field is `K`. (This includes the case `A = ℤ`, `K = ℚ`.) -/
lemma exists_mem_SL2 (A : Type*) [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K]
    [IsPrincipalIdealRing A] (c : OnePoint K) :
    ∃ g : SL(2, A), (mapGL K g) • ∞ = c := by
  cases c with
  | infty => exact ⟨1, by simp⟩
  | coe q =>
    obtain ⟨g, hg0, hg1⟩ := (IsFractionRing.num_den_reduced A q).isCoprime.exists_SL2_col 0
    exact ⟨g, by simp [hg0, hg1, smul_infty_eq_ite]⟩

end OnePoint

namespace Subgroup.HasDetPlusMinusOne

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {𝒢 : Subgroup (GL (Fin 2) K)} [𝒢.HasDetPlusMinusOne]

lemma isParabolic_iff_of_upperTriangular {g} (hg : g ∈ 𝒢) (hg10 : g 1 0 = 0) :
    g.IsParabolic ↔ (∃ x ≠ 0, g = upperRightHom x) ∨ (∃ x ≠ (0 : K), g = -upperRightHom x) :=
  isParabolic_iff_of_upperTriangular_of_det (HasDetPlusMinusOne.det_eq hg) hg10

end Subgroup.HasDetPlusMinusOne

section IsCusp

/-- The *cusps* of a subgroup of `GL(2, ℝ)` are the fixed points of parabolic elements of `g`. -/
def IsCusp (c : OnePoint ℝ) (𝒢 : Subgroup (GL (Fin 2) ℝ)) : Prop :=
  ∃ g ∈ 𝒢, g.IsParabolic ∧ g • c = c

open scoped Pointwise in
lemma IsCusp.smul {c : OnePoint ℝ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c 𝒢)
    (g : GL (Fin 2) ℝ) : IsCusp (g • c) (ConjAct.toConjAct g • 𝒢) := by
  obtain ⟨p, hp𝒢, hpp, hpc⟩ := hc
  refine ⟨_, 𝒢.smul_mem_pointwise_smul _ _ hp𝒢, ?_, ?_⟩
  · simpa [ConjAct.toConjAct_smul] using hpp
  · simp [ConjAct.toConjAct_smul, mul_smul, hpc]

lemma IsCusp.smul_of_mem {c : OnePoint ℝ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c 𝒢)
    {g : GL (Fin 2) ℝ} (hg : g ∈ 𝒢) : IsCusp (g • c) 𝒢 := by
  convert! hc.smul g
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv, Subgroup.mul_mem_cancel_right _ hg,
    Subgroup.mul_mem_cancel_left _ (inv_mem hg)]

lemma isCusp_iff_of_relIndex_ne_zero {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}
    (h𝒢 : 𝒢' ≤ 𝒢) (h𝒢' : 𝒢'.relIndex 𝒢 ≠ 0) (c : OnePoint ℝ) :
    IsCusp c 𝒢' ↔ IsCusp c 𝒢 := by
  refine ⟨fun ⟨g, hg, hgp, hgc⟩ ↦ ⟨g, h𝒢 hg, hgp, hgc⟩, fun ⟨g, hg, hgp, hgc⟩ ↦ ?_⟩
  obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero h𝒢' hg
  refine ⟨g ^ n, (Subgroup.mem_inf.mpr hgn).1, hgp.pow hn.ne', ?_⟩
  rw [Nat.pos_iff_ne_zero] at hn
  rwa [(hgp.pow hn).smul_eq_self_iff, hgp.parabolicFixedPoint_pow hn, ← hgp.smul_eq_self_iff]

lemma Subgroup.Commensurable.isCusp_iff {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}
    (h𝒢 : Commensurable 𝒢 𝒢') {c : OnePoint ℝ} :
    IsCusp c 𝒢 ↔ IsCusp c 𝒢' := by
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_left, isCusp_iff_of_relIndex_ne_zero inf_le_right]
  · simpa [Subgroup.inf_relIndex_right] using h𝒢.1.relIndex_ne_zero
  · simpa [Subgroup.inf_relIndex_left] using h𝒢.2.relIndex_ne_zero

lemma IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ} (hGH : 𝒢 ≤ ℋ)
    (hc : IsCusp c 𝒢) : IsCusp c ℋ :=
  match hc with | ⟨h, hh, hp, hc⟩ => ⟨h, hGH hh, hp, hc⟩

lemma IsCusp.of_isFiniteRelIndex {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ}
    [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) : IsCusp c 𝒢 := by
  have hGH : 𝒢.relIndex ℋ ≠ 0 := 𝒢.relIndex_ne_zero
  rw [← Subgroup.inf_relIndex_right] at hGH
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_right hGH] at hc
  exact hc.mono inf_le_left

open scoped Pointwise in
/-- Variant version of `IsCusp.of_isFiniteRelIndex`. -/
lemma IsCusp.of_isFiniteRelIndex_conj {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ}
    [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) {h} (hh : h ∈ ℋ) :
    IsCusp c (ConjAct.toConjAct h • 𝒢) := by
  suffices (ConjAct.toConjAct h • 𝒢).IsFiniteRelIndex ℋ from hc.of_isFiniteRelIndex
  constructor
  rw [← ℋ.conjAct_pointwise_smul_eq_self (ℋ.le_normalizer hh), 𝒢.relIndex_pointwise_smul]
  exact 𝒢.relIndex_ne_zero

set_option backward.isDefEq.respectTransparency false in
/-- The cusps of `SL(2, ℤ)` are precisely the elements of `ℙ¹(ℚ)`. -/
lemma isCusp_SL2Z_iff {c : OnePoint ℝ} : IsCusp c 𝒮ℒ ↔ c ∈ Set.range (OnePoint.map Rat.cast) := by
  constructor
  · rintro ⟨-, ⟨g, rfl⟩, hgp, hgc⟩
    simpa only [hgp.smul_eq_self_iff.mp hgc] using ⟨(mapGL ℚ g).parabolicFixedPoint,
      by simp [GeneralLinearGroup.parabolicFixedPoint, apply_ite]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := c.exists_mem_SL2 ℤ
    refine ⟨_, ⟨a * ModularGroup.T * a⁻¹, rfl⟩, ?_, ?_⟩
    · suffices (mapGL ℝ ModularGroup.T).IsParabolic by simpa
      refine ⟨fun ⟨a, ha⟩ ↦ zero_ne_one' ℝ (by simpa [ModularGroup.T] using congr_fun₂ ha 0 1), ?_⟩
      simp [discr_fin_two, trace_fin_two, det_fin_two, ModularGroup.T]
      norm_num
    · rw [← Rat.coe_castHom, ← (Rat.castHom ℝ).algebraMap_toAlgebra]
      simp [OnePoint.map_smul, mul_smul, smul_infty_eq_self_iff, ModularGroup.T]

/-- The cusps of `SL(2, ℤ)` are precisely the `SL(2, ℤ)` orbit of `∞`. -/
lemma isCusp_SL2Z_iff' {c : OnePoint ℝ} : IsCusp c 𝒮ℒ ↔ ∃ g : SL(2, ℤ), c = mapGL ℝ g • ∞ := by
  rw [isCusp_SL2Z_iff]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, rfl⟩ := c.exists_mem_SL2 ℤ
    refine ⟨g, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
      ← (Rat.castHom ℝ).algebraMap_toAlgebra, g.map_mapGL]
  · rintro ⟨g, rfl⟩
    refine ⟨mapGL ℚ g • ∞, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
       ← (Rat.castHom ℝ).algebraMap_toAlgebra, g.map_mapGL]

/-- The cusps of any arithmetic subgroup are the same as those of `SL(2, ℤ)`. -/
lemma Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]
    {c : OnePoint ℝ} : IsCusp c 𝒢 ↔ IsCusp c 𝒮ℒ :=
  is_commensurable.isCusp_iff

end IsCusp

section CuspOrbits
/-!
## Cusp orbits

We consider the orbits for the action of `𝒢` on its own cusps. The main result is that if
`[𝒢.IsArithmetic]` holds, then this set is finite.
-/

/-- The action of `𝒢` on its own cusps. -/
noncomputable def cuspsSubMulAction (𝒢 : Subgroup (GL (Fin 2) ℝ)) :
    SubMulAction 𝒢 (OnePoint ℝ) where
  carrier := {c | IsCusp c 𝒢}
  smul_mem' g _ hc := IsCusp.smul_of_mem hc g.property

@[simp] lemma mem_cuspsSubMulAction {𝒢} {c : OnePoint ℝ} :
    c ∈ cuspsSubMulAction 𝒢 ↔ IsCusp c 𝒢 :=
  Iff.rfl

/-- The type of cusp orbits of `𝒢`, i.e. orbits for the action of `𝒢` on its own cusps. -/
abbrev CuspOrbits (𝒢 : Subgroup (GL (Fin 2) ℝ)) :=
  MulAction.orbitRel.Quotient 𝒢 (cuspsSubMulAction 𝒢)

namespace CuspOrbits

variable {G H K : Subgroup (GL (Fin 2) ℝ)}

/-- The map on cusp orbits induced by an inclusion of groups. -/
noncomputable def map (hGH : G ≤ H) : CuspOrbits G → CuspOrbits H :=
  Quotient.map (fun c ↦ ⟨c.val, c.property.mono hGH⟩)
    (fun _ _ ⟨g, hg⟩ ↦ ⟨⟨g.val, hGH g.property⟩, Subtype.ext (congr(Subtype.val $hg))⟩)

@[simp] lemma map_mk (hGH : G ≤ H) (c : cuspsSubMulAction G) :
    map hGH ⟦c⟧ = ⟦⟨c.val, c.property.mono hGH⟩⟧ := rfl

@[simp] lemma map_map (hGH : G ≤ H) (hHK : H ≤ K) (c : CuspOrbits G) :
    map hHK (map hGH c) = map (hGH.trans hHK) c := by
  induction c using Quotient.inductionOn
  rfl

/-- Every cusp orbit lifts along an inclusion of finite relative index. -/
lemma map_surjective (hGH : G ≤ H) [G.IsFiniteRelIndex H] :
    Function.Surjective (map hGH) := by
  intro c
  induction c using Quotient.inductionOn with
  | h c => exact ⟨⟦⟨c.val, c.property.of_isFiniteRelIndex⟩⟧, by simp⟩

open scoped Pointwise

/-- Conjugation transports cusp orbits along the action on the projective line. -/
noncomputable def conj (G : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℝ) :
    CuspOrbits G → CuspOrbits (ConjAct.toConjAct g • G) :=
  Quotient.map (fun c ↦ ⟨g • c.val, c.property.smul g⟩) (by
    rintro c d ⟨a, ha⟩
    refine ⟨⟨ConjAct.toConjAct g • a.val, G.smul_mem_pointwise_smul _ _ a.property⟩, ?_⟩
    have ha' : (a : GL (Fin 2) ℝ) • d.val = c.val := congr(Subtype.val $ha)
    apply Subtype.ext
    exact show (g * a.val * g⁻¹) • (g • d.val) = g • c.val from by
      simp only [mul_smul, inv_smul_smul, ha'])

@[simp] lemma conj_mk (g : GL (Fin 2) ℝ) (c : cuspsSubMulAction G) :
    conj G g ⟦c⟧ = ⟦⟨g • c.val, c.property.smul g⟩⟧ :=
  rfl

lemma conj_bijective (G : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℝ) :
    Function.Bijective (conj G g) := by
  constructor
  · refine Quotient.forall.mpr fun c ↦ Quotient.forall.mpr fun d h ↦ ?_
    obtain ⟨a, ha⟩ := Quotient.eq.mp h
    refine Quotient.eq.mpr ⟨⟨ConjAct.toConjAct g⁻¹ • a.val, ?_⟩, ?_⟩
    · exact G.mem_pointwise_smul_iff_inv_smul_mem.mp a.property
    · have ha' : (a : GL (Fin 2) ℝ) • (g • d.val) = g • c.val := congr(Subtype.val $ha)
      ext
      simpa [-ConjAct.toConjAct_inv, -map_inv, ConjAct.toConjAct_smul, mul_smul, inv_smul_eq_iff]
  · refine Quotient.forall.mpr fun c ↦ ⟨⟦⟨g⁻¹ • c.val, ?_⟩⟧, by simp⟩
    simpa [← mul_smul, ← ConjAct.toConjAct_mul] using c.property.smul g⁻¹

@[simp] lemma map_conj (hGH : G ≤ H) (g : GL (Fin 2) ℝ) (c : CuspOrbits G) :
    map (by simpa) (conj G g c) = conj H g (map hGH c) := by
  induction c using Quotient.inductionOn
  rfl

/-- The natural map from cusp orbits for `G` to those for `G.adjoinNegOne` is a bijection. -/
lemma map_adjoinNegOne_bijective (G : Subgroup (GL (Fin 2) ℝ)) :
    Function.Bijective (map G.le_adjoinNegOne) := by
  refine ⟨Quotient.forall.mpr fun c ↦ Quotient.forall.mpr fun d h ↦ ?_,
    map_surjective G.le_adjoinNegOne⟩
  obtain ⟨a, ha⟩ := Quotient.eq.mp h
  have ha' : (a : GL (Fin 2) ℝ) • d.val = c.val := congr(Subtype.val $ha)
  rcases a.property with hmem | hmem
  · exact Quotient.eq.mpr ⟨⟨a.val, hmem⟩, Subtype.ext ha'⟩
  · exact Quotient.eq.mpr ⟨⟨-a.val, hmem⟩, Subtype.ext <| by simpa using ha'⟩

end CuspOrbits

/-- Surjection from `SL(2, ℤ) / (𝒢 ⊓ SL(2, ℤ))` to cusp orbits of `𝒢`. Mostly useful for showing
that `CuspOrbits 𝒢` is finite for arithmetic subgroups. -/
noncomputable def cosetToCuspOrbit (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] :
    SL(2, ℤ) ⧸ (𝒢.comap <| mapGL ℝ) → CuspOrbits 𝒢 :=
  Quotient.lift
    (fun g ↦ ⟦⟨mapGL ℝ g⁻¹ • ∞,
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr <| isCusp_SL2Z_iff.mpr
        ⟨mapGL ℚ g⁻¹ • ∞, by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
          ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧)
    (fun a b hab ↦ by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hab
      refine Quotient.eq.mpr ⟨⟨_, hab⟩, ?_⟩
      simp [mul_smul])

@[simp]
lemma cosetToCuspOrbit_apply_mk {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] (g : SL(2, ℤ)) :
    cosetToCuspOrbit 𝒢 ⟦g⟧ = ⟦⟨mapGL ℝ g⁻¹ • ∞,
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr <| isCusp_SL2Z_iff.mpr
      ⟨mapGL ℚ g⁻¹ • ∞, by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
        ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧ :=
  rfl

lemma surjective_cosetToCuspOrbit (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] :
    (cosetToCuspOrbit 𝒢).Surjective := by
  rintro ⟨c, (hc : IsCusp c _)⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
  obtain ⟨g, rfl⟩ := hc
  use ⟦g⁻¹⟧
  aesop

/-- An arithmetic subgroup has finitely many cusp orbits. -/
instance (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] : Finite (CuspOrbits 𝒢) :=
  .of_surjective _ (surjective_cosetToCuspOrbit 𝒢)

end CuspOrbits

section Width
/-!
## Width of a cusp

We define the *strict width* of `𝒢` at `∞` to be the smallest `h > 0` such that `[1, h; 0, 1] ∈ 𝒢`,
or `0` if no such `h` exists; and the *width* of `𝒢` to be the strict width of the subgroup
generated by `𝒢` and `-1`, or equivalently the smallest `h > 0` such that `±[1, h; 0, 1] ∈ 𝒢`
(again, if it exists). We show both widths exist when `𝒢` is discrete and has det `± 1`.
-/

namespace Subgroup

section Ring

variable {R : Type*} [Ring R] (𝒢 : Subgroup (GL (Fin 2) R))

/-- For a subgroup `𝒢` of `GL(2, R)`, this is the additive group of `x : R` such that
`[1, x; 0, 1] ∈ 𝒢`. -/
def strictPeriods : AddSubgroup R :=
  (toAddSubgroup 𝒢).comap upperRightHom.toAddMonoidHom

variable {𝒢} in
@[simp] lemma mem_strictPeriods_iff {x : R} :
    x ∈ 𝒢.strictPeriods ↔ upperRightHom x ∈ 𝒢 := by
  simp [strictPeriods]

/-- For a subgroup `𝒢` of `GL(2, R)`, this is the additive group of `x : R` such that
`±[1, x; 0, 1] ∈ 𝒢`. -/
protected noncomputable def periods : AddSubgroup R :=
  𝒢.adjoinNegOne.strictPeriods

lemma strictPeriods_le_periods : 𝒢.strictPeriods ≤ 𝒢.periods := by
  intro k
  simp only [Subgroup.periods, strictPeriods]
  apply 𝒢.le_adjoinNegOne

/-- A subgroup is *regular at ∞* if its periods and strict periods coincide. -/
def IsRegularAtInfty : Prop :=
  𝒢.strictPeriods = 𝒢.periods

lemma IsRegularAtInfty.eq (h : 𝒢.IsRegularAtInfty) : 𝒢.strictPeriods = 𝒢.periods := h

open scoped Classical in
/-- The regularity factor at infinity: one for a regular cusp and two otherwise. -/
noncomputable def regularityFactorInfty : ℕ :=
  if 𝒢.IsRegularAtInfty then 1 else 2

@[simp] lemma regularityFactorInfty_of_isRegularAtInfty (h : 𝒢.IsRegularAtInfty) :
    𝒢.regularityFactorInfty = 1 := by
  simp [regularityFactorInfty, h]

@[simp] lemma regularityFactorInfty_of_not_isRegularAtInfty (h : ¬ 𝒢.IsRegularAtInfty) :
    𝒢.regularityFactorInfty = 2 := by
  simp [regularityFactorInfty, h]

lemma relIndex_strictPeriods :
    𝒢.strictPeriods.relIndex 𝒢.periods = 1 ∨ 𝒢.strictPeriods.relIndex 𝒢.periods = 2 := by
  by_cases h : 𝒢.strictPeriods = 𝒢.periods
  · simp [h]
  · replace h := 𝒢.strictPeriods_le_periods.lt_of_ne h
    obtain ⟨u, hu_mem, hu_notMem⟩ := (SetLike.lt_iff_le_and_exists.mp h).2
    rw [AddSubgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine .inr ⟨u, hu_mem, hu_notMem, fun b hb ↦ ?_⟩
    simp only [Subgroup.periods, mem_strictPeriods_iff, mem_adjoinNegOne_iff,
      AddChar.map_add_eq_mul] at hu_mem hu_notMem hb ⊢
    rcases hb with h | h
    · exact Or.inr h
    · simpa only [neg_mul_neg] using Or.inl (mul_mem h <| hu_mem.resolve_left hu_notMem)

/-- The regularity factor is the index of strict periods in periods. -/
lemma relIndex_strictPeriods_eq_regularityFactorInfty :
    𝒢.strictPeriods.relIndex 𝒢.periods = 𝒢.regularityFactorInfty := by
  by_cases h : 𝒢.IsRegularAtInfty
  · simp [h.eq, regularityFactorInfty, h]
  · rw [𝒢.regularityFactorInfty_of_not_isRegularAtInfty h]
    exact 𝒢.relIndex_strictPeriods.resolve_left fun hi ↦
      h (𝒢.strictPeriods_le_periods.antisymm (AddSubgroup.relIndex_eq_one.mp hi))

lemma commensurable_strictPeriods_periods :
    𝒢.strictPeriods.Commensurable 𝒢.periods := by
  simp_rw [AddSubgroup.Commensurable, AddSubgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  constructor
  · rcases 𝒢.relIndex_strictPeriods with h | h <;> simp [h]
  · simp [AddSubgroup.relIndex_eq_one.mpr 𝒢.strictPeriods_le_periods]

variable {𝒢}

lemma strictPeriods_eq_periods_of_neg_one_mem (h𝒢 : -1 ∈ 𝒢) :
    𝒢.strictPeriods = 𝒢.periods := by
  simp [Subgroup.periods, adjoinNegOne_eq_self_iff.mpr h𝒢]

lemma isRegularAtInfty_of_neg_one_mem (h𝒢 : -1 ∈ 𝒢) : 𝒢.IsRegularAtInfty :=
  𝒢.strictPeriods_eq_periods_of_neg_one_mem h𝒢

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- If `𝒢` is discrete, so is its strict period subgroup. -/
instance instDiscreteTopStrictPeriods [hG : DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.strictPeriods := by
  let H : Set (GL (Fin 2) R) := 𝒢 ∩ Set.range upperRightHom
  have hH : DiscreteTopology H := hG.of_subset Set.inter_subset_left
  have : Set.MapsTo upperRightHom 𝒢.strictPeriods H := fun x hx ↦ by
    grind [SetLike.mem_coe, Subgroup.mem_strictPeriods_iff]
  exact .of_continuous_injective (continuous_upperRightHom.restrict this)
    (this.restrict_inj.mpr injective_upperRightHom.injOn)

/-- If `𝒢` is discrete, so is its period subgroup. -/
instance instDiscreteTopPeriods [T2Space R] [hG : DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.periods :=
  inferInstanceAs (DiscreteTopology 𝒢.adjoinNegOne.strictPeriods)

end Ring

lemma strictPeriods_eq_zmultiples_one_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hΓ : ModularGroup.T ∈ Γ) :
    strictPeriods (Γ : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1 := by
  ext x
  simp only [mem_strictPeriods_iff, Subgroup.mem_map, Units.ext_iff, mapGL_coe_matrix,
    map_apply_coe]
  refine ⟨fun ⟨g, _, hg⟩ ↦ ⟨g 0 1, by simpa using congr_fun₂ hg 0 1⟩, ?_⟩
  rintro ⟨m, rfl⟩
  refine ⟨ModularGroup.T ^ m, zpow_mem hΓ m, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]

@[simp] lemma strictPeriods_SL2Z : strictPeriods 𝒮ℒ = AddSubgroup.zmultiples 1 := by
  simpa [MonoidHom.range_eq_map] using strictPeriods_eq_zmultiples_one_of_T_mem (mem_top _)

section Real

variable (𝒢 : Subgroup (GL (Fin 2) ℝ))

open scoped Classical in
/-- The strict width of the cusp `∞`, i.e. the `x` such that `𝒢.strictPeriods = zmultiples x`, or
0 if no such `x` exists. -/
noncomputable def strictWidthInfty : ℝ :=
  if h : DiscreteTopology 𝒢.strictPeriods then
    |Exists.choose <| 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
      <| AddSubgroup.discrete_iff_addCyclic.mpr h|
  else 0

lemma strictWidthInfty_nonneg : 0 ≤ 𝒢.strictWidthInfty := by
  unfold strictWidthInfty; aesop

/-- The width of the cusp `∞`, i.e. the `x` such that `𝒢.periods = zmultiples x`, or 0 if no such
`x` exists. -/
noncomputable def widthInfty : ℝ := 𝒢.adjoinNegOne.strictWidthInfty

lemma widthInfty_nonneg : 0 ≤ 𝒢.widthInfty := 𝒢.adjoinNegOne.strictWidthInfty_nonneg

variable {𝒢} in
lemma strictPeriods_eq_zmultiples_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] :
    𝒢.strictPeriods = AddSubgroup.zmultiples 𝒢.strictWidthInfty := by
  simp [Subgroup.strictWidthInfty, dite_eq_left,
    Exists.choose_spec <| 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
      <| AddSubgroup.discrete_iff_addCyclic.mpr inferInstance]

lemma strictWidthInfty_eq_one_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hΓ : ModularGroup.T ∈ Γ) :
    strictWidthInfty (Γ : Subgroup (GL (Fin 2) ℝ)) = 1 := by
  have hsp := strictPeriods_eq_zmultiples_one_of_T_mem hΓ
  have : DiscreteTopology (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    -- In fact the image of `Γ` in `GL (Fin 2) ℝ` is itself discrete, but this is quicker:
    rw [hsp]
    infer_instance
  rw [strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
    AddSubgroup.zmultiples_eq_zmultiples_iff (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)]
    at hsp
  grind [strictWidthInfty_nonneg]

lemma strictWidthInfty_SL2Z : strictWidthInfty 𝒮ℒ = 1 := by
  simpa [MonoidHom.range_eq_map] using strictWidthInfty_eq_one_of_T_mem (mem_top _)

lemma strictWidthInfty_mem_strictPeriods : 𝒢.strictWidthInfty ∈ 𝒢.strictPeriods := by
  by_cases h : DiscreteTopology 𝒢.strictPeriods
  · simp [strictPeriods_eq_zmultiples_strictWidthInfty]
  · simp [strictWidthInfty, dite_eq_right h]

variable {𝒢} in
lemma periods_eq_zmultiples_widthInfty [DiscreteTopology 𝒢.periods] :
    𝒢.periods = AddSubgroup.zmultiples 𝒢.widthInfty :=
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  𝒢.adjoinNegOne.strictPeriods_eq_zmultiples_strictWidthInfty

lemma widthInfty_mem_periods : 𝒢.widthInfty ∈ 𝒢.periods :=
  𝒢.adjoinNegOne.strictWidthInfty_mem_strictPeriods

lemma two_mul_widthInfty_mem_strictPeriods : 2 * 𝒢.widthInfty ∈ 𝒢.strictPeriods := by
  have := 𝒢.widthInfty_mem_periods
  simp only [Subgroup.periods, mem_strictPeriods_iff] at this
  rcases this with (h | h) <;>
    simpa [-upperRightHom_apply, ← AddChar.map_nsmul_eq_pow] using Subgroup.pow_mem _ h 2

variable {𝒢} in
lemma strictWidthInfty_pos_iff [DiscreteTopology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] :
    0 < 𝒢.strictWidthInfty ↔ IsCusp ∞ 𝒢 := by
  constructor
  · refine fun h ↦ ⟨_, mem_strictPeriods_iff.mpr 𝒢.strictWidthInfty_mem_strictPeriods, ?_, ?_⟩
    · rw [GeneralLinearGroup.isParabolic_iff_of_upperTriangular (by simp)]
      simpa using h.ne'
    · simp [smul_infty_eq_self_iff]
  · -- Hard implication: if `∞` is a cusp, show the strict width is positive.
    rintro ⟨g, hgg, hgp, hgi⟩
    apply 𝒢.strictWidthInfty_nonneg.lt_of_ne'
    rw [← AddSubgroup.zmultiples_ne_bot]
    simp only [AddSubgroup.ne_bot_iff_exists_ne_zero, Subtype.exists, Ne, AddSubgroup.mk_eq_zero,
      exists_prop, and_comm, ← strictPeriods_eq_zmultiples_strictWidthInfty, mem_strictPeriods_iff]
    -- We have some `g ∈ 𝒢` which is parabolic and fixes `∞`. So `g = ±[1, x; 0, 1]` some `x ≠ 0`.
    rw [smul_infty_eq_self_iff] at hgi
    rw [Subgroup.HasDetPlusMinusOne.isParabolic_iff_of_upperTriangular hgg hgi] at hgp
    rcases hgp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · -- If `g = [1, x; 0, 1]`, we're done
      exact ⟨x, hx, hgg⟩
    · -- If `g = -[1, x; 0, 1]` then `g ^ 2 = [1, 2 * x; 0, 1]`.
      exact ⟨2 • x, by grind,
        by simpa only [AddChar.map_nsmul_eq_pow, neg_sq] using pow_mem hgg 2⟩

lemma strictWidthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.strictWidthInfty := by
  rw [strictWidthInfty_pos_iff]
  simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩

variable {𝒢} in
lemma isCusp_of_mem_strictPeriods {h : ℝ} (hh : 0 < h) (h𝒢 : h ∈ 𝒢.strictPeriods) :
    IsCusp OnePoint.infty 𝒢 := by
  refine ⟨upperRightHom h, 𝒢.mem_strictPeriods_iff.mp h𝒢, ?_, smul_infty_eq_self_iff.mpr rfl⟩
  exact (GeneralLinearGroup.isParabolic_iff_of_upperTriangular rfl).mpr ⟨rfl, hh.ne'⟩

variable {𝒢} in
lemma widthInfty_pos_iff [DiscreteTopology 𝒢.periods] [𝒢.HasDetPlusMinusOne] :
    0 < 𝒢.widthInfty ↔ IsCusp ∞ 𝒢 := by
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  rw [widthInfty, strictWidthInfty_pos_iff, (commensurable_adjoinNegOne_self 𝒢).isCusp_iff]

variable {𝒢} in
lemma isRegularAtInfty_iff [DiscreteTopology 𝒢.periods] :
    𝒢.IsRegularAtInfty ↔ 𝒢.widthInfty ∈ 𝒢.strictPeriods := by
  refine ⟨fun h ↦ h ▸ widthInfty_mem_periods 𝒢, fun h ↦ ?_⟩
  apply 𝒢.strictPeriods_le_periods.antisymm
  rwa [periods_eq_zmultiples_widthInfty, AddSubgroup.zmultiples_le]

lemma strictWidthInfty_of_isRegularAtInfty (h𝒢 : 𝒢.IsRegularAtInfty) :
    𝒢.strictWidthInfty = 𝒢.widthInfty := by
  have heq : 𝒢.strictPeriods = 𝒢.adjoinNegOne.strictPeriods := h𝒢.eq
  simp only [widthInfty, strictWidthInfty]
  congr!

lemma strictWidthInfty_of_not_isRegularAtInfty (h𝒢 : ¬ 𝒢.IsRegularAtInfty) :
    𝒢.strictWidthInfty = 2 * 𝒢.widthInfty := by
  by_cases hd : DiscreteTopology 𝒢.strictPeriods
  · have : DiscreteTopology 𝒢.periods :=
      𝒢.commensurable_strictPeriods_periods.discreteTopology_iff.mp hd
    have hw : 0 < 𝒢.widthInfty := by
      refine 𝒢.widthInfty_nonneg.lt_of_ne fun h ↦ h𝒢 ?_
      exact isRegularAtInfty_iff.mpr (h ▸ 𝒢.strictPeriods.zero_mem)
    have hi : 𝒢.strictPeriods.relIndex 𝒢.periods = 2 :=
      𝒢.relIndex_strictPeriods.resolve_left fun hi ↦
        h𝒢 (𝒢.strictPeriods_le_periods.antisymm (AddSubgroup.relIndex_eq_one.mp hi))
    obtain ⟨n, hn⟩ := (𝒢.periods_eq_zmultiples_widthInfty ▸
      𝒢.strictPeriods_le_periods 𝒢.strictWidthInfty_mem_strictPeriods)
    have hnpos : 0 ≤ n := by
      have hn' : 0 ≤ n * 𝒢.widthInfty := by
        simpa only [← hn, zsmul_eq_mul] using 𝒢.strictWidthInfty_nonneg
      exact_mod_cast (nonneg_of_mul_nonneg_left hn' hw)
    rw [strictPeriods_eq_zmultiples_strictWidthInfty, periods_eq_zmultiples_widthInfty,
      ← hn, AddSubgroup.relIndex_zmultiples_zsmul] at hi
    have hn2 : n = 2 := by
      have hnabs : n.natAbs = 2 := by
        simpa [addOrderOf_eq_zero (not_isOfFinAddOrder_of_isAddTorsionFree hw.ne')] using hi
      omega
    simpa [hn2, zsmul_eq_mul] using hn.symm
  · have hp : ¬ DiscreteTopology 𝒢.adjoinNegOne.strictPeriods :=
      mt 𝒢.commensurable_strictPeriods_periods.discreteTopology_iff.mpr hd
    simp [widthInfty, strictWidthInfty, hd, hp]

/-- The strict width is the width multiplied by the regularity factor. -/
lemma strictWidthInfty_eq_regularityFactorInfty_mul_widthInfty :
    𝒢.strictWidthInfty = 𝒢.regularityFactorInfty * 𝒢.widthInfty := by
  by_cases h : 𝒢.IsRegularAtInfty
  · simp [𝒢.strictWidthInfty_of_isRegularAtInfty h, h]
  · simp [𝒢.strictWidthInfty_of_not_isRegularAtInfty h, h]

lemma widthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.widthInfty := by
  apply strictWidthInfty_pos

open scoped Pointwise

/-- Translation parameters under an upper triangular change of cusp coordinate. -/
lemma mem_strictPeriods_conj_of_upperTriangular {G : Subgroup (GL (Fin 2) ℝ)}
    {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) {x : ℝ} :
    x ∈ (ConjAct.toConjAct g⁻¹ • G).strictPeriods ↔ (g 0 0 / g 1 1) * x ∈ G.strictPeriods := by
  rw [mem_strictPeriods_iff, mem_pointwise_smul_iff_inv_smul_mem, mem_strictPeriods_iff]
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [upperRightHom_conj_of_upperTriangular g hg]

/-- Strict cusp widths scale inversely under an upper triangular change of coordinate. -/
lemma strictWidthInfty_conj_of_upperTriangular {G : Subgroup (GL (Fin 2) ℝ)}
    [DiscreteTopology G] (hw : 0 < G.strictWidthInfty)
    {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) (ha : 0 < g 0 0 / g 1 1) :
    (ConjAct.toConjAct g⁻¹ • G).strictWidthInfty = G.strictWidthInfty / (g 0 0 / g 1 1) := by
  have hperiods : (ConjAct.toConjAct g⁻¹ • G).strictPeriods =
      AddSubgroup.zmultiples (G.strictWidthInfty / (g 0 0 / g 1 1)) := by
    ext
    rw [mem_strictPeriods_conj_of_upperTriangular hg, strictPeriods_eq_zmultiples_strictWidthInfty]
    grind [AddSubgroup.mem_zmultiples_iff]
  have hp : 0 < G.strictWidthInfty / (g 0 0 / g 1 1) := div_pos hw ha
  rw [strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
    AddSubgroup.zmultiples_eq_zmultiples_iff (not_isOfFinAddOrder_of_isAddTorsionFree hp.ne')]
      at hperiods
  have hn : 0 ≤ (ConjAct.toConjAct g⁻¹ • G).strictWidthInfty := strictWidthInfty_nonneg _
  grind

/-- Adjoining `-1` commutes with conjugation. -/
lemma adjoinNegOne_conj (G : Subgroup (GL (Fin 2) ℝ)) (g : ConjAct (GL (Fin 2) ℝ)) :
    (g • G).adjoinNegOne = g • G.adjoinNegOne := by
  ext x
  simp only [mem_adjoinNegOne_iff, mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, mul_neg, neg_mul]

/-- Cusp widths scale inversely under an upper triangular change of coordinate. -/
lemma widthInfty_conj_of_upperTriangular {G : Subgroup (GL (Fin 2) ℝ)}
    [DiscreteTopology G] (hw : 0 < G.widthInfty)
    {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) (ha : 0 < g 0 0 / g 1 1) :
    (ConjAct.toConjAct g⁻¹ • G).widthInfty = G.widthInfty / (g 0 0 / g 1 1) := by
  simpa [widthInfty, adjoinNegOne_conj] using
    strictWidthInfty_conj_of_upperTriangular hw hg ha

/-- Cusp widths scale by the absolute value of the coordinate dilation, allowing either
orientation. -/
lemma widthInfty_conj_of_upperTriangular_abs {G : Subgroup (GL (Fin 2) ℝ)}
    [DiscreteTopology G] (hw : 0 < G.widthInfty)
    {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) :
    (ConjAct.toConjAct g⁻¹ • G).widthInfty = G.widthInfty / |g 0 0 / g 1 1| := by
  have ha : 0 < |g 0 0 / g 1 1| := by
    simpa [Matrix.det_fin_two, hg] using g.det_ne_zero
  have hperiods : (ConjAct.toConjAct g⁻¹ • G.adjoinNegOne).strictPeriods =
      AddSubgroup.zmultiples (G.widthInfty / |g 0 0 / g 1 1|) := by
    ext x
    rw [mem_strictPeriods_conj_of_upperTriangular hg,
      strictPeriods_eq_zmultiples_strictWidthInfty]
    rcases le_total 0 (g 0 0 / g 1 1) with h | h
    · rw [abs_of_nonneg h]
      grind [AddSubgroup.mem_zmultiples_iff, widthInfty]
    · rw [abs_of_nonpos h]
      constructor <;> exact fun ⟨m, hm⟩ ↦ ⟨-m, by grind [widthInfty]⟩
  have hp : 0 < G.widthInfty / |g 0 0 / g 1 1| := div_pos hw ha
  rw [strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
    AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree hp.ne')] at hperiods
  rw [widthInfty, adjoinNegOne_conj]
  have hn : 0 ≤ (ConjAct.toConjAct g⁻¹ • G.adjoinNegOne).strictWidthInfty :=
    strictWidthInfty_nonneg _
  grind

/-- In a discrete determinant-one group with a cusp at infinity, every element fixing
infinity is a signed translation. -/
lemma eq_upperRightHom_or_neg_of_upperTriangular
    {G : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology G] [G.HasDetOne]
    (hw : 0 < G.widthInfty) {g : GL (Fin 2) ℝ} (hgG : g ∈ G) (hg : g 1 0 = 0) :
    g = upperRightHom (g 0 1) ∨ g = -upperRightHom (-g 0 1) := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    simpa [Matrix.det_fin_two, hg] using congrArg Units.val (HasDetOne.det_eq hgG)
  have hd : g 1 1 ≠ 0 := by grind
  have ha : 0 < g 0 0 / g 1 1 := div_pos_iff.mpr <| mul_pos_iff.mp <| by grind
  have hwidth : G.widthInfty = G.widthInfty / (g 0 0 / g 1 1) := by
    simpa only [G.conjAct_pointwise_smul_eq_self (G.le_normalizer (G.inv_mem hgG))] using
      widthInfty_conj_of_upperTriangular hw hg ha
  have heq : g 0 0 = g 1 1 := by grind
  rcases (show g 1 1 = 1 ∨ g 1 1 = -1 by grind) with h | h <;> [left; right] <;>
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hg, heq, h]

end Real

end Subgroup

open Subgroup

namespace CongruenceSubgroup

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma strictPeriods_Gamma0 (N : ℕ) :
    strictPeriods (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1 :=
  strictPeriods_eq_zmultiples_one_of_T_mem <| by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma strictPeriods_Gamma1 (N : ℕ) :
    strictPeriods (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1 :=
  strictPeriods_eq_zmultiples_one_of_T_mem <| by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma strictWidthInfty_Gamma0 (N : ℕ) :
    strictWidthInfty (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) = 1 :=
  strictWidthInfty_eq_one_of_T_mem <| by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma strictWidthInfty_Gamma1 (N : ℕ) :
    strictWidthInfty (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) = 1 :=
  strictWidthInfty_eq_one_of_T_mem <| by simp [ModularGroup.T]

@[simp] lemma strictPeriods_Gamma (N : ℕ) :
    strictPeriods (Gamma N : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples ↑N := by
  ext x
  have : AddSubgroup.zmultiples ↑N = .map (Int.castAddHom ℝ) (.zmultiples N) := by simp
  simp only [this, mem_strictPeriods_iff, Subgroup.mem_map, Gamma_mem]
  constructor
  · rintro ⟨g, ⟨-, hg, -, -⟩, hx⟩
    rw [show x = g 0 1 by simpa using congr_arg (· 0 1) hx.symm]
    apply AddSubgroup.mem_map_of_mem
    rwa [Int.mem_zmultiples_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  · simp only [AddSubgroup.mem_map, AddSubgroup.mem_zmultiples_iff, existsAndEq, true_and,
      Units.ext_iff, mapGL_coe_matrix, map_apply_coe, forall_exists_index]
    refine fun a ha ↦ ⟨ModularGroup.T ^ (a * N), by simp [ModularGroup.coe_T_zpow], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ← ha]

@[simp] lemma strictWidthInfty_Gamma (N : ℕ) [NeZero N] :
    strictWidthInfty (Gamma N : Subgroup (GL (Fin 2) ℝ)) = N := by
  have hsp := strictPeriods_Gamma N
  rw [strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
    AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree (NeZero.ne _))] at hsp
  grind [strictWidthInfty_nonneg, Nat.cast_nonneg]

end CongruenceSubgroup

end Width
