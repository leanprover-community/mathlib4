/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Algebra.Ring.Real

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

open Pointwise in
lemma IsCusp.smul {c : OnePoint ℝ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c 𝒢)
    (g : GL (Fin 2) ℝ) : IsCusp (g • c) (ConjAct.toConjAct g • 𝒢) := by
  obtain ⟨p, hp𝒢, hpp, hpc⟩ := hc
  refine ⟨_, 𝒢.smul_mem_pointwise_smul _ _ hp𝒢, ?_, ?_⟩
  · simpa [ConjAct.toConjAct_smul] using hpp
  · simp [ConjAct.toConjAct_smul, SemigroupAction.mul_smul, hpc]

lemma IsCusp.smul_of_mem {c : OnePoint ℝ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c 𝒢)
    {g : GL (Fin 2) ℝ} (hg : g ∈ 𝒢) : IsCusp (g • c) 𝒢 := by
  convert hc.smul g
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
  · simpa [Subgroup.inf_relIndex_right] using h𝒢.1
  · simpa [Subgroup.inf_relIndex_left] using h𝒢.2

lemma IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ} (hGH : 𝒢 ≤ ℋ)
    (hc : IsCusp c 𝒢) : IsCusp c ℋ :=
  match hc with | ⟨h, hh, hp, hc⟩ => ⟨h, hGH hh, hp, hc⟩

lemma IsCusp.of_isFiniteRelIndex {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ}
    [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) : IsCusp c 𝒢 := by
  have hGH : 𝒢.relIndex ℋ ≠ 0 := 𝒢.relIndex_ne_zero
  rw [← Subgroup.inf_relIndex_right] at hGH
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_right hGH] at hc
  exact hc.mono inf_le_left

open Pointwise in
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
      simp [OnePoint.map_smul, SemigroupAction.mul_smul, smul_infty_eq_self_iff, ModularGroup.T]

set_option backward.isDefEq.respectTransparency false in
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

/-- The type of cusp orbits of `𝒢`, i.e. orbits for the action of `𝒢` on its own cusps. -/
abbrev CuspOrbits (𝒢 : Subgroup (GL (Fin 2) ℝ)) :=
  MulAction.orbitRel.Quotient 𝒢 (cuspsSubMulAction 𝒢)

set_option backward.isDefEq.respectTransparency false in
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
      simp [SemigroupAction.mul_smul])

set_option backward.isDefEq.respectTransparency false in
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

lemma commensurable_strictPeriods_periods :
    𝒢.strictPeriods.Commensurable 𝒢.periods := by
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

open Classical in
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
  simp [Subgroup.strictWidthInfty, dif_pos,
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
  · simp [strictWidthInfty, dif_neg h]

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

lemma widthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.widthInfty := by
  apply strictWidthInfty_pos

end Real

end Subgroup

open Subgroup

namespace CongruenceSubgroup

@[simp] lemma strictPeriods_Gamma0 (N : ℕ) :
    strictPeriods (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1 :=
  strictPeriods_eq_zmultiples_one_of_T_mem <| by simp [ModularGroup.T]

@[simp] lemma strictPeriods_Gamma1 (N : ℕ) :
    strictPeriods (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1 :=
  strictPeriods_eq_zmultiples_one_of_T_mem <| by simp [ModularGroup.T]

@[simp] lemma strictWidthInfty_Gamma0 (N : ℕ) :
    strictWidthInfty (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) = 1 :=
  strictWidthInfty_eq_one_of_T_mem <| by simp [ModularGroup.T]

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
