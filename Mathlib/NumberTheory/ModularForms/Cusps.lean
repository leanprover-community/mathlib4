/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# Cusps

We define the cusps of a subgroup of `GL(2, ℝ)` as the fixed points of parabolic elements.
-/

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
  · simp [ConjAct.toConjAct_smul, MulAction.mul_smul, hpc]

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

@[deprecated (since := "2025-09-13")]
alias isCusp_iff_of_relindex_ne_zero := isCusp_iff_of_relIndex_ne_zero

lemma Subgroup.Commensurable.isCusp_iff {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}
    (h𝒢 : Commensurable 𝒢 𝒢') {c : OnePoint ℝ} :
    IsCusp c 𝒢 ↔ IsCusp c 𝒢' := by
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_left, isCusp_iff_of_relIndex_ne_zero inf_le_right]
  · simpa [Subgroup.inf_relIndex_right] using h𝒢.1
  · simpa [Subgroup.inf_relIndex_left] using h𝒢.2

@[deprecated (since := "2025-09-17")]
alias Commensurable.isCusp_iff := Subgroup.Commensurable.isCusp_iff

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
      simp [disc_fin_two, trace_fin_two, det_fin_two, ModularGroup.T]
      norm_num
    · rw [← Rat.coe_castHom, ← (Rat.castHom ℝ).algebraMap_toAlgebra]
      simp [OnePoint.map_smul, MulAction.mul_smul, smul_infty_eq_self_iff, ModularGroup.T]

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
def cusps_subMulAction (𝒢 : Subgroup (GL (Fin 2) ℝ)) : SubMulAction 𝒢 (OnePoint ℝ) where
  carrier := {c | IsCusp c 𝒢}
  smul_mem' g _ hc := IsCusp.smul_of_mem hc g.property

/-- The type of cusp orbits of `𝒢`, i.e. orbits for the action of `𝒢` on its own cusps. -/
abbrev CuspOrbits (𝒢 : Subgroup (GL (Fin 2) ℝ)) :=
  MulAction.orbitRel.Quotient 𝒢 (cusps_subMulAction 𝒢)

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
      simp [MulAction.mul_smul])

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
or `0` if no such `h` exists. (We say "strict" because the width of a subgroup `Γ ⊆ SL(2, ℤ)` is
usually defined to be the smallest `h > 0` such that `±[1, h; 0, 1] ∈ Γ`, but we assume the
positive sign here.)
-/

variable {K : Type*} [Ring K]
initialize_simps_projections AddChar (toFun → apply)

/-- The map sending `x` to `[1, x; 0, 1]` (bundled as an `AddChar`). -/
@[simps apply]
def Matrix.GeneralLinearGroup.upperRightHom : AddChar K (GL (Fin 2) K) where
  toFun x := ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
  map_zero_eq_one' := by simp [Units.ext_iff, one_fin_two]
  map_add_eq_mul' a b := by simp [Units.ext_iff, add_comm]

lemma continuous_upperRightHom [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous (upperRightHom (K := K)) := by
  simp only [continuous_induced_rng, Function.comp_def, upperRightHom_apply,
    Units.embedProduct_apply, Units.inv_mk, continuous_prodMk, MulOpposite.unop_op]
  constructor <;>
  · refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;>
    fin_cases j <;>
    simp [continuous_const, continuous_neg, continuous_id']

lemma injective_upperRightHom : Function.Injective (upperRightHom (K := K)) := by
  refine (injective_iff_map_eq_zero (upperRightHom (K := K)).toAddMonoidHom).mpr ?_
  simp [Units.ext_iff, one_fin_two]


namespace Subgroup.HasDetPlusMinusOne

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {𝒢 : Subgroup (GL (Fin 2) K)} [𝒢.HasDetPlusMinusOne]

lemma isParabolic_iff_of_upperTriangular {g} (hg : g ∈ 𝒢) (hg10 : g 1 0 = 0) :
    g.IsParabolic ↔ (∃ x ≠ 0, g = upperRightHom x) ∨ (∃ x ≠ 0, g = -upperRightHom x) := by
  rw [GeneralLinearGroup.isParabolic_iff_of_upperTriangular hg10]
  constructor
  · rintro ⟨hg00, hg01⟩
    have : g 1 1 ^ 2 = 1 := by
      have : g.det = g 1 1 ^ 2 := by rw [val_det_apply, det_fin_two, hg10, hg00]; ring
      have h_det : g.det = 1 ∨ g.det = -1 := HasDetPlusMinusOne.det_eq hg
      simp only [Units.ext_iff, Units.val_one, Units.val_neg, this] at h_det
      exact h_det.resolve_right (neg_one_lt_zero.trans_le <| sq_nonneg _).ne'
    apply (sq_eq_one_iff.mp this).imp <;> intro hg11 <;> simp only [Units.ext_iff]
    · refine ⟨g 0 1, hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp [upperRightHom_apply, hg00, hg10, hg11]
    · refine ⟨-g 0 1, neg_eq_zero.not.mpr hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp [upperRightHom_apply, hg00, hg10, hg11]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;>
    simpa using hx

end Subgroup.HasDetPlusMinusOne

namespace Subgroup

/-- For a subgroup `𝒢` of `GL(2, K)`, this is the additive group of `x : K` such that
`[1, x; 0, 1] ∈ 𝒢`. -/
def strictPeriods (𝒢 : Subgroup (GL (Fin 2) K)) : AddSubgroup K :=
  (toAddSubgroup 𝒢).comap upperRightHom.toAddMonoidHom

@[simp] lemma mem_strictPeriods_iff {𝒢 : Subgroup (GL (Fin 2) K)} {x : K} :
    x ∈ 𝒢.strictPeriods ↔ upperRightHom x ∈ 𝒢 := by
  simp [strictPeriods]

@[simp] lemma strictPeriods_SL2Z : strictPeriods 𝒮ℒ = AddSubgroup.zmultiples 1 := by
  ext x
  simp only [mem_strictPeriods_iff, MonoidHom.mem_range, Units.ext_iff, mapGL_coe_matrix,
    map_apply_coe]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨g 0 1, by simpa using congr_fun₂ hg 0 1⟩, ?_⟩
  rintro ⟨m, rfl⟩
  use ModularGroup.T ^ m
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]

/-- If `𝒢` is discrete, so is its strict period subgroup. -/
instance instDiscreteTopStrictPeriods [TopologicalSpace K] [IsTopologicalRing K]
    (𝒢 : Subgroup (GL (Fin 2) K)) [hG : DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.strictPeriods := by
  let H : Set (GL (Fin 2) K) := 𝒢 ∩ (Set.range upperRightHom)
  have hH : DiscreteTopology H := hG.of_subset Set.inter_subset_left
  have : Set.MapsTo upperRightHom 𝒢.strictPeriods H := fun x hx ↦ by
    rw [SetLike.mem_coe, Subgroup.mem_strictPeriods_iff] at hx
    tauto
  exact .of_continuous_injective (continuous_upperRightHom.restrict this)
    (this.restrict_inj.mpr injective_upperRightHom.injOn)

/-- The strict width of the cusp `∞`, i.e. the `x` such that `𝒢.strictPeriods = zmultiples x`, or
0 if no such `x` exists. -/
noncomputable def strictWidthInfty (𝒢 : Subgroup (GL (Fin 2) ℝ)) : ℝ :=
  by classical exact if h : DiscreteTopology 𝒢.strictPeriods then
  |Exists.choose <| 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
      <| AddSubgroup.discrete_iff_addCyclic.mpr h|
  else 0

lemma strictWidthInfty_nonneg (𝒢 : Subgroup (GL (Fin 2) ℝ)) : 0 ≤ 𝒢.strictWidthInfty := by
  unfold strictWidthInfty; aesop

lemma strictPeriods_eq_zmultiples_strictWidthInfty {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [DiscreteTopology 𝒢.strictPeriods] :
    𝒢.strictPeriods = AddSubgroup.zmultiples 𝒢.strictWidthInfty := by
  simp [Subgroup.strictWidthInfty, dif_pos,
    Exists.choose_spec <| 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
      <| AddSubgroup.discrete_iff_addCyclic.mpr inferInstance]

lemma strictWidthInfty_mem_strictPeriods (𝒢 : Subgroup (GL (Fin 2) ℝ)) :
    𝒢.strictWidthInfty ∈ 𝒢.strictPeriods := by
  by_cases h : DiscreteTopology 𝒢.strictPeriods
  · simp [strictPeriods_eq_zmultiples_strictWidthInfty]
  · simpa only [strictWidthInfty, dif_neg h] using 𝒢.strictPeriods.zero_mem

lemma strictWidthInfty_pos_iff {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [DiscreteTopology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] :
    0 < 𝒢.strictWidthInfty ↔ IsCusp ∞ 𝒢 := by
  constructor
  · refine fun h ↦ ⟨_, mem_strictPeriods_iff.mpr 𝒢.strictWidthInfty_mem_strictPeriods, ?_, ?_⟩
    · rw [GeneralLinearGroup.isParabolic_iff_of_upperTriangular (by simp)]
      simpa using h.ne'
    · rw [smul_infty_eq_self_iff]
      simp
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

-- now repeat all the above for `𝒢.periods`, defined as `𝒢.adjoinNegOne.strictPeriods`

/-- For a subgroup `𝒢` of `GL(2, K)`, this is the additive group of `x : K` such that
`±[1, x; 0, 1] ∈ 𝒢`. -/
protected noncomputable def periods (𝒢 : Subgroup (GL (Fin 2) K)) : AddSubgroup K :=
  𝒢.adjoinNegOne.strictPeriods

lemma strictPeriods_le_periods (𝒢 : Subgroup (GL (Fin 2) K)) :
    𝒢.strictPeriods ≤ 𝒢.periods := by
  intro k
  simp only [Subgroup.periods, Subgroup.mem_strictPeriods_iff]
  apply 𝒢.le_adjoinNegOne

lemma strictPeriods_eq_periods_of_neg_one_mem
    {𝒢 : Subgroup (GL (Fin 2) K)} (h𝒢 : -1 ∈ 𝒢) :
    𝒢.strictPeriods = 𝒢.periods := by
  simp [Subgroup.periods, adjoinNegOne_eq_self_iff.mpr h𝒢]

/-- If `𝒢` is discrete, so is its period subgroup. -/
instance instDiscreteTopPeriods [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (𝒢 : Subgroup (GL (Fin 2) K)) [hG : DiscreteTopology 𝒢] : DiscreteTopology 𝒢.periods :=
  inferInstanceAs (DiscreteTopology 𝒢.adjoinNegOne.strictPeriods)

/-- The width of the cusp `∞`, i.e. the `x` such that `𝒢.periods = zmultiples x`, or 0 if no such
`x` exists. -/
noncomputable def widthInfty (𝒢 : Subgroup (GL (Fin 2) ℝ)) : ℝ :=
  𝒢.adjoinNegOne.strictWidthInfty

lemma widthInfty_nonneg (𝒢 : Subgroup (GL (Fin 2) ℝ)) : 0 ≤ 𝒢.widthInfty :=
  𝒢.adjoinNegOne.strictWidthInfty_nonneg

lemma periods_eq_zmultiples_widthInfty {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [DiscreteTopology 𝒢.periods] :
    𝒢.periods = AddSubgroup.zmultiples 𝒢.widthInfty :=
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  𝒢.adjoinNegOne.strictPeriods_eq_zmultiples_strictWidthInfty

lemma widthInfty_mem_periods (𝒢 : Subgroup (GL (Fin 2) ℝ)) : 𝒢.widthInfty ∈ 𝒢.periods :=
  𝒢.adjoinNegOne.strictWidthInfty_mem_strictPeriods

lemma widthInfty_pos_iff {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [DiscreteTopology 𝒢.periods] [𝒢.HasDetPlusMinusOne] :
    0 < 𝒢.widthInfty ↔ IsCusp ∞ 𝒢 := by
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  rw [widthInfty, strictWidthInfty_pos_iff, (commensurable_adjoinNegOne_self 𝒢).isCusp_iff]

lemma two_mul_withInfty_mem_strictPeriods (𝒢 : Subgroup (GL (Fin 2) ℝ)) :
    2 * 𝒢.widthInfty ∈ 𝒢.strictPeriods := by
  have := 𝒢.widthInfty_mem_periods
  simp only [Subgroup.periods, mem_strictPeriods_iff] at this
  rcases this with (h | h) <;>
    simpa only [neg_sq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_ofNat] using
      Subgroup.pow_mem _ h 2

lemma relIndex_strictPeriods (𝒢 : Subgroup (GL (Fin 2) K)) :
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

lemma commensurable_strictPeriods_periods (𝒢 : Subgroup (GL (Fin 2) K)) :
    𝒢.strictPeriods.Commensurable 𝒢.periods := by
  constructor
  · rcases 𝒢.relIndex_strictPeriods with h | h <;> simp [h]
  · simp [AddSubgroup.relIndex_eq_one.mpr 𝒢.strictPeriods_le_periods]

def IsRegularAtInfty (𝒢 : Subgroup (GL (Fin 2) K)) : Prop :=
    𝒢.strictPeriods = 𝒢.periods

lemma isRegularAtInfty_iff {𝒢 : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology 𝒢.periods] :
    𝒢.IsRegularAtInfty ↔ 𝒢.widthInfty ∈ 𝒢.strictPeriods := by
  refine ⟨fun h ↦ h ▸ widthInfty_mem_periods 𝒢, fun h ↦ ?_⟩
  apply 𝒢.strictPeriods_le_periods.antisymm
  rwa [periods_eq_zmultiples_widthInfty, AddSubgroup.zmultiples_le]

lemma isRegularAtInfty_of_neg_one_mem
    {𝒢 : Subgroup (GL (Fin 2) K)} (h𝒢 : -1 ∈ 𝒢) : 𝒢.IsRegularAtInfty :=
  𝒢.strictPeriods_eq_periods_of_neg_one_mem h𝒢

end Subgroup

end Width
