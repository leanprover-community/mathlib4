/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.RCLike.Basic
import Mathlib.GroupTheory.Commensurable
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# Cusps

We define the cusps of a subgroup of `GL(2, ℝ)` as the fixed points of parabolic elements.
-/

open Matrix SpecialLinearGroup Filter Polynomial OnePoint

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
    exact ⟨g, by simp [hg0, hg1]⟩

end OnePoint

section IsCusp

/-- The *cusps* of a subgroup of `GL(2, ℝ)` are the fixed points of parabolic elements of `g`. -/
def IsCusp (c : OnePoint ℝ) (Γ : Subgroup (GL (Fin 2) ℝ)) : Prop :=
    ∃ g ∈ Γ, g.IsParabolic ∧ g • c = c

open Pointwise in
lemma IsCusp.smul {c : OnePoint ℝ} {Γ : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c Γ)
    (g : GL (Fin 2) ℝ) : IsCusp (g • c) (ConjAct.toConjAct g • Γ) := by
  obtain ⟨p, hpΓ, hpp, hpc⟩ := hc
  refine ⟨_, Γ.smul_mem_pointwise_smul _ _ hpΓ, ?_, ?_⟩
  · simpa only [ConjAct.toConjAct_smul, GeneralLinearGroup.IsParabolic, Units.val_mul,
      isParabolic_conj_iff] using hpp
  · simp [ConjAct.toConjAct_smul, MulAction.mul_smul, hpc]

lemma IsCusp.smul_of_mem {c : OnePoint ℝ} {Γ : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c Γ)
    {g : GL (Fin 2) ℝ} (hg : g ∈ Γ) : IsCusp (g • c) Γ := by
  convert hc.smul g
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv, Subgroup.mul_mem_cancel_right _ hg,
    Subgroup.mul_mem_cancel_left _ (inv_mem hg)]

lemma isCusp_finiteIndex_iff
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hΓ : Γ' ≤ Γ) (hΓ' : Γ'.relindex Γ ≠ 0) (c : OnePoint ℝ) :
    IsCusp c Γ' ↔ IsCusp c Γ := by
  refine ⟨fun ⟨g, hg, hgp, hgc⟩ ↦ ⟨g, hΓ hg, hgp, hgc⟩, fun ⟨g, hg, hgp, hgc⟩ ↦ ?_⟩
  obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_relindex_ne_zero hΓ' hg
  refine ⟨g ^ n, (Subgroup.mem_inf.mpr hgn).1, hgp.pow hn.ne', ?_⟩
  rw [Nat.pos_iff_ne_zero] at hn
  rwa [(hgp.pow hn).smul_eq_self_iff, hgp.parabolicFixedPoint_pow hn, ← hgp.smul_eq_self_iff]

lemma Commensurable.isCusp_iff
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hΓ : Commensurable Γ Γ') {c : OnePoint ℝ} :
    IsCusp c Γ ↔ IsCusp c Γ' := by
  rw [← isCusp_finiteIndex_iff (inf_le_left ..), isCusp_finiteIndex_iff (inf_le_right ..)]
  · simpa [Subgroup.inf_relindex_right] using hΓ.1
  · simpa [Subgroup.inf_relindex_left] using hΓ.2

/-- The cusps of `SL(2, ℤ)` are precisely the elements of `ℙ¹(ℚ)`. -/
lemma isCusp_SL2Z_iff {c : OnePoint ℝ} :
    IsCusp c (mapGL (R := ℤ) ℝ).range ↔ c ∈ Set.range (OnePoint.map Rat.cast) := by
  constructor
  · rintro ⟨-, ⟨γ, rfl⟩, hgp, hgc⟩
    simpa only [hgp.smul_eq_self_iff.mp hgc] using ⟨(mapGL ℚ γ).parabolicFixedPoint,
      by simp [GeneralLinearGroup.parabolicFixedPoint, apply_ite]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := c.exists_mem_SL2 ℤ
    refine ⟨_, ⟨a * ModularGroup.T * a⁻¹, rfl⟩, ?_, ?_⟩
    · simp only [map_mul, map_inv, GeneralLinearGroup.IsParabolic, Units.val_mul,
         isParabolic_conj_iff]
      refine ⟨fun ⟨a, ha⟩ ↦ zero_ne_one' ℝ (by simpa [ModularGroup.T] using congr_fun₂ ha 0 1), ?_⟩
      simp [disc, trace_fin_two, det_fin_two, ModularGroup.T]
      norm_num
    · simp [-smul_infty_eq_ite, ← Rat.coe_castHom, OnePoint.map_smul, MulAction.mul_smul,
        a.map_mapGL (by rfl : _ = Rat.castHom ℝ),
        smul_infty_eq_self_iff.mpr (show mapGL ℝ ModularGroup.T 1 0 = 0 by simp [ModularGroup.T])]

/-- The cusps of `SL(2, ℤ)` are precisely the `SL(2, ℤ)` orbit of `∞`. -/
lemma isCusp_SL2Z_iff' {c : OnePoint ℝ} :
    IsCusp c (mapGL (R := ℤ) ℝ).range ↔ ∃ γ : SL(2, ℤ), c = mapGL ℝ γ • ∞ := by
  rw [isCusp_SL2Z_iff]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨γ, rfl⟩ := c.exists_mem_SL2 ℤ
    refine ⟨γ, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty, γ.map_mapGL (by rfl)]
  · rintro ⟨γ, rfl⟩
    refine ⟨mapGL ℚ γ • ∞, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty, γ.map_mapGL (by rfl)]

/-- The cusps of any arithmetic subgroup are the same as those of `SL(2, ℤ)`. -/
lemma IsArith.isCusp_iff_isCusp_SL2Z (Γ : Subgroup (GL (Fin 2) ℝ)) [IsArith Γ] {c : OnePoint ℝ} :
    IsCusp c Γ ↔ IsCusp c (mapGL (R := ℤ) ℝ).range :=
  IsArith.is_comm.isCusp_iff

end IsCusp

section CuspOrbits

/-- The action of `Γ` on its own cusps. -/
def cusps_subMulAction (Γ : Subgroup (GL (Fin 2) ℝ)) : SubMulAction Γ (OnePoint ℝ) where
  carrier := {c | IsCusp c Γ}
  smul_mem' g _ hc := IsCusp.smul_of_mem hc g.property

/-- The type of cusps of `Γ`, i.e. orbits for the action of `Γ` its own cusps. -/
@[reducible]
def CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)) :=
  MulAction.orbitRel.Quotient Γ (cusps_subMulAction Γ)

/-- Surjection from `SL(2, ℤ) / (Γ ⊓ SL(2, ℤ))` to cusps of `Γ`. Mostly useful for showing that
`CuspOrbits Γ` is finite for arithmetic subgroups. -/
noncomputable def cosetToCuspOrbit
    (Γ : Subgroup <| GL (Fin 2) ℝ) [IsArith Γ] : SL(2, ℤ) ⧸ (Γ.comap <| mapGL ℝ) → CuspOrbits Γ :=
  Quotient.lift
    (fun g ↦ ⟦⟨mapGL ℝ g⁻¹ • ∞,
      (IsArith.isCusp_iff_isCusp_SL2Z Γ).mpr <| isCusp_SL2Z_iff.mpr ⟨mapGL ℚ g⁻¹ • ∞, by
        rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty, map_mapGL _ (by rfl)]⟩⟩⟧)
    (fun a b hab ↦ by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hab
      refine Quotient.eq.mpr ⟨⟨_, hab⟩, ?_⟩
      simp [-smul_infty_eq_ite, MulAction.mul_smul])

lemma surjective_cosetToCuspOrbit (Γ : Subgroup <| GL (Fin 2) ℝ) [IsArith Γ] :
    (cosetToCuspOrbit Γ).Surjective := by
  rintro ⟨c, (hc : IsCusp c _)⟩
  rw [IsArith.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
  obtain ⟨γ, rfl⟩ := hc
  use ⟦γ⁻¹⟧
  simp only [cosetToCuspOrbit, Quotient.lift_mk, inv_inv]
  rfl

/-- An arithmetic subgroup has finitely many cusps. -/
instance (Γ : Subgroup (GL (Fin 2) ℝ)) [IsArith Γ] : Finite (CuspOrbits Γ) :=
  .of_surjective _ (surjective_cosetToCuspOrbit Γ)

end CuspOrbits
