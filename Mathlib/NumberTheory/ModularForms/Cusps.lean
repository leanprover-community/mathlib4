/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Cusps

We define the notions of "bounded at c" and "vanishing at c" for functions on `ℍ`, where `c` is
an element of `OnePoint ℚ`. We also define cusps of a subgroup, as `Γ`-orbits on  `OnePoint ℚ`.
-/

open Matrix SpecialLinearGroup UpperHalfPlane Filter

open scoped MatrixGroups LinearAlgebra.Projectivization OnePoint ModularForm

/-- The modular group `SL(2, A)` acts transitively on `OnePoint K`, if `A` is a PID whose fraction
field is `K`. (This includes the case `A = ℤ`, `K = ℚ`.) -/
lemma OnePoint.exists_mem_SL2 {K : Type*} (A : Type*) [CommRing A] [IsDomain A] [Field K]
    [DecidableEq K] [Algebra A K] [IsFractionRing A K] [IsPrincipalIdealRing A] (c : OnePoint K) :
    ∃ g : SL(2, A), (mapGL K g) • ∞ = c := by
  cases c with
  | infty => use 1; simp
  | coe q =>
    obtain ⟨g, hg0, hg1⟩ := (IsFractionRing.num_den_reduced A q).isCoprime.exists_SL2_col 0
    use g
    have : mapGL K g 1 0 ≠ 0 := by simp [hg1]
    simp [hg0, hg1]

section IsBoundedAtImInfty

lemma UpperHalfPlane.IsZeroAtImInfty.slash {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) {f : ℍ → ℂ}
    (hf : IsZeroAtImInfty f) (k : ℤ) : IsZeroAtImInfty (f ∣[k] g) := by
  simp only [IsZeroAtImInfty, ZeroAtFilter] at hf ⊢
  rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  have (z : ℂ) : ‖σ g z‖ = ‖z‖ := by simp only [σ]; split_ifs <;> simp
  simpa [this, ModularForm.slash_def, denom, hg, mul_assoc]
    using (hf.comp <| tendsto_smul_atImInfty hg).mul_const _

lemma UpperHalfPlane.IsBoundedAtImInfty.slash {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) {f : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) (k : ℤ) : IsBoundedAtImInfty (f ∣[k] g) := by
  simp only [IsBoundedAtImInfty, BoundedAtFilter] at hf ⊢
  rw [← Asymptotics.isBigO_norm_left] at hf ⊢
  have (z : ℂ) : ‖σ g z‖ = ‖z‖ := by simp only [σ]; split_ifs <;> simp
  simp only [this, ModularForm.slash_def, denom, hg, Complex.ofReal_zero, zero_mul, zero_add,
    norm_mul, mul_assoc]
  simpa only [mul_comm (‖f _‖)] using
    (hf.comp_tendsto (tendsto_smul_atImInfty hg)).const_mul_left _

end IsBoundedAtImInfty

section IsBoundedAt

variable (c : OnePoint ℚ) (f : ℍ → ℂ) (k : ℤ)

/-- We say `f` is bounded at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
bounded at `∞`. -/
def OnePoint.IsBoundedAt : Prop :=
    ∀ (g : GL (Fin 2) ℚ), g • ∞ = c → IsBoundedAtImInfty (f ∣[k] (g.map <| algebraMap ℚ ℝ))

/-- We say `f` is zero at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
zero at `∞`. -/
def OnePoint.IsZeroAt : Prop :=
    ∀ (g : GL (Fin 2) ℚ), g • ∞ = c → IsZeroAtImInfty (f ∣[k] (g.map <| algebraMap ℚ ℝ))

variable {c f k} {γ : SL(2, ℤ)} {g : GL (Fin 2) ℚ}

lemma OnePoint.isBoundedAt_iff_forall_GL2Q :
    IsBoundedAt c f k ↔ ∀ (g : GL (Fin 2) ℚ), g • ∞ = c
      → IsBoundedAtImInfty (f ∣[k] (g.map <| algebraMap ℚ ℝ)) :=
  Iff.rfl

lemma OnePoint.isZeroAt_iff_forall_GL2Q :
    IsZeroAt c f k ↔ ∀ (g : GL (Fin 2) ℚ), g • ∞ = c
      → IsZeroAtImInfty (f ∣[k] (g.map <| algebraMap ℚ ℝ)) :=
  Iff.rfl

/-- Tedious lemma: if `γ ∈ SL(2, ℤ)` and `g ∈ GL(2, ℝ)` both map . -/
private lemma OnePoint.SL2Z_trans_eq_GL2Z_trans
    (hγ : (mapGL ℚ) γ • ∞ = c) (hg : g • ∞ = c) :
    ((mapGL ℝ γ)⁻¹ * (g.map (algebraMap ℚ ℝ))) 1 0 = 0 := by
  have h1 : g.map (algebraMap ℚ ℝ) • ∞ = (g • ∞).map (algebraMap ℚ ℝ) := by
    by_cases h : g 1 0 = 0 <;> simp [h]
  have h2 : mapGL ℝ γ • ∞ = (mapGL ℚ γ • ∞).map (algebraMap ℚ ℝ) := by
    by_cases h : γ 1 0 = 0 <;> simp [h]
  rw [← OnePoint.smul_infty_eq_iff, MulAction.mul_smul, inv_smul_eq_iff, h1, h2, hg, hγ]

lemma OnePoint.isBoundedAt_iff_exists_SL2Z :
    IsBoundedAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℚ γ • ∞ = c ∧ IsBoundedAtImInfty (f ∣[k] γ) := by
  refine ⟨fun h ↦ match c.exists_mem_SL2 ℤ with | ⟨γ, hγ⟩ => ⟨γ, hγ, by simpa using h _ hγ⟩, ?_⟩
  rintro ⟨γ, hγ, hf⟩ g hg
  replace hf : IsBoundedAtImInfty (f ∣[k] (mapGL ℝ γ)) := by
    simpa only [ModularForm.SL_slash] using hf
  simpa [← SlashAction.slash_mul] using hf.slash (c.SL2Z_trans_eq_GL2Z_trans hγ hg) k

lemma OnePoint.isZeroAt_iff_exists_SL2Z :
    IsZeroAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℚ γ • ∞ = c ∧ IsZeroAtImInfty (f ∣[k] γ) := by
  refine ⟨fun h ↦ match c.exists_mem_SL2 ℤ with | ⟨γ, hγ⟩ => ⟨γ, hγ, by simpa using h _ hγ⟩, ?_⟩
  rintro ⟨γ, hγ, hf⟩ g hg
  replace hf : IsZeroAtImInfty (f ∣[k] (mapGL ℝ γ)) := by
    simpa only [ModularForm.SL_slash] using hf
  simpa [← SlashAction.slash_mul] using hf.slash (c.SL2Z_trans_eq_GL2Z_trans hγ hg) k

lemma OnePoint.isBoundedAt_iff_forall_SL2Z :
    IsBoundedAt c f k ↔ ∀ γ : SL(2, ℤ), (mapGL ℚ γ) • ∞ = c → IsBoundedAtImInfty (f ∣[k] γ) :=
  ⟨fun hc _ hγ ↦ by simpa using hc _ hγ, fun hc ↦ match c.exists_mem_SL2 ℤ with
    | ⟨γ, hγ⟩ => c.isBoundedAt_iff_exists_SL2Z.mpr ⟨γ, hγ, hc _ hγ⟩⟩

lemma OnePoint.isZeroAt_iff_forall_SL2Z :
    IsZeroAt c f k ↔ ∀ γ : SL(2, ℤ), (mapGL ℚ γ) • ∞ = c → IsZeroAtImInfty (f ∣[k] γ) :=
  ⟨fun hc _ hγ ↦ by simpa using hc _ hγ, fun hc ↦ match c.exists_mem_SL2 ℤ with
    | ⟨γ, hγ⟩ => c.isZeroAt_iff_exists_SL2Z.mpr ⟨γ, hγ, hc _ hγ⟩⟩

lemma OnePoint.IsBoundedAt.slash :
    IsBoundedAt c (f ∣[k] (g.map <| algebraMap ℚ ℝ)) k ↔ IsBoundedAt (g • c) f k := by
  simp only [isBoundedAt_iff_forall_GL2Q]
  rw [(Equiv.mulLeft g).forall_congr_left]
  simp [-smul_infty_eq_ite, MulAction.mul_smul, inv_smul_eq_iff, ← SlashAction.slash_mul]

lemma OnePoint.IsZeroAt.slash :
    IsZeroAt c (f ∣[k] (g.map <| algebraMap ℚ ℝ)) k ↔ IsZeroAt (g • c) f k := by
  simp only [isZeroAt_iff_forall_GL2Q]
  rw [(Equiv.mulLeft g).forall_congr_left]
  simp [-smul_infty_eq_ite, MulAction.mul_smul, inv_smul_eq_iff, ← SlashAction.slash_mul]

end IsBoundedAt

section Cusps

/-- The type of cusps of `Γ`, i.e. orbits for the action of `Γ` on `ℚ ∪ ∞`. -/
def Cusp (Γ : Subgroup SL(2, ℤ)) := MulAction.orbitRel.Quotient (Γ.map (mapGL ℚ)) (OnePoint ℚ)

/-- Surjection from `SL(2, ℤ) / Γ` to cusps of `Γ`. Mostly useful for showing that `Cusp Γ` is
finite for finite-index subgroups. -/
-- XXX TODO: Why does this complain if not flagged as `noncomputable`? It looks pretty computable
-- to me.
noncomputable def cosetToCusp (Γ : Subgroup SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ → Cusp Γ :=
  Quotient.lift fun g ↦ ⟦mapGL ℚ g⁻¹ • ∞⟧ (by
    intro a b hab
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    use ⟨_, Γ.mem_map_of_mem _ (QuotientGroup.leftRel_apply.mp hab)⟩
    rw [Subgroup.smul_def, Subgroup.coe_mk, ← MulAction.mul_smul, ← map_mul, mul_inv_cancel_right])

lemma cosetToCusp_apply (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    cosetToCusp Γ ⟦g⟧ = ⟦mapGL ℚ g⁻¹ • ∞⟧ :=
  rfl

lemma surjective_cosetToCusp (Γ : Subgroup SL(2, ℤ)) : (cosetToCusp Γ).Surjective := by
  rintro ⟨c⟩
  obtain ⟨g, rfl⟩ := c.exists_mem_SL2 ℤ
  use ⟦g⁻¹⟧
  rw [cosetToCusp_apply, inv_inv, Quotient.mk]

/-- A finite-index subgroup has finitely many cusps. -/
instance instFiniteOfFiniteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : Finite (Cusp Γ) :=
  .of_surjective _ (surjective_cosetToCusp Γ)

end Cusps
