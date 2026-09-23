/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Boundedness and vanishing at cusps

We define the notions of "bounded at c" and "vanishing at c" for functions on `ℍ`, where `c` is
an element of `OnePoint ℝ`.
-/

@[expose] public section

open Matrix SpecialLinearGroup UpperHalfPlane Filter Polynomial OnePoint

open scoped MatrixGroups LinearAlgebra.Projectivization ModularForm

namespace UpperHalfPlane

variable {g : GL (Fin 2) ℝ} {f : ℍ → ℂ} (k : ℤ)

lemma IsZeroAtImInfty.slash (hg : g 1 0 = 0) (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (f ∣[k] g) := by
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  simpa [ModularForm.slash_def, denom, hg, mul_assoc]
    using (hf.comp <| tendsto_smul_atImInfty hg).mul_const _

lemma IsBoundedAtImInfty.slash (hg : g 1 0 = 0) (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (f ∣[k] g) := by
  rw [IsBoundedAtImInfty, BoundedAtFilter, ← Asymptotics.isBigO_norm_left] at hf ⊢
  suffices (fun x ↦ (‖g.det.val ^ (k - 1)‖ * ‖g 1 1 ^ (-k)‖) * ‖f (g • x)‖) =O[atImInfty] 1 by
    simpa [ModularForm.slash_def, denom, hg, mul_assoc, mul_comm ‖f _‖]
  apply (hf.comp_tendsto (tendsto_smul_atImInfty hg)).const_mul_left

end UpperHalfPlane

namespace OnePoint

variable (c : OnePoint ℝ) (f : ℍ → ℂ) (k : ℤ)

/-- We say `f` is bounded at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
bounded at `∞`. -/
def IsBoundedAt : Prop := ∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsBoundedAtImInfty (f ∣[k] g)

/-- We say `f` is zero at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
zero at `∞`. -/
def IsZeroAt : Prop := ∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsZeroAtImInfty (f ∣[k] g)

variable {c f k} {g : GL (Fin 2) ℝ}

lemma IsBoundedAt.smul_iff : IsBoundedAt (g • c) f k ↔ IsBoundedAt c (f ∣[k] g) k := by
  rw [IsBoundedAt, IsBoundedAt, (Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

lemma IsZeroAt.smul_iff : IsZeroAt (g • c) f k ↔ IsZeroAt c (f ∣[k] g) k := by
  rw [IsZeroAt, IsZeroAt, (Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

lemma IsBoundedAt.add {f' : ℍ → ℂ} (hf : IsBoundedAt c f k) (hf' : IsBoundedAt c f' k) :
    IsBoundedAt c (f + f') k :=
  fun g hg ↦ by simpa using (hf g hg).add (hf' g hg)

lemma IsZeroAt.add {f' : ℍ → ℂ} (hf : IsZeroAt c f k) (hf' : IsZeroAt c f' k) :
    IsZeroAt c (f + f') k :=
  fun g hg ↦ by simpa using (hf g hg).add (hf' g hg)

lemma isBoundedAt_infty_iff : IsBoundedAt ∞ f k ↔ IsBoundedAtImInfty f :=
  ⟨fun h ↦ by simpa using h 1 (by simp), fun h _ hg ↦ h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

lemma isZeroAt_infty_iff : IsZeroAt ∞ f k ↔ IsZeroAtImInfty f :=
  ⟨fun h ↦ by simpa using h 1 (by simp), fun h _ hg ↦ h.slash _ (smul_infty_eq_self_iff.mp hg)⟩

/-- To check that `f` is bounded at `c`, it suffices for `f ∣[k] g` to be bounded at `∞` for any
single `g` with `g • ∞ = c`. -/
lemma isBoundedAt_iff (hg : g • ∞ = c) : IsBoundedAt c f k ↔ IsBoundedAtImInfty (f ∣[k] g) :=
  ⟨fun hc ↦ hc g hg , by simp [← hg, IsBoundedAt.smul_iff, isBoundedAt_infty_iff]⟩

/-- To check that `f` is zero at `c`, it suffices for `f ∣[k] g` to be zero at `∞` for any
single `g` with `g • ∞ = c`. -/
lemma isZeroAt_iff (hg : g • ∞ = c) : IsZeroAt c f k ↔ IsZeroAtImInfty (f ∣[k] g) :=
  ⟨fun hc ↦ hc g hg , by simp [← hg, IsZeroAt.smul_iff, isZeroAt_infty_iff]⟩

section SL2Z

variable {c : OnePoint ℝ} {f : ℍ → ℂ} {k : ℤ}

lemma isBoundedAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsBoundedAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c ∧ IsBoundedAtImInfty (f ∣[k] γ) := by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using fun hfc ↦ ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using b

lemma isZeroAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsZeroAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c ∧ IsZeroAtImInfty (f ∣[k] γ) := by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using fun hfc ↦ ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using b

lemma isBoundedAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsBoundedAt c f k ↔ ∀ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c → IsBoundedAtImInfty (f ∣[k] γ) := by
  refine ⟨fun hc _ hγ ↦ by simpa using hc _ hγ, fun h ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsBoundedAt.smul_iff, isBoundedAt_infty_iff] using h γ rfl

lemma isZeroAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsZeroAt c f k ↔ ∀ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c → IsZeroAtImInfty (f ∣[k] γ) := by
  refine ⟨fun hc _ hγ ↦ by simpa using hc _ hγ, fun h ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa [IsZeroAt.smul_iff, isZeroAt_infty_iff] using h γ rfl

end SL2Z

end OnePoint
