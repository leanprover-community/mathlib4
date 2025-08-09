/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Boundedness and vanishing at cusps

We define the notions of "bounded at c" and "vanishing at c" for functions on `ℍ`, where `c` is
an element of `OnePoint ℝ`.
-/

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
  simp only [norm_σ, ModularForm.slash_def, denom, hg, Complex.ofReal_zero, zero_mul, zero_add,
    norm_mul, mul_assoc]
  simpa only [mul_comm (‖f _‖)] using
    (hf.comp_tendsto (tendsto_smul_atImInfty hg)).const_mul_left _

end UpperHalfPlane

namespace OnePoint

variable (c : OnePoint ℝ) (f : ℍ → ℂ) (k : ℤ)

/-- We say `f` is bounded at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
bounded at `∞`. -/
def IsBoundedAt : Prop :=
    ∀ (g : GL (Fin 2) ℝ), g • ∞ = c → IsBoundedAtImInfty (f ∣[k] g)

/-- We say `f` is zero at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
zero at `∞`. -/
def IsZeroAt : Prop :=
    ∀ (g : GL (Fin 2) ℝ), g • ∞ = c → IsZeroAtImInfty (f ∣[k] g)

variable {c f k} {g : GL (Fin 2) ℝ}

lemma IsBoundedAt.slash :
    IsBoundedAt c (f ∣[k] g) k ↔ IsBoundedAt (g • c) f k := by
  rw [IsBoundedAt, IsBoundedAt, (Equiv.mulLeft g).forall_congr_left]
  simp [-smul_infty_eq_ite, MulAction.mul_smul, inv_smul_eq_iff, ← SlashAction.slash_mul]

lemma IsZeroAt.slash :
    IsZeroAt c (f ∣[k] g) k ↔ IsZeroAt (g • c) f k := by
  rw [IsZeroAt, IsZeroAt, (Equiv.mulLeft g).forall_congr_left]
  simp [-smul_infty_eq_ite, MulAction.mul_smul, inv_smul_eq_iff, ← SlashAction.slash_mul]

lemma IsBoundedAt.add {f' : ℍ → ℂ} (hf : IsBoundedAt c f k) (hf' : IsBoundedAt c f' k) :
    IsBoundedAt c (f + f') k :=
  fun g hg ↦ by simpa using (hf g hg).add (hf' g hg)

lemma IsZeroAt.add {f' : ℍ → ℂ} (hf : IsZeroAt c f k) (hf' : IsZeroAt c f' k) :
    IsZeroAt c (f + f') k :=
  fun g hg ↦ by simpa using (hf g hg).add (hf' g hg)

lemma isBoundedAt_infty : IsBoundedAt ∞ f k ↔ IsBoundedAtImInfty f := by
  constructor
  · intro h
    simpa using h 1 (by simp)
  · exact fun h _ hg ↦ h.slash _ (smul_infty_eq_self_iff.mp hg)

lemma isZeroAt_infty : IsZeroAt ∞ f k ↔ IsZeroAtImInfty f := by
  constructor
  · intro h
    simpa using h 1 (by simp)
  · exact fun h _ hg ↦ h.slash _ (smul_infty_eq_self_iff.mp hg)

/-- To check that `f` is bounded at `c`, it suffices for `f ∣[k] g` to be bounded at `∞` for any
single `g` with `g • ∞ = c`. -/
lemma isBoundedAt_iff (hg : g • ∞ = c) :
    IsBoundedAt c f k ↔ IsBoundedAtImInfty (f ∣[k] g) :=
  ⟨fun hc ↦ hc g hg , by simp only [← hg, ← IsBoundedAt.slash, isBoundedAt_infty, imp_self]⟩

/-- To check that `f` is zero at `c`, it suffices for `f ∣[k] g` to be zero at `∞` for any
single `g` with `g • ∞ = c`. -/
lemma isZeroAt_iff (hg : g • ∞ = c) :
    IsZeroAt c f k ↔ IsZeroAtImInfty (f ∣[k] g) :=
  ⟨fun hc ↦ hc g hg , by simp only [← hg, ← IsZeroAt.slash, isZeroAt_infty, imp_self]⟩

section SL2Z

variable {c : OnePoint ℝ} {f : ℍ → ℂ} {k : ℤ}

lemma isBoundedAt_iff_exists_SL2Z (hc : IsCusp c (mapGL (R := ℤ) ℝ).range) :
    IsBoundedAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c ∧ IsBoundedAtImInfty (f ∣[k] γ) := by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa only [← IsBoundedAt.slash, isBoundedAt_infty] using fun hfc ↦ ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa only [← IsBoundedAt.slash, isBoundedAt_infty] using b

lemma isZeroAt_iff_exists_SL2Z (hc : IsCusp c (mapGL (R := ℤ) ℝ).range) :
    IsZeroAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c ∧ IsZeroAtImInfty (f ∣[k] γ) := by
  constructor
  · obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    simpa only [← IsZeroAt.slash, isZeroAt_infty] using fun hfc ↦ ⟨γ, rfl, hfc⟩
  · rintro ⟨γ, rfl, b⟩
    simpa only [← IsZeroAt.slash, isZeroAt_infty] using b

lemma isBoundedAt_iff_forall_SL2Z (hc : IsCusp c (mapGL (R := ℤ) ℝ).range) :
    IsBoundedAt c f k ↔ ∀ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c → IsBoundedAtImInfty (f ∣[k] γ) := by
  refine ⟨fun hc _ hγ ↦ by simpa using hc _ hγ, fun h ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa only [← IsBoundedAt.slash, isBoundedAt_infty] using h γ rfl

lemma isZeroAt_iff_forall_SL2Z (hc : IsCusp c (mapGL (R := ℤ) ℝ).range) :
    IsZeroAt c f k ↔ ∀ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c → IsZeroAtImInfty (f ∣[k] γ) := by
  refine ⟨fun hc _ hγ ↦ by simpa using hc _ hγ, fun h ↦ ?_⟩
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  simpa only [← IsZeroAt.slash, isZeroAt_infty] using h γ rfl

end SL2Z

end OnePoint
