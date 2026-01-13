/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth dependence on initial condition
-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace SmoothFlow

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E]

/--
Precomposition with a projection from `ℝ` to `Icc tmin tmax`, provided with `t₀` in the non-empty
interval.

This helps us work with the space of continuous curves `C(Icc tmin tmax, E)`. We have to use
`C(Icc tmin tmax, E)` instead of the junk value pattern on `ℝ → E` because we need the space of
curves to be a complete normed space.
-/
def compProj {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) : ℝ → E :=
  fun t ↦ α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t)

@[continuity, fun_prop]
lemma continuous_compProj {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    Continuous (compProj t₀ α) :=
  α.continuous.comp continuous_projIcc

variable [NormedSpace ℝ E]

/--
The integral
$$\int_{t₀}^t g(\alpha(\tau))(d\alpha_1(\tau),\cdots,d\alpha_n(\tau)) \,d\tau,$$
where `g : x → E [×n]→L[ℝ] E` has the same type as the `n`-th iterated derivative of `f : E → E`.
This is defined so that its derivative with respect to `α` will yield the same integral expression,
but with `n` replaced by `n + 1` and `g` replaced by its derivative.
-/
def integralFun {n : ℕ} (g : E → E [×n]→L[ℝ] E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) (dα : Fin n → C(Icc tmin tmax, E)) (t : Icc tmin tmax) : E :=
  ∫ τ in t₀..t, g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)

lemma integralFun_def {n : ℕ} {g : E → E [×n]→L[ℝ] E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {α : C(Icc tmin tmax, E)} {dα : Fin n → C(Icc tmin tmax, E)} :
    integralFun g t₀ α dα =
      fun t : Icc tmin tmax ↦ ∫ τ in t₀..t, g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ) :=
  rfl

variable [CompleteSpace E]

-- consider new lemma for `MapsTo α univ u ↔ range α ⊆ u`
lemma continuous_integralFun {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) :
    Continuous (integralFun g t₀ α dα) := by
  classical

  -- abbreviate the projected curves
  let ϕ : ℝ → E := compProj t₀ α
  let ψ : Fin n → ℝ → E := fun i => compProj t₀ (dα i)

  have hϕ : Continuous ϕ := by
    simpa [ϕ] using (continuous_compProj (t₀ := t₀) (α := α))

  have hψ : ∀ i, Continuous (ψ i) := by
    intro i
    simpa [ψ] using (continuous_compProj (t₀ := t₀) (α := dα i))

  -- `ϕ τ ∈ u` for all `τ`, using `hα` and the fact `projIcc ... τ ∈ Icc`
  have hϕ_mem : ∀ τ, ϕ τ ∈ u := by
    intro τ
    simpa [ϕ, compProj] using
      (hα (by
        trivial :
          projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) τ ∈ (Set.univ : Set (Icc tmin tmax))))

  -- continuity of τ ↦ g (ϕ τ)
  have hgϕ : Continuous fun τ => g (ϕ τ) := by
    refine continuous_iff_continuousAt.2 ?_
    intro τ
    have hx : ϕ τ ∈ u := hϕ_mem τ
    have hnhds : u ∈ 𝓝 (ϕ τ) := hu.mem_nhds hx
    exact (hg.continuousAt hnhds).comp hϕ.continuousAt

  -- continuity of τ ↦ (i ↦ ψ i τ)
  have hvec : Continuous fun τ => (fun i => ψ i τ) := by
    refine continuous_pi ?_
    intro i
    simpa [ψ] using (hψ i)

  -- evaluation map (m, v) ↦ m v is continuous for continuous multilinear maps
  have happ :
      Continuous (fun p : (E [×n]→L[ℝ] E) × (Fin n → E) => p.1 p.2) := by
    simpa using
      (ContinuousEval.continuous_eval :
        Continuous (fun p : (E [×n]→L[ℝ] E) × (Fin n → E) => p.1 p.2))

  -- integrand is continuous
  have hf : Continuous (fun τ => g (ϕ τ) (fun i => ψ i τ)) := by
    have hpair : Continuous (fun τ => (g (ϕ τ), (fun i => ψ i τ))) :=
      hgϕ.prodMk hvec
    simpa using happ.comp hpair

  -- continuity of t ↦ ∫ τ in t₀..t, f τ as a real-variable function
  have hIntReal :
      Continuous (fun t : ℝ =>
        ∫ τ in (t₀ : ℝ)..t, g (ϕ τ) (fun i => ψ i τ)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    -- strict derivative ⇒ continuous
    exact (hf.integral_hasStrictDerivAt (t₀ : ℝ) t).continuousAt

  -- restrict to t : Icc tmin tmax
  simpa [integralFun, ϕ, ψ] using hIntReal.comp continuous_subtype_val

def integralCM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) where
  toFun := integralFun g t₀ α dα
  continuous_toFun := continuous_integralFun hg hu t₀ hα dα



end

end SmoothFlow
