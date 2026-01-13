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

/--
The integrand is continuous in the integration variable.
-/
lemma continuous_integrand {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) :
    Continuous (fun τ ↦ g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)) := by
  -- projected α is continuous
  have hφ : Continuous (compProj t₀ α) := by
    simpa using (continuous_compProj (t₀ := t₀) (α := α))

  -- projected α lands in u everywhere
  have hφ_mem : ∀ τ, compProj t₀ α τ ∈ u := by
    intro τ
    -- `projIcc ... τ ∈ univ`, then apply `hα`
    simpa [compProj] using
      (hα (by
        trivial :
          projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) τ ∈ (Set.univ : Set (Icc tmin tmax))))

  -- continuity of τ ↦ g (compProj t₀ α τ)
  have hgφ : Continuous fun τ => g (compProj t₀ α τ) := by
    refine continuous_iff_continuousAt.2 ?_
    intro τ
    have hx : compProj t₀ α τ ∈ u := hφ_mem τ
    have hnhds : u ∈ 𝓝 (compProj t₀ α τ) := hu.mem_nhds hx
    exact (hg.continuousAt hnhds).comp hφ.continuousAt

  -- continuity of τ ↦ (j ↦ compProj t₀ (m' j) τ)
  have hvec : Continuous (fun τ => (fun j => compProj t₀ (dα j) τ)) := by
    refine continuous_pi ?_
    intro j
    simpa using (continuous_compProj (t₀ := t₀) (α := dα j))

  -- evaluation map (M, v) ↦ M v is continuous
  have happ :
      Continuous (fun p : (E [×n]→L[ℝ] E) × (Fin n → E) => p.1 p.2) := by
    simpa using
      (continuous_eval :
        Continuous (fun p : (E [×n]→L[ℝ] E) × (Fin n → E) => p.1 p.2))

  have hpair : Continuous (fun τ => (g (compProj t₀ α τ), (fun j => compProj t₀ (dα j) τ))) := by
    simpa using (hgφ.prodMk hvec)

  simpa using happ.comp hpair

variable [CompleteSpace E]

-- consider new lemma for `MapsTo α univ u ↔ range α ⊆ u`
lemma continuous_integralFun {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) :
    Continuous (integralFun g t₀ α dα) := by
  apply Continuous.comp
    (g := fun t ↦ ∫ τ in t₀..t, g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)) _
    continuous_subtype_val
  rw [continuous_iff_continuousAt]
  exact fun t ↦ ((continuous_integrand hg hu t₀ hα dα).integral_hasStrictDerivAt t₀ t).continuousAt

/--
The integral as a function from continuous curves to continuous curves, enabling us to take
derivatives with respect to the curve
-/
def integralCM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) where
  toFun := integralFun g t₀ α dα
  continuous_toFun := continuous_integralFun hg hu t₀ hα dα

-- rename `x`, `y`
lemma integralCM_update_add {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n)
    (x y : C(Icc tmin tmax, E)) :
    integralCM hg hu t₀ hα (update dα i (x + y)) =
      integralCM hg hu t₀ hα (update dα i x) + integralCM hg hu t₀ hα (update dα i y) := by
  ext t
  -- unfold the bundled maps, reduce to a statement about integrals
  rw [ContinuousMap.add_apply]

  -- abbreviations for the three integrands
  let fxy : ℝ → E :=
    fun τ =>
      g (compProj t₀ α τ) (fun j => compProj t₀ (update dα i (x + y) j) τ)
  let fx : ℝ → E :=
    fun τ =>
      g (compProj t₀ α τ) (fun j => compProj t₀ (update dα i x j) τ)
  let fy : ℝ → E :=
    fun τ =>
      g (compProj t₀ α τ) (fun j => compProj t₀ (update dα i y j) τ)

  have hfx_cont : Continuous fx := by
    simpa [fx] using continuous_integrand hg hu t₀ hα (update dα i x)
  have hfy_cont : Continuous fy := by
    simpa [fy] using continuous_integrand hg hu t₀ hα (update dα i y)

  have hfx_int : IntervalIntegrable fx volume (t₀ : ℝ) (t : ℝ) :=
    (continuous_integrand hg hu t₀ hα (update dα i x)).intervalIntegrable t₀ t
  have hfy_int : IntervalIntegrable fy volume (t₀ : ℝ) (t : ℝ) :=
    (continuous_integrand hg hu t₀ hα (update dα i y)).intervalIntegrable t₀ t

  -- pointwise additivity of the integrand in the i-th slot
  have h_point : ∀ τ, fxy τ = fx τ + fy τ := by
    intro τ
    -- base vector in E^n at time τ
    let v : Fin n → E := fun j => compProj t₀ (dα j) τ

    have harg_xy :
        (fun j => compProj t₀ (update dα i (x + y) j) τ) =
          Function.update v i (compProj t₀ (x + y) τ) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [v]
      · simp [v, hji]

    have harg_x :
        (fun j => compProj t₀ (update dα i x j) τ) =
          Function.update v i (compProj t₀ x τ) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [v]
      · simp [v, hji]

    have harg_y :
        (fun j => compProj t₀ (update dα i y j) τ) =
          Function.update v i (compProj t₀ y τ) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [v]
      · simp [v, hji]

    have hcomp_add : compProj t₀ (x + y) τ = compProj t₀ x τ + compProj t₀ y τ := by
      simp [compProj]

    -- now use multilinearity of `g (compProj t₀ α τ)` in the i-th coordinate
    have hmul :
        g (compProj t₀ α τ) (Function.update v i (compProj t₀ (x + y) τ)) =
          g (compProj t₀ α τ) (Function.update v i (compProj t₀ x τ)) +
          g (compProj t₀ α τ) (Function.update v i (compProj t₀ y τ)) := by
      -- `map_update_add` lives on `MultilinearMap`, so go via `toMultilinearMap`
      simpa [hcomp_add] using
        ((g (compProj t₀ α τ)).toMultilinearMap.map_update_add
          (m := v) (i := i) (x := compProj t₀ x τ) (y := compProj t₀ y τ))

    -- rewrite back to the original `fun j => compProj ...`
    simpa [fxy, fx, fy, harg_xy, harg_x, harg_y] using hmul

  -- finish by rewriting the integrand, then using `integral_add`
  calc
    ∫ τ in (t₀ : ℝ)..(t : ℝ), fxy τ
        = ∫ τ in (t₀ : ℝ)..(t : ℝ), (fx τ + fy τ) := by
            refine intervalIntegral.integral_congr ?_
            intro τ hτ
            exact h_point τ
    _ = (∫ τ in (t₀ : ℝ)..(t : ℝ), fx τ) + (∫ τ in (t₀ : ℝ)..(t : ℝ), fy τ) := by
          simpa using (intervalIntegral.integral_add hfx_int hfy_int)

-- rename `x`
lemma integralCM_update_smul {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n) (c : ℝ)
    (x : C(Icc tmin tmax, E)) :
    integralCM hg hu t₀ hα (update dα i (c • x)) = c • integralCM hg hu t₀ hα (update dα i x) := by
  ext t

  -- abbreviate the two integrands
  let fcx : ℝ → E :=
    fun τ =>
      g (compProj t₀ α τ) (fun j => compProj t₀ (update dα i (c • x) j) τ)
  let fx : ℝ → E :=
    fun τ =>
      g (compProj t₀ α τ) (fun j => compProj t₀ (update dα i x j) τ)

  -- (You likely already have a lemma / helper from the previous proof.)
  -- We need intervalIntegrable fx to use `integral_smul`.
  -- One convenient way: prove `Continuous fx` as in your `update_add` proof, then:
  have hx_int : IntervalIntegrable fx volume t₀ t :=
    (continuous_integrand hg hu t₀ hα (update dα i x)).intervalIntegrable t₀ t

  -- pointwise: fcx τ = c • fx τ (multilinearity in slot i)
  have h_point : ∀ τ, fcx τ = c • fx τ := by
    intro τ
    let v : Fin n → E := fun j => compProj t₀ (dα j) τ

    have harg_cx :
        (fun j => compProj t₀ (update dα i (c • x) j) τ) =
          Function.update v i (compProj t₀ (c • x) τ) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [v]
      · simp [v, hji]

    have harg_x :
        (fun j => compProj t₀ (update dα i x j) τ) =
          Function.update v i (compProj t₀ x τ) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [v]
      · simp [v, hji]

    have hcomp_smul : compProj t₀ (c • x) τ = c • compProj t₀ x τ := by
      simp [compProj]

    -- multilinearity in the i-th coordinate
    have hmul :
        g (compProj t₀ α τ) (Function.update v i (compProj t₀ (c • x) τ)) =
          c • g (compProj t₀ α τ) (Function.update v i (compProj t₀ x τ)) := by
      -- `map_update_smul` is on `MultilinearMap`, so go via `toMultilinearMap`
      simpa [hcomp_smul] using
        ((g (compProj t₀ α τ)).toMultilinearMap.map_update_smul
          (m := v) (i := i) (c := c) (x := compProj t₀ x τ))

    simpa [fcx, fx, harg_cx, harg_x] using hmul

  -- now integrate: ∫ fcx = ∫ (c•fx) = c • ∫ fx
  calc
    ∫ τ in (t₀ : ℝ)..(t : ℝ), fcx τ
        = ∫ τ in (t₀ : ℝ)..(t : ℝ), (c • fx τ) := by
            refine intervalIntegral.integral_congr ?_
            intro τ hτ
            simpa using h_point τ
    _ = c • ∫ τ in (t₀ : ℝ)..(t : ℝ), fx τ := by
          simpa using (intervalIntegral.integral_smul c hx_int)

lemma continuous_integralCM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) : Continuous (integralCM hg hu t₀ hα) := by
  -- Let X be the parameter space for dα
  let X := Fin n → C(Icc tmin tmax, E)
  let fparam : (X × (Icc tmin tmax)) → ℝ → E :=
    fun p τ => g (compProj t₀ α τ) (fun i => compProj t₀ (p.1 i) τ)

  -- Use the curry/uncurry criterion for continuity into `C(Icc, E)`:
  -- it suffices to show the uncurried map is continuous.
  refine
    ContinuousMap.continuous_of_continuous_uncurry
      (X := X) (Y := Icc tmin tmax) (Z := E)
      (f := fun dα : X => integralCM hg hu t₀ hα dα) ?_

  -- Goal: continuity of (dα, t) ↦ (integralCM ... dα) t
  -- This is definitionaly `integralFun g t₀ α dα t`.
  -- We'll prove it via a parametric-interval-integral lemma.

  -- First, show τ ↦ g (compProj t₀ α τ) is continuous (only depends on τ).
  have hg_comp :
      Continuous (fun τ : ℝ => g (compProj t₀ α τ)) := by
    -- show MapsTo (compProj t₀ α) univ u using hα
    have hmap : ∀ (x : ℝ), compProj t₀ α x ∈ u := by
      intro τ
      rw [compProj]
      apply hα
      trivial
    have hcont :
        ContinuousOn (fun τ : ℝ => g (compProj t₀ α τ)) Set.univ :=
      hg.comp_continuous (continuous_compProj (t₀ := t₀) (α := α)) hmap |>.continuousOn
    simpa [Continuous, Set.restrict] using hcont

  -- Next: joint continuity of the integrand (dα, τ) ↦ g(compProj α τ) (…evaluations of dα…)
  have hIntegrand :
      Continuous (fun q : X × ℝ =>
        g (compProj t₀ α q.2) (fun i => compProj t₀ (q.1 i) q.2)) := by
    -- Build continuity of q ↦ (fun i => compProj t₀ (q.1 i) q.2)
    have hm :
        Continuous (fun q : X × ℝ => fun i : Fin n => compProj t₀ (q.1 i) q.2) := by
      classical
      refine continuous_pi ?_
      intro i
      -- We show (q ↦ compProj t₀ (q.1 i) q.2) is continuous using evaluation continuity.
      -- compProj t₀ f t = f (projIcc ... t).
      have heval :
          Continuous (fun p : C(Icc tmin tmax, E) × Icc tmin tmax => p.1 p.2) := by
        -- evaluation map is continuous when domain is locally compact (Icc is compact hence locally compact)
        simpa using
          (continuous_eval :
            Continuous (fun p : C(Icc tmin tmax, E) × Icc tmin tmax => p.1 p.2))
      have hpair :
          Continuous (fun p : C(Icc tmin tmax, E) × ℝ =>
            (p.1, projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) p.2)) := by
        exact continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)
      have hcompProjVar :
          Continuous (fun p : C(Icc tmin tmax, E) × ℝ =>
            p.1 (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) p.2)) := by
        exact heval.comp hpair
      -- Now compose with q ↦ (q.1 i, q.2)
      have hqi : Continuous (fun q : X × ℝ => q.1 i) :=
        (continuous_apply i).comp continuous_fst
      have hqpair : Continuous (fun q : X × ℝ => (q.1 i, q.2)) :=
        hqi.prodMk continuous_snd
      exact hcompProjVar.comp hqpair

    -- continuity of q ↦ g (compProj t₀ α q.2)
    have hgq : Continuous (fun q : X × ℝ => g (compProj t₀ α q.2)) :=
      hg_comp.comp continuous_snd

    -- Now combine with continuity of evaluation (h,m) ↦ h m for ContinuousMultilinearMap
    have hEval :
        Continuous (fun p : (E [×n]→L[ℝ] E) × (Fin n → E) => p.1 p.2) := by
      -- NOTE: if this lemma name doesn’t resolve, import `Mathlib/Analysis/NormedSpace/Multilinear`
      simpa using
        (continuous_eval :
          Continuous (fun p : (E [×n]→L[ℝ] E) × (Fin n → E) => p.1 p.2))

    exact hEval.comp (hgq.prodMk hm)

  -- Lift the integrand continuity to include the extra (ignored) `t : Icc` parameter.
  have hIntegrand' :
      Continuous (fun q : (X × Icc tmin tmax) × ℝ =>
        g (compProj t₀ α q.2) (fun i => compProj t₀ (q.1.1 i) q.2)) := by
    -- just precompose hIntegrand with ( (dα,t),τ ) ↦ (dα,τ )
    have hproj : Continuous (fun q : (X × Icc tmin tmax) × ℝ => (q.1.1, q.2)) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    simpa using hIntegrand.comp hproj

  have hfparam : Continuous (Function.uncurry fparam) := by
    -- Function.uncurry fparam = fun q : X' × ℝ => fparam q.1 q.2
    simpa [Function.uncurry, fparam] using hIntegrand'

  -- Finally, apply continuity of the parametric interval integral with variable upper limit.
  -- This lemma lives in `MeasureTheory/Integral/DominatedConvergence`.
  -- It gives continuity of p ↦ ∫ τ in a..b(p), F(p,τ) when F is continuous.
  have huncurry :
      Continuous (fun p : X × Icc tmin tmax => integralFun g t₀ α p.1 p.2) := by
    -- Use the library lemma for parametric interval integrals of continuous integrands.
    -- (Depending on your imports/version, you may need the primed/unprimed variant.)
    simpa [integralFun] using
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (a₀ := (t₀ : ℝ))
        (s := fun p : X × Icc tmin tmax => (p.2 : ℝ))
        (f := fparam)
        hfparam
        (continuous_induced_dom.comp' continuous_snd)

  -- Finish by rewriting the uncurried map in terms of `integralCM`.
  simpa [integralCM, integralCM, integralFun] using huncurry

def integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) : C(Icc tmin tmax, E) [×n]→L[ℝ] C(Icc tmin tmax, E) where
  toFun := integralCM hg hu t₀ hα
  -- why convert? `instDecidableEqFin` isn't being recognised as a `DecidableEq (Fin n)`
  map_update_add' dα i α₁ α₂ := by convert integralCM_update_add hg hu t₀ hα dα i α₁ α₂
  map_update_smul' dα i c α₁ := by convert integralCM_update_smul hg hu t₀ hα dα i c α₁
  cont := continuous_integralCM ..

end

end SmoothFlow
