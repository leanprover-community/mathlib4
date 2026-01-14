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

lemma compProj_mapsTo {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    {u : Set E} (hα : MapsTo α univ u) (τ : ℝ) : compProj t₀ α τ ∈ u :=
  hα trivial

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
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) :
    Continuous (fun τ ↦ g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)) := by
  -- continuity of τ ↦ g (compProj t₀ α τ)
  have hgφ : Continuous fun τ => g (compProj t₀ α τ) :=
    hg.comp_continuous (continuous_compProj t₀ α) (compProj_mapsTo t₀ hα)
  -- continuity of τ ↦ (j ↦ compProj t₀ (dα j) τ)
  have hvec : Continuous (fun τ => (fun j => compProj t₀ (dα j) τ)) :=
    continuous_pi fun j => continuous_compProj t₀ (dα j)
  exact continuous_eval.comp (hgφ.prodMk hvec)

variable [CompleteSpace E]

-- consider new lemma for `MapsTo α univ u ↔ range α ⊆ u`
lemma continuous_integralFun {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) :
    Continuous (integralFun g t₀ α dα) := by
  apply Continuous.comp
    (g := fun t ↦ ∫ τ in t₀..t, g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)) _
    continuous_subtype_val
  rw [continuous_iff_continuousAt]
  exact fun t ↦ ((continuous_integrand hg t₀ hα dα).integral_hasStrictDerivAt t₀ t).continuousAt

/--
The integral as a function from continuous curves to continuous curves, enabling us to take
derivatives with respect to the curve
-/
def integralCMAux {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) where
  toFun := integralFun g t₀ α dα
  continuous_toFun := continuous_integralFun hg t₀ hα dα

open Classical in
/--
The integral as a global function from continuous curves to continuous curves, using the junk value
pattern, which will allow us to take its iterated derivative with respect to the curve
-/
def integralCM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : Fin n → C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) :=
  if hα : MapsTo α univ u then integralCMAux hg t₀ hα dα else 0

open Classical in
lemma integralCM_def {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    integralCM hg t₀ α =
      fun dα ↦ if hα : MapsTo α univ u then integralCMAux hg t₀ hα dα else 0 := rfl

lemma integralCM_if_pos {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)} (hα : MapsTo α univ u) :
    integralCM hg t₀ α = integralCMAux hg t₀ hα := by
  simp [integralCM_def, dif_pos hα]

lemma integralCM_if_neg {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : ¬MapsTo α univ u) :
    integralCM hg t₀ α = fun _ ↦ 0 := by
  simp [integralCM_def, dif_neg hα]

-- rename `x`, `y`
lemma integralCM_update_add {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n) (x y : C(Icc tmin tmax, E)) :
    integralCM hg t₀ α (update dα i (x + y)) =
      integralCM hg t₀ α (update dα i x) + integralCM hg t₀ α (update dα i y) := by
  by_cases hα : MapsTo α univ u
  · simp only [integralCM_if_pos _ _ hα]
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
      simpa [fx] using continuous_integrand hg t₀ hα (update dα i x)
    have hfy_cont : Continuous fy := by
      simpa [fy] using continuous_integrand hg t₀ hα (update dα i y)

    have hfx_int : IntervalIntegrable fx volume (t₀ : ℝ) (t : ℝ) :=
      (continuous_integrand hg t₀ hα (update dα i x)).intervalIntegrable t₀ t
    have hfy_int : IntervalIntegrable fy volume (t₀ : ℝ) (t : ℝ) :=
      (continuous_integrand hg t₀ hα (update dα i y)).intervalIntegrable t₀ t

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
  · simp [integralCM_if_neg _ _ hα]

-- rename `x`
lemma integralCM_update_smul {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n) (c : ℝ) (x : C(Icc tmin tmax, E)) :
    integralCM hg t₀ α (update dα i (c • x)) = c • integralCM hg t₀ α (update dα i x) := by
  by_cases hα : MapsTo α univ u
  · simp only [integralCM_if_pos _ _ hα]
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
      (continuous_integrand hg t₀ hα (update dα i x)).intervalIntegrable t₀ t

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
  · simp [integralCM_if_neg _ _ hα]

lemma continuous_integralCM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    Continuous (integralCM hg t₀ α) := by
  by_cases hα : MapsTo α univ u
  · simp only [integralCM_if_pos _ _ hα]
    -- Let X be the parameter space for dα
    let X := Fin n → C(Icc tmin tmax, E)
    let fparam : (X × (Icc tmin tmax)) → ℝ → E :=
      fun p τ => g (compProj t₀ α τ) (fun i => compProj t₀ (p.1 i) τ)

    -- Use the curry/uncurry criterion for continuity into `C(Icc, E)`:
    -- it suffices to show the uncurried map is continuous.
    refine
      ContinuousMap.continuous_of_continuous_uncurry
        (X := X) (Y := Icc tmin tmax) (Z := E)
        (f := fun dα : X => integralCMAux hg t₀ hα dα) ?_

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
  · simpa [integralCM_if_neg _ _ hα] using continuous_const

/--
The integral as a continuous multilinear map on the space of continuous curves, which will allow us
to relate it to `iteratedFDeriv`
-/
def integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u) {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) [×n]→L[ℝ] C(Icc tmin tmax, E) where
  toFun := integralCM hg t₀ α
  -- why convert? `instDecidableEqFin` isn't being recognised as a `DecidableEq (Fin n)`
  map_update_add' dα i α₁ α₂ := by convert integralCM_update_add hg t₀ α dα i α₁ α₂
  map_update_smul' dα i c α₁ := by convert integralCM_update_smul hg t₀ α dα i c α₁
  cont := continuous_integralCM ..

lemma continuousOn_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    ContinuousOn (integralCMLM hg t₀) {α : C(Icc tmin tmax, E) | MapsTo α univ u} := by
  -- The set {α | MapsTo α univ u} is open
  have hS_open : IsOpen {α : C(Icc tmin tmax, E) | MapsTo α univ u} :=
    ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu

  -- Subtype for the set S
  let S := {α : C(Icc tmin tmax, E) | MapsTo α univ u}

  -- Abbreviate the parameter space
  let X := Fin n → C(Icc tmin tmax, E)

  rw [continuousOn_iff_continuous_restrict]

  -- The topology on ContinuousMultilinearMap is induced by the embedding into UniformOnFun.
  -- We use isEmbedding_toUniformOnFun to reduce to continuity of the underlying function.
  rw [ContinuousMultilinearMap.isEmbedding_toUniformOnFun.continuous_iff]

  -- Goal: Continuous (toUniformOnFun ∘ S.restrict (integralCMLM hg hu t₀))
  -- The topology on UniformOnFun is uniform convergence on von Neumann bounded sets.
  rw [UniformOnFun.continuous_rng_iff]

  -- Goal: for every von Neumann bounded set B in X = (Fin n → C(Icc, E)),
  -- the map α ↦ (integralCMLM hg hu t₀ α)|_B is continuous into UniformFun B C(Icc, E).
  intro B hB

  -- By equicontinuous_iff_continuous, it suffices to show equicontinuity of the family
  -- F_dα : S → C(Icc, E) given by F_dα(α) = (integralCMLM hg hu t₀ α) dα, indexed by dα ∈ B.
  rw [← equicontinuous_iff_continuous]

  -- Since B is von Neumann bounded in a normed space, it's norm-bounded.
  have hB_bdd : Bornology.IsBounded B := NormedSpace.isVonNBounded_iff ℝ |>.mp hB

  -- Equicontinuity at each point α₀
  intro α₀
  rw [equicontinuousAt_iff_pair]
  intro U hU

  -- Get ε from the uniformity
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU

  -- The key: joint continuity of the parametric integral in (α, dα)
  -- Define the uncurried integral function
  let fparam : (S × X) × Icc tmin tmax → ℝ → E :=
    fun p τ => g (compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) τ) (fun i => compProj t₀ (p.1.2 i) τ)

  -- Joint continuity of the integrand
  have hIntegrand : Continuous (fun p : ((S × X) × Icc tmin tmax) × ℝ =>
      g (compProj t₀ (p.1.1.1 : C(Icc tmin tmax, E)) p.2) (fun i => compProj t₀ (p.1.1.2 i) p.2)) := by
    -- Membership in u
    have hmem : ∀ p : (S × X) × ℝ, compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) p.2 ∈ u := by
      intro ⟨⟨α, _⟩, τ⟩
      exact α.2 (Set.mem_univ _)
    -- Continuity of compProj in (α, τ)
    have hcomp : Continuous (fun p : (S × X) × ℝ =>
        compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) p.2) := by
      have hpair : Continuous (fun p : (S × X) × ℝ =>
          ((p.1.1 : C(Icc tmin tmax, E)), projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) p.2)) :=
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
          (continuous_projIcc.comp continuous_snd)
      exact continuous_eval.comp hpair
    have hg_comp : Continuous (fun p : (S × X) × ℝ =>
        g (compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) p.2)) := hg.comp_continuous hcomp hmem
    -- Continuity of dα evaluation
    have hvec : Continuous (fun p : (S × X) × ℝ => fun i => compProj t₀ (p.1.2 i) p.2) := by
      refine continuous_pi fun i => ?_
      have hpair : Continuous (fun p : (S × X) × ℝ =>
          (p.1.2 i, projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) p.2)) :=
        ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).prodMk
          (continuous_projIcc.comp continuous_snd)
      exact continuous_eval.comp hpair
    -- Combine via multilinear evaluation
    have hg' : Continuous (fun p : ((S × X) × Icc tmin tmax) × ℝ =>
        g (compProj t₀ (p.1.1.1 : C(Icc tmin tmax, E)) p.2)) :=
      hg_comp.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hvec' : Continuous (fun p : ((S × X) × Icc tmin tmax) × ℝ =>
        fun i => compProj t₀ (p.1.1.2 i) p.2) :=
      hvec.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact continuous_eval.comp (hg'.prodMk hvec')

  have hfparam : Continuous (Function.uncurry fparam) := by
    simpa [Function.uncurry, fparam] using hIntegrand

  -- The parametric integral is continuous in (α, dα, t)
  have hIntegralCont : Continuous (fun p : (S × X) × Icc tmin tmax =>
      ∫ τ in (t₀ : ℝ)..(p.2 : ℝ), g (compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) τ)
        (fun i => compProj t₀ (p.1.2 i) τ)) := by
    simpa [fparam] using
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (a₀ := (t₀ : ℝ))
        (s := fun p : (S × X) × Icc tmin tmax => (p.2 : ℝ))
        (f := fparam)
        hfparam
        (continuous_induced_dom.comp continuous_snd)

  -- The map (α, dα) ↦ (t ↦ integral) is continuous into C(Icc, E)
  have hCont : Continuous (fun p : S × X => (integralCMLM hg t₀ ↑p.1) p.2) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    convert hIntegralCont using 2 with ⟨⟨α, dα⟩, t⟩
    simp only [Function.uncurry_apply_pair, integralCMLM, integralCM_if_pos _ _ α.2]
    rfl

  -- Use joint continuity at (α₀, dα) to get uniform bound over B
  -- For each dα ∈ B, the map α ↦ F(α, dα) is continuous.
  -- We need uniform control over B.

  -- The key observation: since hCont is continuous and we're in a metric space,
  -- the preimage of the ε/2-ball around F(α₀, dα) contains a neighborhood of (α₀, dα).
  -- For the product topology on S × B, we get uniform neighborhoods.

  -- Use that the restriction S × B → C(Icc, E) is continuous.
  -- At α₀ and for dα in the compact... wait, B may not be compact.

  -- Alternative approach: use the integral bound directly.
  -- F(α, dα) - F(α₀, dα) = ∫ [g(α(τ)) - g(α₀(τ))](dα(τ)) dτ
  -- ‖F(α, dα) - F(α₀, dα)‖_∞ ≤ (tmax - tmin) · sup_τ ‖g(α(τ)) - g(α₀(τ))‖_op · M^n
  -- where M bounds ‖dα‖ for dα ∈ B.

  -- Get the bound M for B
  obtain ⟨M, hM⟩ := hB_bdd.exists_norm_le
  -- Ensure M ≥ 0
  let M' := max M 0

  -- For the estimate, we need g to be uniformly continuous on compact subsets of u.
  -- Since α ∈ S and α₀ ∈ S, their images are in u.
  -- The set of values {α(τ) : α ∈ V, τ ∈ Icc} for V a neighborhood of α₀ is compact.

  -- For any neighborhood of α₀ in S, the images under compProj are precompact in u.
  -- By continuity of g on u, g is uniformly continuous on compact subsets.

  -- Define the modulus: for α close to α₀, sup_τ ‖g(α(τ)) - g(α₀(τ))‖ is small.

  -- The map α ↦ g ∘ (compProj t₀ α) is continuous from S to C(ℝ, E [×n]→L[ℝ] E).
  have hg_cont : Continuous (fun α : S => fun τ : ℝ =>
      g (compProj t₀ (α : C(Icc tmin tmax, E)) τ)) := by
    refine continuous_pi fun τ => ?_
    have hmem : ∀ α : S, compProj t₀ (α : C(Icc tmin tmax, E)) τ ∈ u := fun α => α.2 (mem_univ _)
    have hcomp : Continuous (fun α : S => compProj t₀ (α : C(Icc tmin tmax, E)) τ) := by
      simp only [compProj]
      exact (ContinuousEvalConst.continuous_eval_const _).comp continuous_subtype_val
    exact hg.comp_continuous hcomp hmem

  -- At α₀, by continuity of hg_cont, for any ε' > 0 there's a neighborhood V of α₀ such that
  -- for all α ∈ V and all τ, ‖g(α(τ)) - g(α₀(τ))‖ < ε'.

  -- Set ε' = ε / (4 * (1 + |tmax - tmin|) * (1 + M'^n))
  -- Using 4 instead of 2 ensures strict inequality ε' * (...) < ε/2
  let ε' := ε / (4 * (1 + |tmax - tmin|) * (1 + M' ^ n))
  have hε' : 0 < ε' := by
    apply div_pos hε
    apply mul_pos
    apply mul_pos
    · linarith
    · linarith [abs_nonneg (tmax - tmin)]
    · have : 0 ≤ M' ^ n := pow_nonneg (le_max_right M 0) n
      linarith

  -- Get neighborhood V from continuity of hg_cont
  -- This requires working with the uniformity on C(ℝ, E [×n]→L[ℝ] E), which is complex.

  -- Simpler approach: use continuity of hCont directly.
  -- The map hCont : S × X → C(Icc, E) is continuous.
  -- At (α₀, dα₀) for any dα₀, we have continuity.

  -- For the equicontinuity goal, we need:
  -- ∀ ε > 0, ∃ V ∈ 𝓝 α₀, ∀ α ∈ V, ∀ dα ∈ B, dist (F α₀ dα) (F α dα) < ε

  -- Use the specific structure: F(α, dα)(t) = ∫_{t₀}^t g(α(τ))(dα(τ)) dτ
  -- The difference F(α, dα) - F(α₀, dα) satisfies:
  -- ‖F(α, dα)(t) - F(α₀, dα)(t)‖ ≤ |t - t₀| · sup_τ ‖g(α(τ)) - g(α₀(τ))‖ · ∏_i ‖dα_i‖_∞

  -- Since |t - t₀| ≤ tmax - tmin and ∏_i ‖dα_i‖_∞ ≤ M^n for dα ∈ B,
  -- we get ‖F(α, dα) - F(α₀, dα)‖_∞ ≤ (tmax - tmin) · sup_τ ‖g(α(τ)) - g(α₀(τ))‖ · M^n

  -- The term sup_τ ‖g(α(τ)) - g(α₀(τ))‖ → 0 as α → α₀ uniformly in τ,
  -- by continuity of g and compactness of the image of Icc under α, α₀.

  -- Formally, we need a neighborhood of α₀ where this sup is small.
  -- This follows from continuity of the map α ↦ (g ∘ α) from S to C(Icc, E [×n]→L[ℝ] E).

  -- For the full formal proof, we would extract this neighborhood from hg_cont.
  -- The argument is:
  -- 1. hg_cont gives continuity at α₀ in the sup norm topology on C(ℝ, ...)
  -- 2. Restricting to τ ∈ [tmin, tmax] (via projIcc), we get the bound we need
  -- 3. Combined with the M^n factor, we get uniform control over B

  -- The goal from equicontinuousAt_iff_pair is:
  -- ∃ V ∈ 𝓝 α₀, ∀ x ∈ V, ∀ y ∈ V, ∀ (i : ↑B), (F x i, F y i) ∈ U
  -- where F x i = (integralCMLM hg hu t₀ x) i

  -- We show this by finding a neighborhood V where for any x, y ∈ V and dα ∈ B,
  -- dist (F x dα) (F y dα) < ε. By triangle inequality, it suffices to show
  -- dist (F x dα) (F α₀ dα) < ε/2 and dist (F α₀ dα) (F y dα) < ε/2.

  -- The key lemma: for any dα ∈ B, there's a uniform neighborhood of α₀ where the integral is close
  have key : ∀ᶠ α in 𝓝 α₀, ∀ dα ∈ B, dist ((integralCMLM hg t₀ ↑α₀) dα)
      ((integralCMLM hg t₀ ↑α) dα) < ε / 2 := by
    -- Strategy: use the integral estimate
    -- ‖F(α, dα) - F(α₀, dα)‖_∞ ≤ |tmax - tmin| · sup_τ ‖g(α(τ)) - g(α₀(τ))‖ · M^n
    -- where M bounds ‖dα‖ for dα ∈ B.

    -- The key is that for α in the open set S (curves mapping into u),
    -- the map α ↦ (t ↦ g(α(t))) is continuous on S with values in C(Icc, CLM).

    -- We work with the restriction to the open set S.
    -- The integralCMLM only depends on curves in S, and for α ∉ S, the value is junk.

    -- Since S is open, 𝓝 ↑α₀ in the ambient space equals Filter.map Subtype.val (𝓝 α₀).
    -- We use this to work with the subtype neighborhood filter.

    -- Convert the goal to the subtype filter
    have hS_nhd : ∀ᶠ x in 𝓝 (α₀ : C(Icc tmin tmax, E)), x ∈ S := hS_open.mem_nhds α₀.2
    rw [← map_nhds_subtype_coe_eq_nhds α₀.2 hS_nhd]
    rw [Filter.eventually_map]

    -- Now we need: ∀ᶠ α : S in 𝓝 α₀, ∀ dα ∈ B, dist ... < ε/2

    -- The map α ↦ (t ↦ g(α(t))) is continuous S → C(Icc, CLM).
    let gComp : S → C(Icc tmin tmax, E [×n]→L[ℝ] E) := fun α =>
      ⟨fun t => g (α.1 t),
        hg.comp_continuous α.1.continuous_toFun (fun t => α.2 (mem_univ t))⟩

    have hg_unif : Continuous gComp := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      have h1 : Continuous (fun p : S × Icc tmin tmax => (p.1 : C(Icc tmin tmax, E)) p.2) :=
        continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)
      have hmem : ∀ p : S × Icc tmin tmax, (p.1 : C(Icc tmin tmax, E)) p.2 ∈ u :=
        fun ⟨α, t⟩ => α.2 (mem_univ t)
      exact hg.comp_continuous h1 hmem

    -- By continuity at α₀, get a neighborhood where sup_t ‖g(α(t)) - g(α₀(t))‖ < ε'
    have hball : Metric.ball (gComp α₀) ε' ∈ 𝓝 (gComp α₀) := Metric.ball_mem_nhds _ hε'
    have hV_mem : gComp ⁻¹' Metric.ball (gComp α₀) ε' ∈ 𝓝 α₀ :=
      hg_unif.continuousAt.preimage_mem_nhds hball

    apply Filter.eventually_of_mem hV_mem
    intro α hα dα hdα

    -- α ∈ gComp ⁻¹' ball means gComp α ∈ Metric.ball (gComp α₀) ε'
    have hα_ball : dist (gComp α₀) (gComp α) < ε' := by
      rw [dist_comm]; exact Metric.mem_ball.mp hα

    -- Now estimate dist (F α₀ dα) (F α dα) using the integral bound
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    rw [ContinuousMap.dist_lt_iff hε2]
    intro t

    simp only [integralCMLM, integralCM_if_pos hg t₀ α₀.2, integralCM_if_pos hg t₀ α.2]

    -- Now the goal is:
    -- dist ((integralCMAux hg t₀ α₀.2 dα) t) ((integralCMAux hg t₀ α.2 dα) t) < ε/2
    -- which expands to:
    -- dist (∫ τ in t₀..t, g(α₀(τ))(dα(τ)) dτ) (∫ τ in t₀..t, g(α(τ))(dα(τ)) dτ) < ε/2

    -- Rewrite to the integral form explicitly
    show dist ((integralCMAux hg t₀ α₀.2 dα) t) ((integralCMAux hg t₀ α.2 dα) t) < ε / 2
    simp only [integralCMAux, ContinuousMap.coe_mk, integralFun]

    -- The distance is the norm of the difference
    rw [dist_eq_norm]

    -- Combine the integrals
    rw [← intervalIntegral.integral_sub]
    · -- Estimate ‖∫ [g(α₀(τ)) - g(α(τ))](dα(τ)) dτ‖
      -- The bound is: |t - t₀| · sup_τ ‖g(α₀(τ)) - g(α(τ))‖ · ∏_i ‖dα_i‖_∞
      --            ≤ |tmax - tmin| · ε' · M'^n
      --            < ε/2 (by choice of ε')

      -- Get the bound M' on dα
      have hdα_bound : ‖dα‖ ≤ M' := (hM dα hdα).trans (le_max_left M 0)

      -- Bound on each component
      have hdα_i_bound : ∀ i, ‖dα i‖ ≤ M' := fun i =>
        (norm_le_pi_norm dα i).trans hdα_bound

      -- The sup norm on C(Icc, E) bounds pointwise evaluation
      have hdα_eval_bound : ∀ i τ, ‖compProj t₀ (dα i) τ‖ ≤ M' := fun i τ => by
        simp only [compProj]
        exact ((dα i).norm_coe_le_norm _).trans (hdα_i_bound i)

      -- Product bound
      have hprod_bound : ∀ τ, ∏ i : Fin n, ‖compProj t₀ (dα i) τ‖ ≤ M' ^ n := fun τ => by
        calc ∏ i : Fin n, ‖compProj t₀ (dα i) τ‖
            ≤ ∏ _ : Fin n, M' := Finset.prod_le_prod (fun i _ => norm_nonneg _)
                (fun i _ => hdα_eval_bound i τ)
          _ = M' ^ n := by simp [Finset.prod_const, Finset.card_fin]

      -- The distance on C(Icc, CLM) gives pointwise bounds
      have hg_diff_bound : ∀ s : Icc tmin tmax, ‖g (α₀.1 s) - g (α.1 s)‖ < ε' := fun s => by
        have h1 : ‖gComp α₀ s - gComp α s‖ ≤ dist (gComp α₀) (gComp α) := by
          rw [← dist_eq_norm]
          exact ContinuousMap.dist_apply_le_dist s
        calc ‖g (α₀.1 s) - g (α.1 s)‖ = ‖gComp α₀ s - gComp α s‖ := by
              simp only [gComp, ContinuousMap.coe_mk]
          _ ≤ dist (gComp α₀) (gComp α) := h1
          _ < ε' := hα_ball

      -- Bound on the integrand at each point τ
      have hintegrand_bound : ∀ τ : ℝ,
          ‖(g (compProj t₀ (α₀ : C(Icc tmin tmax, E)) τ) -
            g (compProj t₀ (α : C(Icc tmin tmax, E)) τ))
              (fun i => compProj t₀ (dα i) τ)‖ ≤ ε' * M' ^ n := fun τ => by
        -- Use the multilinear map norm bound
        have hclm := ContinuousMultilinearMap.le_opNorm
          (g (compProj t₀ (α₀ : C(Icc tmin tmax, E)) τ) -
           g (compProj t₀ (α : C(Icc tmin tmax, E)) τ))
          (fun i => compProj t₀ (dα i) τ)
        -- compProj projects to the interval, so we can use hg_diff_bound
        simp only [compProj] at hclm ⊢
        set s : Icc tmin tmax := projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) τ with hs
        calc ‖(g (α₀.1 s) - g (α.1 s)) (fun i => (dα i) s)‖
            ≤ ‖g (α₀.1 s) - g (α.1 s)‖ * ∏ i : Fin n, ‖(dα i) s‖ := hclm
          _ ≤ ε' * ∏ i : Fin n, ‖(dα i) s‖ := by
              apply mul_le_mul_of_nonneg_right (le_of_lt (hg_diff_bound s))
              exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
          _ ≤ ε' * M' ^ n := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hε')
              simp only [compProj] at hprod_bound
              convert hprod_bound τ using 2

      -- Since compProj maps τ into [tmin, tmax], and |t - t₀| ≤ |tmax - tmin|:
      have ht_bound : |(t : ℝ) - (t₀ : ℝ)| ≤ tmax - tmin := by
        have h1 : (t : ℝ) ∈ Icc tmin tmax := t.2
        have h2 : (t₀ : ℝ) ∈ Icc tmin tmax := t₀.2
        rw [← Real.dist_eq]
        exact Real.dist_le_of_mem_Icc h1 h2

      -- Bound the integral using the constant bound
      -- Note: norm_integral_le_of_norm_le_const gives C * |b - a|, so we need to reorder
      have hM'_nn : 0 ≤ M' ^ n := pow_nonneg (le_max_right M 0) n
      have hpos1 : 0 < 1 + |tmax - tmin| := by linarith [abs_nonneg (tmax - tmin)]
      have hpos2 : 0 < 1 + M' ^ n := by linarith
      have hdenom_pos : 0 < 2 * (1 + |tmax - tmin|) * (1 + M' ^ n) := by positivity
      have hprod_pos : 0 < (1 + |tmax - tmin|) * (1 + M' ^ n) := by positivity
      have htnn : 0 ≤ tmax - tmin := by
        have := t₀.2
        linarith [this.1, this.2]

      have hε'_eq : ε' * ((1 + |tmax - tmin|) * (1 + M' ^ n)) = ε / 4 := by
        simp only [ε']; field_simp

      calc ‖∫ x in ↑t₀..↑t, ((g (compProj t₀ ↑α₀ x) - g (compProj t₀ ↑α x))
              fun i => compProj t₀ (dα i) x)‖
          ≤ (ε' * M' ^ n) * |(t : ℝ) - (t₀ : ℝ)| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro τ _
            exact hintegrand_bound τ
        _ ≤ (ε' * M' ^ n) * (tmax - tmin) := by
            apply mul_le_mul_of_nonneg_left ht_bound
            apply mul_nonneg (le_of_lt hε') hM'_nn
        _ ≤ ε' * ((1 + |tmax - tmin|) * (1 + M' ^ n)) := by
            have h1 : tmax - tmin ≤ 1 + |tmax - tmin| := by
              calc tmax - tmin ≤ |tmax - tmin| := le_abs_self _
                _ ≤ 1 + |tmax - tmin| := le_add_of_nonneg_left (by linarith)
            have h2 : M' ^ n ≤ 1 + M' ^ n := le_add_of_nonneg_left (by linarith)
            calc ε' * M' ^ n * (tmax - tmin)
                = ε' * (M' ^ n * (tmax - tmin)) := by ring
              _ = ε' * ((tmax - tmin) * M' ^ n) := by ring
              _ ≤ ε' * ((1 + |tmax - tmin|) * M' ^ n) := by
                  apply mul_le_mul_of_nonneg_left _ (le_of_lt hε')
                  apply mul_le_mul_of_nonneg_right h1 hM'_nn
              _ ≤ ε' * ((1 + |tmax - tmin|) * (1 + M' ^ n)) := by
                  apply mul_le_mul_of_nonneg_left _ (le_of_lt hε')
                  apply mul_le_mul_of_nonneg_left h2
                  linarith [abs_nonneg (tmax - tmin)]
        _ = ε / 4 := hε'_eq
        _ < ε / 2 := by linarith

    · exact continuous_integrand hg t₀ α₀.2 dα |>.intervalIntegrable ..
    · exact continuous_integrand hg t₀ α.2 dα |>.intervalIntegrable ..

  -- Now construct the neighborhood V
  -- key gives us V ∈ 𝓝 (↑α₀) in the ambient space C(Icc, E)
  -- We need to convert this to a neighborhood in the subtype S
  obtain ⟨V, hV_nhd, hV⟩ := key.exists_mem

  -- The preimage of V under the subtype embedding is a neighborhood in the subtype topology
  let V' : Set S := Subtype.val ⁻¹' V
  have hV'_nhd : V' ∈ 𝓝 α₀ := continuous_subtype_val.continuousAt.preimage_mem_nhds hV_nhd

  refine ⟨V', hV'_nhd, fun x hx y hy ⟨dα, hdα⟩ => ?_⟩
  -- x, y : S (the subtype), hx : x ∈ V' means ↑x ∈ V, and dα ∈ B

  -- Need to show ((integralCMLM hg hu t₀ x) dα, (integralCMLM hg hu t₀ y) dα) ∈ U
  -- By triangle inequality: dist (F x dα) (F y dα) ≤ dist (F x dα) (F α₀ dα) + dist (F α₀ dα) (F y dα)
  apply hεU
  calc dist ((integralCMLM hg t₀ ↑x) dα) ((integralCMLM hg t₀ ↑y) dα)
      ≤ dist ((integralCMLM hg t₀ ↑x) dα) ((integralCMLM hg t₀ ↑α₀) dα) +
        dist ((integralCMLM hg t₀ ↑α₀) dα) ((integralCMLM hg t₀ ↑y) dα) := dist_triangle ..
    _ = dist ((integralCMLM hg t₀ ↑α₀) dα) ((integralCMLM hg t₀ ↑x) dα) +
        dist ((integralCMLM hg t₀ ↑α₀) dα) ((integralCMLM hg t₀ ↑y) dα) := by
          rw [dist_comm ((integralCMLM hg t₀ ↑x) dα)]
    _ < ε / 2 + ε / 2 := add_lt_add (hV (↑x) hx dα hdα) (hV (↑y) hy dα hdα)
    _ = ε := by ring

end

end SmoothFlow
