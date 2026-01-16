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

/-- `compProj` is jointly continuous in the curve and time. -/
lemma continuous_compProj₂ {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    Continuous (fun p : C(Icc tmin tmax, E) × ℝ ↦ compProj t₀ p.1 p.2) :=
  continuous_fst.eval (continuous_projIcc.comp continuous_snd)

lemma _root_.ContinuousOn.continuous_comp_compProj {F : Type*} [TopologicalSpace F] {g : E → F}
    {u : Set E} (hg : ContinuousOn g u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    {α : C(Icc tmin tmax, E)} (hα : MapsTo α univ u) :
    Continuous (fun τ ↦ g (compProj t₀ α τ)) :=
  hg.comp_continuous (continuous_compProj t₀ α) (fun _ ↦ hα trivial)

lemma compProj_update {n : ℕ} {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n) (x : C(Icc tmin tmax, E)) (τ : ℝ) :
    (fun j ↦ compProj t₀ (update dα i x j) τ) =
      update (fun j ↦ compProj t₀ (dα j) τ) i (compProj t₀ x τ) := by
  ext j
  simp only [Function.update_apply, compProj]
  split_ifs <;> rfl

/-- `compProj` is continuous when the curve varies continuously. -/
lemma _root_.Continuous.continuous_compProj_pi₂ {X : Type*} [TopologicalSpace X] {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax) {f : X → C(Icc tmin tmax, E)} (hf : Continuous f) :
    Continuous (fun p : X × ℝ ↦ compProj t₀ (f p.1) p.2) :=
  (continuous_compProj₂ t₀).comp ((hf.comp continuous_fst).prodMk continuous_snd)

/-- Composing a function with `compProj` is continuous when the curve varies continuously. -/
lemma _root_.ContinuousOn.continuous_comp_compProj_pi₂ {X F : Type*} [TopologicalSpace X]
    [TopologicalSpace F] {g : E → F} {u : Set E} (hg : ContinuousOn g u) {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax) {f : X → C(Icc tmin tmax, E)} (hf : Continuous f)
    (hf_mem : ∀ x, MapsTo (f x) univ u) :
    Continuous (fun p : X × ℝ ↦ g (compProj t₀ (f p.1) p.2)) :=
  hg.comp_continuous (hf.continuous_compProj_pi₂ t₀) fun p ↦ hf_mem p.1 trivial

/-- Joint continuity of evaluating a family of curves via `compProj`. -/
lemma _root_.Continuous.continuous_compProj_pi_apply₂ {X : Type*} [TopologicalSpace X]
    {ι : Type*} {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {f : X → ι → C(Icc tmin tmax, E)}
    (hf : Continuous f) :
    Continuous (fun p : X × ℝ ↦ fun i ↦ compProj t₀ (f p.1 i) p.2) :=
  continuous_pi fun i ↦ ((continuous_apply i).comp hf).continuous_compProj_pi₂ t₀

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
    Continuous (fun τ ↦ g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)) :=
  continuous_eval.comp ((hg.continuous_comp_compProj t₀ hα).prodMk
    (continuous_pi fun j ↦ continuous_compProj t₀ (dα j)))

/-- The integrand is interval integrable. -/
lemma intervalIntegrable_integrand {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hg : ContinuousOn g u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    {α : C(Icc tmin tmax, E)} (hα : MapsTo α univ u) (dα : Fin n → C(Icc tmin tmax, E))
    (a b : Icc tmin tmax) :
    IntervalIntegrable (fun τ ↦ g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)) volume a b :=
  (continuous_integrand hg t₀ hα dα).intervalIntegrable a b

/-- Parametric version of `continuous_integrand`: the integrand is jointly continuous
in `dα` and the integration variable. -/
lemma continuous_integrand_pi₂ {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)} (hα : MapsTo α univ u) :
    Continuous (fun p : (Fin n → C(Icc tmin tmax, E)) × ℝ ↦
      g (compProj t₀ α p.2) (fun i ↦ compProj t₀ (p.1 i) p.2)) :=
  continuous_eval.comp (((hg.continuous_comp_compProj t₀ hα).comp continuous_snd).prodMk
    (continuous_id.continuous_compProj_pi_apply₂ t₀))

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

lemma integralCM_if_pos {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} (hα : MapsTo α univ u) :
    integralCM hg t₀ α = integralCMAux hg t₀ hα := by
  simp [integralCM_def, dif_pos hα]

lemma integralCM_if_neg {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)}
    (hα : ¬MapsTo α univ u) :
    integralCM hg t₀ α = fun _ ↦ 0 := by
  simp [integralCM_def, dif_neg hα]

-- TODO: Should this proof and `integralCM_update_smul` be pushed up to `integralFun`?
lemma integralCM_update_add {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n) (x y : C(Icc tmin tmax, E)) :
    integralCM hg t₀ α (update dα i (x + y)) =
      integralCM hg t₀ α (update dα i x) + integralCM hg t₀ α (update dα i y) := by
  by_cases hα : MapsTo α univ u
  · simp only [integralCM_if_pos hα, ContinuousMap.ext_iff, ContinuousMap.add_apply]
    intro t
    simp only [integralCMAux, ContinuousMap.coe_mk, integralFun]
    rw [← integral_add (intervalIntegrable_integrand hg t₀ hα _ t₀ t)
        (intervalIntegrable_integrand hg t₀ hα _ t₀ t),
      integral_congr fun τ _ ↦ ?_]
    simpa only [compProj_update] using (g (compProj t₀ α τ)).toMultilinearMap.map_update_add ..
  · simp [integralCM_if_neg hα]

lemma integralCM_update_smul {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n) (c : ℝ) (x : C(Icc tmin tmax, E)) :
    integralCM hg t₀ α (update dα i (c • x)) = c • integralCM hg t₀ α (update dα i x) := by
  by_cases hα : MapsTo α univ u
  · simp only [integralCM_if_pos hα, ContinuousMap.ext_iff, ContinuousMap.smul_apply]
    intro t
    simp only [integralCMAux, ContinuousMap.coe_mk, integralFun]
    rw [← intervalIntegral.integral_smul, integral_congr fun τ _ ↦ ?_]
    simpa only [compProj_update] using (g (compProj t₀ α τ)).toMultilinearMap.map_update_smul ..
  · simp [integralCM_if_neg hα]

lemma continuous_integralCM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    Continuous (integralCM hg t₀ α) := by
  by_cases hα : MapsTo α univ u
  · rw [integralCM_if_pos hα]
    let X := Fin n → C(Icc tmin tmax, E)
    let fparam : (X × Icc tmin tmax) → ℝ → E :=
      fun p τ ↦ g (compProj t₀ α τ) (fun i ↦ compProj t₀ (p.1 i) τ)
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_parametric_intervalIntegral_of_continuous _
      (continuous_induced_dom.comp continuous_snd)
    exact (continuous_integrand_pi₂ hg t₀ hα).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  · rw [integralCM_if_neg hα]
    exact continuous_const

/--
The integral as a continuous multilinear map on the space of continuous curves, which will allow us
to relate it to `iteratedFDeriv`
-/
def integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u) {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) [×n]→L[ℝ] C(Icc tmin tmax, E) where
  toFun := integralCM hg t₀ α
  -- `ContinuousMultilinearMap` asks for a proof for arbitrary `[DecidableEq ι]`, which is why we
  -- need `convert` here
  map_update_add' dα i α₁ α₂ := by convert integralCM_update_add hg t₀ α dα i α₁ α₂
  map_update_smul' dα i c α₁ := by convert integralCM_update_smul hg t₀ α dα i c α₁
  cont := continuous_integralCM ..

-- missing general lemma about applying `ContinuousMultilinearMap` equals applying `toFun`?
lemma integralCMLM_apply {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)}
    {dα : Fin n → C(Icc tmin tmax, E)} :
    integralCMLM hg t₀ α dα = integralCM hg t₀ α dα := rfl

/-
Strategy for proving the continuity of `α ↦ dα ↦ t ↦ ∫ τ in t₀..t, g (α τ) (fun i ↦ dα i τ)` as a
function `F → F [×n]→L[ℝ] F`:

* Embed `F [×n]→L[ℝ] F` into `UniformOnFun (Fin n → F) F`
(`ContinuousMultilinearMap.isEmbedding_toUniformOnFun`)
* Translate continuity `Topology.IsEmbedding.continuous_iff` across the embedding
* Translate continuity in the topology of uniform convergence on bounded sets to equicontinuity
(`UniformOnFun.continuous_rng_iff`, `equicontinuous_iff_continuous`, missing lemma combining them)
* Translate equicontinuity to finding witness sets (`equicontinuousAt_iff_pair`)
* Translate uniformity to `ε` witness (`Metric.mem_uniformity_dist`)
* Translate von Neumann boundedness to boundedness (`NormedSpace.isVonNBounded_iff`)
* Prove key inequality

(look into uniform equicontinuity, perhaps a missing lemma like iff_pair could remove the need for
`ε/2`)

-/

omit [CompleteSpace E] in
/-- The norm of a multilinear map difference applied to vectors is bounded by the operator norm
difference times the product of vector norms. -/
lemma norm_sub_continuousMultilinearMap_apply_le {n : ℕ} {f₁ f₂ : E [×n]→L[ℝ] E}
    {ε M : ℝ} (hε : ‖f₁ - f₂‖ ≤ ε) {v : Fin n → E} (hv : ∏ i, ‖v i‖ ≤ M) :
    ‖(f₁ - f₂) v‖ ≤ ε * M := by
  calc ‖(f₁ - f₂) v‖
      ≤ ‖f₁ - f₂‖ * ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm ..
    _ ≤ ε * M := by
        apply mul_le_mul hε hv (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        exact (norm_nonneg _).trans hε

/-- The distance between two `integralCMLM` values is bounded by the sup-norm distance of `g ∘ α`
times the norm bound on `dα` times the interval length. -/
lemma dist_integralCMLM_le {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α α' : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) (hα' : MapsTo α' univ u)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hg_close : ∀ t : Icc tmin tmax, ‖g (α t) - g (α' t)‖ ≤ ε)
    {dα : Fin n → C(Icc tmin tmax, E)} (hdα : ∀ i, ‖dα i‖ ≤ M) :
    dist ((integralCMLM hg t₀ α) dα) ((integralCMLM hg t₀ α') dα) ≤
      ε * M ^ n * (tmax - tmin) := by
  have hnn : 0 ≤ ε * M ^ n * (tmax - tmin) := by
    apply mul_nonneg (mul_nonneg (le_of_lt hε) (pow_nonneg hM n))
    linarith [t₀.2.1, t₀.2.2]
  rw [ContinuousMap.dist_le hnn]
  intro t
  simp only [integralCMLM_apply, integralCM_if_pos hα, integralCM_if_pos hα',
    integralCMAux, ContinuousMap.coe_mk, integralFun, dist_eq_norm,
    ← intervalIntegral.integral_sub
      (intervalIntegrable_integrand hg t₀ hα dα ..)
      (intervalIntegrable_integrand hg t₀ hα' dα ..)]
  have hdα_eval_bound : ∀ i τ, ‖compProj t₀ (dα i) τ‖ ≤ M := fun i τ ↦ by
    simp only [compProj]
    exact ((dα i).norm_coe_le_norm _).trans (hdα i)
  have hprod_bound : ∀ τ, ∏ i : Fin n, ‖compProj t₀ (dα i) τ‖ ≤ M ^ n := fun τ ↦
    (Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hdα_eval_bound i τ)).trans_eq
      (by simp [Finset.prod_const])
  have hintegrand_bound : ∀ τ : ℝ,
      ‖(g (compProj t₀ α τ) - g (compProj t₀ α' τ)) (fun i ↦ compProj t₀ (dα i) τ)‖ ≤
        ε * M ^ n := fun τ ↦ by
    simp only [compProj] at hprod_bound ⊢
    exact norm_sub_continuousMultilinearMap_apply_le (hg_close _) (hprod_bound τ)
  have ht_bound : |(t : ℝ) - (t₀ : ℝ)| ≤ tmax - tmin := by
    rw [← Real.dist_eq]
    exact Real.dist_le_of_mem_Icc t.2 t₀.2
  calc ‖∫ x in ↑t₀..↑t, ((g (compProj t₀ α x) - g (compProj t₀ α' x))
          fun i ↦ compProj t₀ (dα i) x)‖
      ≤ (ε * M ^ n) * |(t : ℝ) - (t₀ : ℝ)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro τ _
        exact hintegrand_bound τ
    _ ≤ ε * M ^ n * (tmax - tmin) := by
        apply mul_le_mul_of_nonneg_left ht_bound
        apply mul_nonneg (le_of_lt hε) (pow_nonneg hM n)

omit [CompleteSpace E] in
/-- The integrand `(α, dα, τ) ↦ g(compProj t₀ α τ)(fun i ↦ compProj t₀ (dα i) τ)` is continuous
when `g` is continuous on the open set `u` and `α` maps into `u`. This is the fully parametric
version of `continuous_integrand`, varying in both `α` and `dα`. -/
lemma continuous_integrand_param {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    Continuous
      (fun p : ({α : C(Icc tmin tmax, E) | MapsTo α univ u} × (Fin n → C(Icc tmin tmax, E))) × ℝ ↦
      g (compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) p.2)
        (fun i ↦ compProj t₀ (p.1.2 i) p.2)) := by
  let S := {α : C(Icc tmin tmax, E) | MapsTo α univ u}
  have hmem : ∀ p : (S × (Fin n → C(Icc tmin tmax, E))) × ℝ,
      compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) p.2 ∈ u := fun ⟨⟨α, _⟩, _⟩ ↦ α.2 (mem_univ _)
  have hcomp : Continuous (fun p : (S × (Fin n → C(Icc tmin tmax, E))) × ℝ ↦
      compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) p.2) :=
    (continuous_compProj₂ t₀).comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd)
  have hg_comp : Continuous (fun p : (S × (Fin n → C(Icc tmin tmax, E))) × ℝ ↦
      g (compProj t₀ (p.1.1 : C(Icc tmin tmax, E)) p.2)) := hg.comp_continuous hcomp hmem
  have hvec : Continuous (fun p : (S × (Fin n → C(Icc tmin tmax, E))) × ℝ ↦
      fun i ↦ compProj t₀ (p.1.2 i) p.2) :=
    continuous_snd.continuous_compProj_pi_apply₂ t₀
  exact continuous_eval.comp (hg_comp.prodMk hvec)

omit [CompleteSpace E] in
/-- The epsilon bound cancellation: when `ε' = ε / (4 * (1 + |T|) * (1 + M^n))`, we have
`ε' * M^n * T ≤ ε / 4`. This is the key arithmetic fact used in equicontinuity estimates. -/
lemma epsilon_bound_cancellation {ε M T : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hT : 0 ≤ T) (n : ℕ) :
    ε / (4 * (1 + |T|) * (1 + M ^ n)) * M ^ n * T ≤ ε / 4 := by
  have h1 : T ≤ 1 + |T| := (le_abs_self _).trans (le_add_of_nonneg_left (by linarith))
  have h2 : M ^ n ≤ 1 + M ^ n := le_add_of_nonneg_left (by linarith)
  have hε' : 0 < ε / (4 * (1 + |T|) * (1 + M ^ n)) := by
    refine div_pos hε (mul_pos (mul_pos (by linarith) ?_) ?_) <;> positivity
  calc ε / (4 * (1 + |T|) * (1 + M ^ n)) * M ^ n * T
      ≤ ε / (4 * (1 + |T|) * (1 + M ^ n)) * (1 + M ^ n) * (1 + |T|) := by
        apply mul_le_mul _ h1 hT (by positivity)
        exact mul_le_mul_of_nonneg_left h2 (le_of_lt hε')
    _ = ε / 4 := by
      have : 1 + M ^ n ≠ 0 := by positivity
      have : 1 + |T| ≠ 0 := by positivity
      field_simp

/-- Key neighborhood estimate for equicontinuity: near any `α₀`, all `α` in a neighborhood satisfy
a distance bound for `integralCMLM` applied to bounded `dα`. -/
lemma integralCMLM_eventually_dist_lt {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hg : ContinuousOn g u) (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α₀ : {α : C(Icc tmin tmax, E) | MapsTo α univ u}) {ε : ℝ} (hε : 0 < ε)
    {M : ℝ} (hM : 0 ≤ M) {B : Set (Fin n → C(Icc tmin tmax, E))} (hB : ∀ dα ∈ B, ‖dα‖ ≤ M) :
    ∀ᶠ α in 𝓝 α₀, ∀ dα ∈ B, dist ((integralCMLM hg t₀ ↑α₀) dα)
      ((integralCMLM hg t₀ ↑α) dα) < ε / 2 := by
  let S := {α : C(Icc tmin tmax, E) | MapsTo α univ u}
  have hS_open : IsOpen S := ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu
  let M' := max M 0
  let ε' := ε / (4 * (1 + |tmax - tmin|) * (1 + M' ^ n))
  have hε' : 0 < ε' := by
    refine div_pos hε (mul_pos (mul_pos (by linarith) ?_) ?_) <;> positivity
  have hS_nhd : ∀ᶠ x in 𝓝 (α₀ : C(Icc tmin tmax, E)), x ∈ S := hS_open.mem_nhds α₀.2
  rw [← map_nhds_subtype_coe_eq_nhds α₀.2 hS_nhd, Filter.eventually_map]
  let gComp : S → C(Icc tmin tmax, E [×n]→L[ℝ] E) := fun α ↦
    ⟨fun t ↦ g (α.1 t), hg.comp_continuous α.1.continuous_toFun (fun t ↦ α.2 (mem_univ t))⟩
  have hg_unif : Continuous gComp := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have h1 : Continuous (fun p : S × Icc tmin tmax ↦ (p.1 : C(Icc tmin tmax, E)) p.2) :=
      continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)
    exact hg.comp_continuous h1 fun ⟨α, t⟩ ↦ α.2 (mem_univ t)
  have hV_mem : gComp ⁻¹' Metric.ball (gComp α₀) ε' ∈ 𝓝 α₀ :=
    hg_unif.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε')
  apply Filter.eventually_of_mem hV_mem
  intro α hα dα hdα
  have hα_ball : dist (gComp α₀) (gComp α) < ε' := by
    rw [dist_comm]
    exact Metric.mem_ball.mp hα
  have hg_close : ∀ s : Icc tmin tmax, ‖g (α₀.1 s) - g (α.1 s)‖ ≤ ε' := fun s ↦ by
    calc ‖g (α₀.1 s) - g (α.1 s)‖ = ‖gComp α₀ s - gComp α s‖ := rfl
      _ ≤ dist (gComp α₀) (gComp α) := by
        rw [← dist_eq_norm]
        exact ContinuousMap.dist_apply_le_dist s
      _ ≤ ε' := le_of_lt hα_ball
  have hdα_bound : ∀ i, ‖dα i‖ ≤ M' := fun i ↦
    (norm_le_pi_norm dα i).trans ((hB dα hdα).trans (le_max_left M 0))
  have hε'_eq : ε' * M' ^ n * (tmax - tmin) ≤ ε / 4 :=
    epsilon_bound_cancellation hε (le_max_right M 0) (by linarith [t₀.2.1, t₀.2.2]) n
  calc dist ((integralCMLM hg t₀ ↑α₀) dα) ((integralCMLM hg t₀ ↑α) dα)
      ≤ ε' * M' ^ n * (tmax - tmin) := dist_integralCMLM_le hg t₀ α₀.2 α.2 hε'
          (le_max_right M 0) hg_close hdα_bound
    _ ≤ ε / 4 := hε'_eq
    _ < ε / 2 := by linarith

lemma continuousOn_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    ContinuousOn (integralCMLM hg t₀) {α : C(Icc tmin tmax, E) | MapsTo α univ u} := by
  let S := {α : C(Icc tmin tmax, E) | MapsTo α univ u}
  rw [continuousOn_iff_continuous_restrict,
    ContinuousMultilinearMap.isEmbedding_toUniformOnFun.continuous_iff,
    UniformOnFun.continuous_rng_iff]
  intro B hB
  rw [← equicontinuous_iff_continuous]
  have hB_bdd : Bornology.IsBounded B := NormedSpace.isVonNBounded_iff ℝ |>.mp hB
  intro α₀
  rw [equicontinuousAt_iff_pair]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨M, hM⟩ := hB_bdd.exists_norm_le
  have key := integralCMLM_eventually_dist_lt hg hu t₀ α₀ hε (le_max_right M 0)
    (fun dα hdα ↦ (hM dα hdα).trans (le_max_left M 0))
  obtain ⟨V, hV_nhd, hV⟩ := key.exists_mem
  let V' : Set S := Subtype.val ⁻¹' V
  have hV'_nhd : V' ∈ 𝓝 α₀ := continuous_subtype_val.continuousAt.preimage_mem_nhds hV_nhd
  refine ⟨V', hV'_nhd, fun x hx y hy ⟨dα, hdα⟩ ↦ ?_⟩
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
