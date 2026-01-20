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

open Function intervalIntegral MeasureTheory Metric Set ContinuousMultilinearMap
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

lemma compProj_of_mem {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} {t : ℝ}
    (ht : t ∈ Icc tmin tmax) :
    compProj t₀ α t = α ⟨t, ht⟩ := by
  rw [compProj, projIcc_of_mem (le_trans t₀.2.1 t₀.2.2) ht]

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

lemma integralCM_apply_if_pos {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} (hα : MapsTo α univ u)
    {dα : Fin n → C(Icc tmin tmax, E)} {t : Icc tmin tmax} :
    integralCM hg t₀ α dα t = integralFun g t₀ α dα t := by
  simp [integralCM_def, dif_pos hα, integralCMAux]

lemma integralCM_apply_if_neg {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} (hα : ¬ MapsTo α univ u)
    {dα : Fin n → C(Icc tmin tmax, E)} {t : Icc tmin tmax} :
    integralCM hg t₀ α dα t = 0 := by
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
def integralCMLMAux {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) [×n]→L[ℝ] C(Icc tmin tmax, E) where
  toFun := integralCM hg t₀ α
  -- `ContinuousMultilinearMap` asks for a proof for arbitrary `[DecidableEq ι]`, which is why we
  -- need `convert` here
  map_update_add' dα i α₁ α₂ := by convert integralCM_update_add hg t₀ α dα i α₁ α₂
  map_update_smul' dα i c α₁ := by convert integralCM_update_smul hg t₀ α dα i c α₁
  cont := continuous_integralCM ..

@[simp]
lemma integralCMLMAux_apply {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)}
    {dα : Fin n → C(Icc tmin tmax, E)} :
    integralCMLMAux hg t₀ α dα = integralCM hg t₀ α dα := rfl

open Classical in
/--
The integral as a continuous multilinear map on the space of continuous curves, as a global function
of `g` (later taken to be the `n`-th derivative of the vector field `E → E`), using the junk value
pattern
-/
def integralCMLM {n : ℕ} (g : E → E [×n]→L[ℝ] E) (u : Set E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) [×n]→L[ℝ] C(Icc tmin tmax, E) :=
  if hg : ContinuousOn g u then integralCMLMAux hg t₀ α else 0

lemma integralCMLM_apply_if_pos {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} {dα : Fin n → C(Icc tmin tmax, E)}
    (hg : ContinuousOn g u) :
    integralCMLM g u t₀ α dα = integralCM hg t₀ α dα := by
  rw [integralCMLM, dif_pos hg, integralCMLMAux_apply]

lemma integralCMLM_apply_if_neg {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} {dα : Fin n → C(Icc tmin tmax, E)}
    (hg : ¬ ContinuousOn g u) :
    integralCMLM g u t₀ α dα = 0 := by
  rw [integralCMLM, dif_neg hg, zero_apply]

def gComp (I : Type*) {F : Type*} [TopologicalSpace I] [TopologicalSpace F] {g : E → F} {u : Set E}
    (hg : ContinuousOn g u) (α : {α : C(I, E) | MapsTo α univ u}) : C(I, F) :=
  ⟨g ∘ α, hg.comp_continuous α.1.continuous_toFun (fun _ ↦ α.2 trivial)⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma gComp_apply_projIcc {F : Type*} [TopologicalSpace F] {g : E → F} {u : Set E}
    (hg : ContinuousOn g u) {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {α : {α : C(Icc tmin tmax, E) | MapsTo α univ u}} (t : ℝ) :
    gComp (Icc tmin tmax) hg α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t) =
      g (compProj t₀ α t) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma continuous_gComp {F : Type*} [TopologicalSpace F] {g : E → F} {u : Set E}
    (hg : ContinuousOn g u) (tmin tmax : ℝ) :
    Continuous (gComp (Icc tmin tmax) hg) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  refine hg.comp_continuous ?_ fun ⟨α, _⟩ ↦ α.2 trivial
  exact continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)

lemma continuousOn_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    ContinuousOn (integralCMLM g u t₀) {α : C(Icc tmin tmax, E) | MapsTo α univ u} := by
  -- embed `ContinuousMultilinearMap` into `UniformOnFun` and use notion of continuity there
  rw [continuousOn_iff_continuous_restrict, isEmbedding_toUniformOnFun.continuous_iff,
    UniformOnFun.continuous_rng_iff]
  intro B hB
  rw [mem_setOf, NormedSpace.isVonNBounded_iff] at hB
  rw [← equicontinuous_iff_continuous]
  simp_rw [comp_apply, restrict_apply, toUniformOnFun_toFun]
  intro α₀
  simp_rw [EquicontinuousAt, Subtype.forall] -- redundant?
  intro U hU
  -- express in terms of `ε`-`δ`
  obtain ⟨ε, hε, hεU⟩ := mem_uniformity_dist.mp hU
  obtain ⟨C, hC⟩ := hB.exists_norm_le
  -- `max C 0` to avoid needing `B` to be nonempty
  -- `1 +` to ensure strict positivity
  let δ := ε / ((1 + |tmax - tmin|) * (1 + (max C 0) ^ n))
  have hδ : 0 < δ := div_pos hε (mul_pos (by positivity) (by positivity))
  let V := ball (gComp (Icc tmin tmax) hg α₀) δ
  have hV : (gComp (Icc tmin tmax) hg) ⁻¹' ball (gComp (Icc tmin tmax) hg α₀) δ ∈ 𝓝 α₀ :=
    (continuous_gComp hg tmin tmax).continuousAt.preimage_mem_nhds (ball_mem_nhds _ hδ)
  apply Filter.eventually_of_mem hV
  intro α hα dα hdα
  rw [mem_preimage, mem_ball, ContinuousMap.dist_lt_iff hδ] at hα
  apply hεU
  rw [integralCMLM_apply_if_pos hg, integralCMLM_apply_if_pos hg, ContinuousMap.dist_lt_iff hε]
  intro t
  rw [integralCM_apply_if_pos α₀.2, integralCM_apply_if_pos α.2, dist_eq_norm, integralFun,
    integralFun, ← integral_sub (intervalIntegrable_integrand hg _ α₀.2 ..)
      (intervalIntegrable_integrand hg _ α.2 ..)]
  calc
    _ ≤ δ * (max C 0) ^ n * |↑t - ↑t₀| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro τ hτ
      replace hτ : τ ∈ Icc tmin tmax := uIcc_subset_Icc t₀.2 t.2 (uIoc_subset_uIcc hτ)
      rw [← sub_apply, compProj_of_mem hτ, compProj_of_mem hτ]
      apply (le_opNorm _ _).trans
      rw [← dist_eq_norm, dist_comm]
      apply mul_le_mul (hα _).le _ (by positivity) (by positivity)
      have heq' : n = (Finset.univ : Finset (Fin n)).card := by simp
      nth_rw 5 [heq']
      -- replace with `prod_le_pow_card'` that works on `ℝ`, not just `ℝ≥0`
      apply (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) _).trans_eq (Finset.prod_const _)
      intro i _
      rw [compProj_of_mem hτ]
      exact (ContinuousMap.norm_coe_le_norm _ _).trans
        ((norm_le_pi_norm dα i).trans ((hC dα hdα).trans (le_max_left ..)))
    _ ≤ δ * max C 0 ^ n * |↑tmax - ↑tmin| := by
      gcongr 1
      apply abs_le_abs <;> linarith [t.2.1, t.2.2, t₀.2.1, t₀.2.2]
    _ = ε * ((|tmax - tmin| * (max C 0 ^ n)) / ((1 + |tmax - tmin|) * (1 + max C 0 ^ n))) := by
      simp_rw [δ]
      field_simp
    _ < ε := by
      apply mul_lt_of_lt_one_right hε
      rw [div_lt_one (by positivity)]
      exact mul_lt_mul' (lt_one_add _).le (lt_one_add _) (by positivity) (by positivity)

/-
`g : E → E [×n]→L[ℝ] E`
Show the `α`-derivative of
`dα ↦ t ↦ ∫ τ in t₀..t, g (α τ) (dα τ)`
is `(dα₀ :: dα) ↦ t ↦ ∫ τ in t₀..t, fderiv ℝ g (α τ) (dα₀ τ) (dα τ)`
The latter has to be expressed as a `
-/

omit [CompleteSpace E] in
lemma _root_.ContDiffOn.continuousOn_continuousMultilinearCurryLeftEquiv_fderiv
    {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContDiffOn ℝ 1 g u) (hu : IsOpen u) :
    ContinuousOn
      (fun x ↦ (continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ E) E).symm (fderiv ℝ g x)) u := by
  simp_rw [← Function.comp_apply (g := fderiv ℝ g)]
  rw [LinearIsometryEquiv.comp_continuousOn_iff]
  exact hg.continuousOn_fderiv_of_isOpen hu le_rfl

lemma fderiv_integralCMLM' {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContDiffOn ℝ 1 g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) :
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ C(Icc tmin tmax, E)) C(Icc tmin tmax, E)).symm
        (fderiv ℝ (integralCMLM g u t₀) α) =
      integralCMLM
        (fun x ↦ (continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ E) E).symm (fderiv ℝ g x)) u t₀
        α := by
  rw [← (continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ C(Icc tmin tmax, E))
      C(Icc tmin tmax, E)).map_eq_iff, LinearIsometryEquiv.apply_symm_apply]
  apply HasFDerivAt.fderiv
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let V : Set C(Icc tmin tmax, E) := sorry
  have hV : V ∈ 𝓝 0 := sorry
  apply Filter.eventually_of_mem hV
  intro dα₀ hdα₀
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro dα
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have hg' := hg.continuousOn_continuousMultilinearCurryLeftEquiv_fderiv hu
  have hα_add : MapsTo (α + dα₀) univ u := sorry
  have hinteg₁ := intervalIntegrable_integrand hg.continuousOn t₀ hα_add dα t₀ t
  have hinteg₂ := intervalIntegrable_integrand hg.continuousOn t₀ hα dα t₀ t
  have hinteg₃ := intervalIntegrable_integrand hg' t₀ hα (Fin.cons dα₀ dα) t₀ t
  rw [sub_apply, sub_apply, continuousMultilinearCurryLeftEquiv_apply,
    integralCMLM_apply_if_pos hg.continuousOn, integralCMLM_apply_if_pos hg.continuousOn,
    integralCMLM_apply_if_pos hg', ContinuousMap.sub_apply, ContinuousMap.sub_apply,
    integralCM_apply_if_pos hα_add, integralCM_apply_if_pos hα, integralCM_apply_if_pos hα,
    integralFun, integralFun, integralFun, ← intervalIntegral.integral_sub hinteg₁ hinteg₂,
    ← intervalIntegral.integral_sub (hinteg₁.sub hinteg₂) hinteg₃]
  let C : ℝ := sorry
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) _).trans
  · sorry
  · intro τ hτ
    rw [continuousMultilinearCurryLeftEquiv_symm_apply, Fin.cons_zero, Fin.tail_def]
    simp_rw [Fin.cons_succ]

    sorry

/--
The derivative of `integralCMLM g u t₀` in `C(Icc tmin tmax, E)` is given by `integralCMLM g' u t₀`,
where `g'` is the derivative of `g` in `E`.
-/
lemma fderiv_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContDiffOn ℝ 1 g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : MapsTo α univ u) :
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ C(Icc tmin tmax, E)) C(Icc tmin tmax, E)).symm
        (fderiv ℝ (integralCMLM g u t₀) α) =
      integralCMLM
        (fun x ↦ (continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ E) E).symm (fderiv ℝ g x)) u t₀
        α := by
  rw [← (continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ C(Icc tmin tmax, E))
      C(Icc tmin tmax, E)).map_eq_iff, LinearIsometryEquiv.apply_symm_apply]
  apply HasFDerivAt.fderiv
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε


  -----AI start
  -- The image of α is compact, and it lies in the open set u
  have hcompact : IsCompact (range α) := isCompact_range α.continuous
  have hrange_sub : range α ⊆ u := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    exact hα trivial
  -- Find δ₁ > 0 such that thickening δ₁ (range α) ⊆ u
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hcompact.exists_thickening_subset_open hu hrange_sub
  -- The derivative fderiv ℝ g is uniformly continuous on the compact set range α
  have hfderiv_cont : ContinuousOn (fderiv ℝ g) (range α) :=
    (hg.continuousOn_fderiv_of_isOpen hu le_rfl).mono hrange_sub
  have hfderiv_unifCont : UniformContinuousOn (fderiv ℝ g) (range α) :=
    hcompact.uniformContinuousOn_of_continuous hfderiv_cont
  -- Use a scaled ε to account for the integration interval length
  let ε' := ε / (1 + |tmax - tmin|)
  have hε'_pos : 0 < ε' := div_pos hε (by positivity)
  -- Get δ₂ from uniform continuity such that ‖fderiv g x - fderiv g y‖ < ε' when ‖x - y‖ < δ₂
  rw [Metric.uniformContinuousOn_iff] at hfderiv_unifCont
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hfderiv_unifCont ε' hε'_pos
  -- Get δ₃ from continuity of fderiv ℝ g on u, such that for all x ∈ range α and z ∈ u,
  -- dist z x < δ₃ → dist (fderiv ℝ g z) (fderiv ℝ g x) < ε'
  -- This uses that fderiv is continuous on u ⊇ range α, and range α is compact
  have hfderiv_cont_u : ContinuousOn (fderiv ℝ g) u := hg.continuousOn_fderiv_of_isOpen hu le_rfl
  -- For each x ∈ range α, fderiv ℝ g is continuous at x, giving a ball where it's ε'-close
  -- By compactness of range α, we can find a uniform δ₃
  have hδ₃_exists : ∃ δ₃ > 0, ∀ x ∈ range α, ∀ z ∈ u,
      dist z x < δ₃ → dist (fderiv ℝ g z) (fderiv ℝ g x) < ε' := by
    -- Use compactness: for each x ∈ range α, continuity at x gives δₓ
    -- Use ε'/2 so that triangle inequality gives ε'/2 + ε'/2 = ε'
    have hε'2_pos : 0 < ε' / 2 := by linarith
    have h : ∀ x ∈ range α, ∃ δₓ > 0, ∀ z ∈ u,
        dist z x < δₓ → dist (fderiv ℝ g z) (fderiv ℝ g x) < ε' / 2 := by
      intro x hx
      have hcont : ContinuousAt (fderiv ℝ g) x :=
        hfderiv_cont_u.continuousAt (hu.mem_nhds (hrange_sub hx))
      rw [Metric.continuousAt_iff] at hcont
      obtain ⟨δₓ, hδₓ_pos, hδₓ⟩ := hcont (ε' / 2) hε'2_pos
      exact ⟨δₓ, hδₓ_pos, fun z _ hz ↦ hδₓ hz⟩
    -- Use Lebesgue number lemma with the open cover {ball x δₓ}
    choose δₓ hδₓ_pos hδₓ using h
    -- The open cover: for each x ∈ range α, the ball of radius δₓ x hx
    let c : range α → Set E := fun ⟨x, hx⟩ ↦ Metric.ball x (δₓ x hx)
    have hc_open : ∀ i, IsOpen (c i) := fun _ ↦ Metric.isOpen_ball
    have hc_cover : range α ⊆ ⋃ i, c i := by
      intro y hy
      simp only [Set.mem_iUnion, Subtype.exists]
      exact ⟨y, hy, Metric.mem_ball_self (hδₓ_pos y hy)⟩
    obtain ⟨δ₃, hδ₃_pos, hδ₃_lebesgue⟩ := lebesgue_number_lemma_of_metric hcompact hc_open hc_cover
    refine ⟨δ₃, hδ₃_pos, fun x hx z hz hdist ↦ ?_⟩
    -- By Lebesgue number, ball x δ₃ ⊆ some ball y (δₓ y hy) for some y ∈ range α
    obtain ⟨⟨y, hy⟩, hball_sub⟩ := hδ₃_lebesgue x hx
    -- z ∈ ball x δ₃, so z ∈ ball y (δₓ y hy)
    have hz_in_bally : z ∈ Metric.ball y (δₓ y hy) := hball_sub (Metric.mem_ball.mpr hdist)
    have hx_in_bally : x ∈ Metric.ball y (δₓ y hy) := hball_sub (Metric.mem_ball_self hδ₃_pos)
    have hdist_zy : dist z y < δₓ y hy := Metric.mem_ball.mp hz_in_bally
    have hdist_xy : dist x y < δₓ y hy := Metric.mem_ball.mp hx_in_bally
    -- Triangle inequality: dist (fderiv g z) (fderiv g x) < ε'/2 + ε'/2 = ε'
    calc dist (fderiv ℝ g z) (fderiv ℝ g x)
        ≤ dist (fderiv ℝ g z) (fderiv ℝ g y) + dist (fderiv ℝ g y) (fderiv ℝ g x) :=
          dist_triangle _ _ _
      _ = dist (fderiv ℝ g z) (fderiv ℝ g y) + dist (fderiv ℝ g x) (fderiv ℝ g y) := by
          rw [dist_comm (fderiv ℝ g y)]
      _ < ε' / 2 + ε' / 2 :=
          add_lt_add (hδₓ y hy z hz hdist_zy) (hδₓ y hy x (hrange_sub hx) hdist_xy)
      _ = ε' := by ring
  obtain ⟨δ₃, hδ₃_pos, hδ₃⟩ := hδ₃_exists
  -- Choose δ = min (δ₁ / 2) (min δ₂ (δ₃ / 2)), and let V = ball 0 δ
  -- Using δ₃/2 ensures strict inequality when applying hδ₃
  let δ := min (δ₁ / 2) (min δ₂ (δ₃ / 2))
  have hδ_pos : 0 < δ := lt_min (by linarith) (lt_min hδ₂_pos (by linarith))
  have hδ_le_δ₁ : δ ≤ δ₁ / 2 := min_le_left _ _
  have hδ_le_δ₂ : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_lt_δ₃ : δ < δ₃ := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
  let V : Set C(Icc tmin tmax, E) := Metric.ball 0 δ
  have hV : V ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hδ_pos
  ----------AI end




  apply Filter.eventually_of_mem hV
  intro dα₀ hdα₀



  ----------AI start
  rw [Metric.mem_ball, dist_zero_right] at hdα₀
  -- Key fact: α + dα₀ maps into u (actually into thickening δ₁ (range α))
  have hα_add : MapsTo (α + dα₀) univ u := by
    intro x _
    apply hδ₁
    rw [Metric.mem_thickening_iff]
    refine ⟨α x, mem_range_self x, ?_⟩
    simp only [ContinuousMap.add_apply, dist_eq_norm, add_sub_cancel_left]
    calc ‖dα₀ x‖ ≤ ‖dα₀‖ := ContinuousMap.norm_coe_le_norm dα₀ x
      _ < δ := hdα₀
      _ ≤ δ₁ / 2 := hδ_le_δ₁
      _ < δ₁ := by linarith
  ----------AI end




  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro dα
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have hg' := hg.continuousOn_continuousMultilinearCurryLeftEquiv_fderiv hu
  have hinteg₁ := intervalIntegrable_integrand hg.continuousOn t₀ hα_add dα t₀ t
  have hinteg₂ := intervalIntegrable_integrand hg.continuousOn t₀ hα dα t₀ t
  have hinteg₃ := intervalIntegrable_integrand hg' t₀ hα (Fin.cons dα₀ dα) t₀ t
  rw [sub_apply, sub_apply, continuousMultilinearCurryLeftEquiv_apply,
    integralCMLM_apply_if_pos hg.continuousOn, integralCMLM_apply_if_pos hg.continuousOn,
    integralCMLM_apply_if_pos hg', ContinuousMap.sub_apply, ContinuousMap.sub_apply,
    integralCM_apply_if_pos hα_add, integralCM_apply_if_pos hα, integralCM_apply_if_pos hα,
    integralFun, integralFun, integralFun, ← intervalIntegral.integral_sub hinteg₁ hinteg₂,
    ← intervalIntegral.integral_sub (hinteg₁.sub hinteg₂) hinteg₃]




  ------------AI start
  -- The constant C for the pointwise bound: ε' * ‖dα₀‖ * ∏ᵢ ‖dα i‖
  let C : ℝ := ε' * ‖dα₀‖ * ∏ i, ‖dα i‖
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) _).trans
  · -- The integral bound: C * |t - t₀| ≤ ε * ‖dα₀‖ * ∏ᵢ ‖dα i‖
    simp only [C, ε']
    have h_interval : |(t : ℝ) - (t₀ : ℝ)| ≤ |tmax - tmin| := by
      have ht_lo : tmin ≤ (t : ℝ) := t.2.1
      have ht_hi : (t : ℝ) ≤ tmax := t.2.2
      have ht₀_lo : tmin ≤ (t₀ : ℝ) := t₀.2.1
      have ht₀_hi : (t₀ : ℝ) ≤ tmax := t₀.2.2
      have h1 : (t : ℝ) - (t₀ : ℝ) ≤ tmax - tmin := by linarith
      have h2 : -(tmax - tmin) ≤ (t : ℝ) - (t₀ : ℝ) := by linarith
      rw [abs_le]
      constructor
      · calc -|tmax - tmin| ≤ -(tmax - tmin) := neg_le_neg (le_abs_self _)
          _ ≤ (t : ℝ) - (t₀ : ℝ) := h2
      · exact h1.trans (le_abs_self _)
    have hprod_nonneg : 0 ≤ ∏ i, ‖dα i‖ := Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
    have hdenom_pos : 0 < 1 + |tmax - tmin| := by positivity
    calc (ε / (1 + |tmax - tmin|) * ‖dα₀‖ * ∏ i, ‖dα i‖) * |(t : ℝ) - (t₀ : ℝ)|
        ≤ (ε / (1 + |tmax - tmin|) * ‖dα₀‖ * ∏ i, ‖dα i‖) * |tmax - tmin| := by
          gcongr
      _ ≤ (ε / (1 + |tmax - tmin|) * ‖dα₀‖ * ∏ i, ‖dα i‖) * (1 + |tmax - tmin|) := by
          gcongr; linarith [abs_nonneg (tmax - tmin)]
      _ = ε * ‖dα₀‖ * ∏ i, ‖dα i‖ := by field_simp
  ------------AI end



  · intro τ hτ
    rw [continuousMultilinearCurryLeftEquiv_symm_apply, Fin.cons_zero, Fin.tail_def]
    simp_rw [Fin.cons_succ]




    ---------AI start
    -- We need: ‖(g(α+dα₀) - g(α) - fderiv g α dα₀) dα‖ ≤ ε' * ‖dα₀‖ * ∏ᵢ ‖dα i‖
    -- Rewrite to expose the ContinuousMultilinearMap subtraction structure
    rw [← ContinuousMultilinearMap.sub_apply, ← ContinuousMultilinearMap.sub_apply]
    -- First, factor out dα using opNorm bound
    apply (ContinuousMultilinearMap.le_opNorm _ _).trans
    -- Now we need: ‖g(α+dα₀) - g(α) - fderiv g α dα₀‖ * ∏ᵢ ‖dα i τ'‖ ≤ C
    simp only [C, ε']
    gcongr
    case h₁ =>
      -- Need: ‖g((α+dα₀) τ') - g(α τ') - fderiv g (α τ') (dα₀ τ')‖ ≤ ε' * ‖dα₀‖
      -- Set up the points
      let τ' := projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) τ
      let x := α τ'
      let y := (α + dα₀) τ'
      -- Note: y - x = dα₀ τ'
      have hyx : y - x = dα₀ τ' := by simp only [y, x, ContinuousMap.add_apply, add_sub_cancel_left]
      -- compProj evaluates to function application at τ'
      have hcompProj_α : compProj t₀ α τ = x := rfl
      have hcompProj_αdα₀ : compProj t₀ (α + dα₀) τ = y := rfl
      have hcompProj_dα₀ : compProj t₀ dα₀ τ = dα₀ τ' := rfl
      -- Rewrite the goal in terms of x, y
      simp only [hcompProj_α, hcompProj_αdα₀, hcompProj_dα₀, ← hyx]
      -- Use mean value theorem on the convex ball around x
      have hx_mem : x ∈ range α := mem_range_self τ'
      have hdα₀_τ' : ‖dα₀ τ'‖ ≤ ‖dα₀‖ := ContinuousMap.norm_coe_le_norm dα₀ τ'
      have hdist_xy : dist y x < δ := by
        rw [dist_eq_norm, hyx]
        exact hdα₀_τ'.trans_lt hdα₀
      -- y is in the closed ball around x with radius δ
      have hy_in_ball : y ∈ Metric.closedBall x δ := by
        rw [Metric.mem_closedBall]
        exact le_of_lt hdist_xy
      -- The segment [x, y] is contained in closedBall x δ
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      have hseg_sub_ball : segment ℝ x y ⊆ Metric.closedBall x δ :=
        (convex_closedBall x δ).segment_subset (Metric.mem_closedBall_self hδ_nonneg) hy_in_ball
      -- closedBall x δ ⊆ thickening δ₁ (range α) ⊆ u
      have hball_sub_u : Metric.closedBall x δ ⊆ u := by
        apply (Metric.closedBall_subset_ball _).trans
        · exact fun z hz ↦ hδ₁ (Metric.mem_thickening_iff.mpr ⟨x, hx_mem, hz⟩)
        · calc δ < δ₁ / 2 + δ₁ / 2 := by linarith [hδ_le_δ₁]
            _ = δ₁ := by ring
      have hseg_sub_u : segment ℝ x y ⊆ u := hseg_sub_ball.trans hball_sub_u
      -- g is differentiable on the segment
      have hdiff : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ g z :=
        fun z hz ↦ (hg.differentiableOn one_ne_zero).differentiableAt (hu.mem_nhds (hseg_sub_u hz))
      -- Bound the derivative difference on the segment
      -- Use continuity of fderiv ℝ g on u at x
      have hfderiv_cont_at : ContinuousAt (fderiv ℝ g) x := by
        apply (hg.continuousOn_fderiv_of_isOpen hu le_rfl).continuousAt
        exact hu.mem_nhds (hball_sub_u (Metric.mem_closedBall_self hδ_nonneg))
      -- fderiv ℝ g maps ball x δ₂ into ball (fderiv ℝ g x) ε'
      -- by uniform continuity on range α at x
      have hfderiv_near : ∀ z ∈ Metric.closedBall x δ, dist (fderiv ℝ g z) (fderiv ℝ g x) ≤ ε' := by
        intro z hz_ball
        have hz_dist : dist z x ≤ δ := Metric.mem_closedBall.mp hz_ball
        -- Key: we need to show dist (fderiv ℝ g z) (fderiv ℝ g x) ≤ ε'
        -- We have x ∈ range α, and dist z x ≤ δ ≤ δ₂
        -- The issue is that hδ₂ requires z ∈ range α
        -- But we can use the following: find w ∈ range α close to z, then use triangle inequality
        -- Actually, for z in ball x δ where δ ≤ δ₂, we can directly bound using
        -- continuity of fderiv on u.
        -- Since fderiv ℝ g is continuous on u at x, and we're looking at z with dist z x ≤ δ,
        -- if δ was chosen small enough for continuity at x, we'd have the bound.
        -- But our δ comes from uniform continuity on range α.
        -- The fix: since range α is compact and fderiv ℝ g is continuous on u ⊇ range α,
        -- by compactness, for each ε' > 0, there exists δ₃ > 0 such that
        -- for all x ∈ range α and z ∈ u with dist z x < δ₃, dist (fderiv g z) (fderiv g x) < ε'
        -- This is uniform continuity extended to a neighborhood.
        -- For now, we use the direct approach: fderiv ℝ g is continuous at x ∈ u.
        -- We know dist z x ≤ δ ≤ δ₂. We need dist z x < some δ' from continuity at x.
        -- The issue is that δ₂ comes from uniform continuity on range α, not continuity at x.
        -- However, since x ∈ range α ⊆ u and fderiv is continuous on u, by compactness of range α,
        -- the uniform continuity modulus on range α also works for nearby points in u.
        -- This is because fderiv ℝ g restricted to a compact neighborhood of range α in u
        -- is uniformly continuous.
        -- Actually, let's just use that z is close to x, and fderiv is continuous at x.
        -- The bound might be slightly weaker, but the structure is correct.
        -- For a rigorous proof, we would need to modify δ at the start.
        -- For now, complete with a placeholder using continuity at x.
        -- z is in the closed ball, hence in u
        have hz_in_u : z ∈ u := hball_sub_u hz_ball
        -- Use hδ₃: for x ∈ range α and z ∈ u with dist z x < δ₃,
        -- we have dist (fderiv g z) (fderiv g x) < ε'
        -- We have dist z x ≤ δ < δ₃ (by hδ_lt_δ₃)
        have hdist_lt_δ₃ : dist z x < δ₃ := hz_dist.trans_lt hδ_lt_δ₃
        exact le_of_lt (hδ₃ x hx_mem z hz_in_u hdist_lt_δ₃)
      have hderiv_bound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ ε' := by
        intro z hz
        rw [← dist_eq_norm]
        exact hfderiv_near z (hseg_sub_ball hz)
      -- Apply mean value theorem
      have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le' hdiff hderiv_bound
        (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
      calc ‖g y - g x - (fderiv ℝ g x) (y - x)‖
          ≤ ε' * ‖y - x‖ := hmvt
        _ = ε' * ‖dα₀ τ'‖ := by rw [hyx]
        _ ≤ ε' * ‖dα₀‖ := by gcongr
    case h₂.h1 =>
      -- Bound ‖compProj t₀ (dα i) τ‖ ≤ ‖dα i‖
      simp only [compProj]
      exact ContinuousMap.norm_coe_le_norm (dα _) _
    ------------AI end

end

end SmoothFlow
