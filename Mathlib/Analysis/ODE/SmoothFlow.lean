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

/-- The segment from `x` to `y` is contained in the closed ball centered at `x` with radius
`dist x y`. -/
-- TODO: this is the "left" version. make a "right" version too
lemma segment_subset_closedBall {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) : segment ℝ x y ⊆ Metric.closedBall x (dist x y) :=
  (convex_closedBall x _).segment_subset (Metric.mem_closedBall_self dist_nonneg)
    (Metric.mem_closedBall.mpr (dist_comm y x ▸ le_refl _))

/-- `f` maps `univ` into `t` if and only if the range of `f` is contained in `t`. -/
lemma Set.mapsTo_univ_iff_range_subset {α : Type*} {β : Type*} {t : Set β} {f : α → β} :
    MapsTo f univ t ↔ range f ⊆ t :=
  mapsTo_univ_iff.trans range_subset_iff.symm

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
    {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    Continuous (fun τ ↦ g (compProj t₀ α τ)) :=
  hg.comp_continuous (continuous_compProj t₀ α) (fun _ ↦ hα (mem_range_self _))

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
    (hf_mem : ∀ x, range (f x) ⊆ u) :
    Continuous (fun p : X × ℝ ↦ g (compProj t₀ (f p.1) p.2)) :=
  hg.comp_continuous (hf.continuous_compProj_pi₂ t₀) fun p ↦ hf_mem p.1 (mem_range_self _)

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
    (hα : range α ⊆ u) (dα : Fin n → C(Icc tmin tmax, E)) :
    Continuous (fun τ ↦ g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)) :=
  continuous_eval.comp ((hg.continuous_comp_compProj t₀ hα).prodMk
    (continuous_pi fun j ↦ continuous_compProj t₀ (dα j)))

/-- The integrand is interval integrable. -/
lemma intervalIntegrable_integrand {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hg : ContinuousOn g u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) (dα : Fin n → C(Icc tmin tmax, E))
    (a b : Icc tmin tmax) :
    IntervalIntegrable (fun τ ↦ g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)) volume a b :=
  (continuous_integrand hg t₀ hα dα).intervalIntegrable a b

/-- Parametric version of `continuous_integrand`: the integrand is jointly continuous
in `dα` and the integration variable. -/
lemma continuous_integrand_pi₂ {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    Continuous (fun p : (Fin n → C(Icc tmin tmax, E)) × ℝ ↦
      g (compProj t₀ α p.2) (fun i ↦ compProj t₀ (p.1 i) p.2)) :=
  continuous_eval.comp (((hg.continuous_comp_compProj t₀ hα).comp continuous_snd).prodMk
    (continuous_id.continuous_compProj_pi_apply₂ t₀))

variable [CompleteSpace E]

lemma continuous_integralFun {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) (dα : Fin n → C(Icc tmin tmax, E)) :
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
    (hα : range α ⊆ u) (dα : Fin n → C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) where
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
  if hα : range α ⊆ u then integralCMAux hg t₀ hα dα else 0

open Classical in
lemma integralCM_def {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    integralCM hg t₀ α =
      fun dα ↦ if hα : range α ⊆ u then integralCMAux hg t₀ hα dα else 0 := rfl

lemma integralCM_if_pos {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    integralCM hg t₀ α = integralCMAux hg t₀ hα := by
  simp [integralCM_def, dif_pos hα]

lemma integralCM_if_neg {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)}
    (hα : ¬ range α ⊆ u) :
    integralCM hg t₀ α = fun _ ↦ 0 := by
  simp [integralCM_def, dif_neg hα]

lemma integralCM_apply_if_pos {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u)
    {dα : Fin n → C(Icc tmin tmax, E)} {t : Icc tmin tmax} :
    integralCM hg t₀ α dα t = integralFun g t₀ α dα t := by
  simp [integralCM_def, dif_pos hα, integralCMAux]

lemma integralCM_apply_if_neg {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} (hα : ¬ range α ⊆ u)
    {dα : Fin n → C(Icc tmin tmax, E)} {t : Icc tmin tmax} :
    integralCM hg t₀ α dα t = 0 := by
  simp [integralCM_def, dif_neg hα]

-- TODO: Should this proof and `integralCM_update_smul` be pushed up to `integralFun`?
lemma integralCM_update_add {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n) (x y : C(Icc tmin tmax, E)) :
    integralCM hg t₀ α (update dα i (x + y)) =
      integralCM hg t₀ α (update dα i x) + integralCM hg t₀ α (update dα i y) := by
  by_cases hα : range α ⊆ u
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
  by_cases hα : range α ⊆ u
  · simp only [integralCM_if_pos hα, ContinuousMap.ext_iff, ContinuousMap.smul_apply]
    intro t
    simp only [integralCMAux, ContinuousMap.coe_mk, integralFun]
    rw [← intervalIntegral.integral_smul, integral_congr fun τ _ ↦ ?_]
    simpa only [compProj_update] using (g (compProj t₀ α τ)).toMultilinearMap.map_update_smul ..
  · simp [integralCM_if_neg hα]

lemma continuous_integralCM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    Continuous (integralCM hg t₀ α) := by
  by_cases hα : range α ⊆ u
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
    (hg : ContinuousOn g u) (α : {α : C(I, E) | range α ⊆ u}) : C(I, F) :=
  ⟨g ∘ α, hg.comp_continuous α.1.continuous_toFun (fun _ ↦ α.2 (mem_range_self _))⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma gComp_apply_projIcc {F : Type*} [TopologicalSpace F] {g : E → F} {u : Set E}
    (hg : ContinuousOn g u) {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {α : {α : C(Icc tmin tmax, E) | range α ⊆ u}} (t : ℝ) :
    gComp (Icc tmin tmax) hg α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t) =
      g (compProj t₀ α t) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma continuous_gComp {F : Type*} [TopologicalSpace F] {g : E → F} {u : Set E}
    (hg : ContinuousOn g u) (tmin tmax : ℝ) :
    Continuous (gComp (Icc tmin tmax) hg) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  refine hg.comp_continuous ?_ fun ⟨α, _⟩ ↦ α.2 (mem_range_self _)
  exact continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)

lemma continuousOn_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    ContinuousOn (integralCMLM g u t₀) {α : C(Icc tmin tmax, E) | range α ⊆ u} := by
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

lemma _root_.IsCompact.exists_mem_open_dist_lt_of_continuousOn
    {X : Type*} [PseudoMetricSpace X] {Y : Type*} [PseudoMetricSpace Y]
    {u : Set X} {s : Set X} {f : X → Y} (hs : IsCompact s) (hf : ContinuousOn f u) (hu : IsOpen u)
    (hsu : s ⊆ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y, dist x y < δ → y ∈ u ∧ dist (f x) (f y) < ε := by
  obtain ⟨δ₁, hδ₁, hthick⟩ := hs.exists_thickening_subset_open hu hsu
  have h := fun x (hx : x ∈ s) ↦ Metric.continuousOn_iff.mp hf x (hsu hx) (ε / 2) (half_pos hε)
  choose δₓ hδₓ h using h
  let c : s → Set X := fun ⟨x, hx⟩ ↦ ball x (δₓ x hx)
  have hcover : s ⊆ ⋃ i, c i := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hδₓ x hx)⟩
  obtain ⟨δ₂, hδ₂, hleb⟩ := lebesgue_number_lemma_of_metric hs (fun _ ↦ isOpen_ball) hcover
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx y hxy ↦ ?_⟩
  have hy : y ∈ u := by
    apply hthick
    rw [mem_thickening_iff]
    refine ⟨x, hx, ?_⟩
    rw [dist_comm]
    exact hxy.trans_le (min_le_left _ _)
  refine ⟨hy, ?_⟩
  obtain ⟨⟨z, hz⟩, hball⟩ := hleb x hx
  have hx' : dist x z < (δₓ z hz) := by
    rw [← mem_ball]
    exact hball (mem_ball_self hδ₂)
  have hy' : dist y z < (δₓ z hz) := by
    rw [← mem_ball]
    apply hball
    rw [mem_ball, dist_comm]
    exact hxy.trans_le (min_le_right _ _)
  calc dist (f x) (f y)
      ≤ dist (f x) (f z) + dist (f z) (f y) := dist_triangle _ _ _
    _ = dist (f x) (f z) + dist (f y) (f z) := by rw [dist_comm (f z) (f y)]
    _ < ε / 2 + ε / 2 := add_lt_add
        (h z hz x (hsu hx) (Metric.mem_ball.mp hx'))
        (h z hz y hy (Metric.mem_ball.mp hy'))
    _ = ε := by ring

/--
The derivative of `integralCMLM g u t₀` in `C(Icc tmin tmax, E)` is given by `integralCMLM g' u t₀`,
where `g'` is the derivative of `g` in `E`.
-/
lemma fderiv_integralCMLM' {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContDiffOn ℝ 1 g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) :
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
  have hpos : 0 < ε / (1 + |tmax - tmin|) := by positivity
  obtain ⟨δ, hδ, h⟩ := (isCompact_range α.continuous).exists_mem_open_dist_lt_of_continuousOn
    (hg.continuousOn_fderiv_of_isOpen hu le_rfl) hu hα hpos
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun dα₀ hdα₀ ↦ ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro dα
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have hg' := hg.continuousOn_continuousMultilinearCurryLeftEquiv_fderiv hu
  have hα_add : range (α + dα₀) ⊆ u := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    refine (h (α t) (mem_range_self t) _ ?_).1
    rw [dist_eq_norm, ContinuousMap.add_apply, sub_add_cancel_left, norm_neg]
    apply (ContinuousMap.norm_coe_le_norm dα₀ t).trans_lt
    rwa [← dist_zero_right]
  have hinteg₁ := intervalIntegrable_integrand hg.continuousOn t₀ hα_add dα t₀ t
  have hinteg₂ := intervalIntegrable_integrand hg.continuousOn t₀ hα dα t₀ t
  have hinteg₃ := intervalIntegrable_integrand hg' t₀ hα (Fin.cons dα₀ dα) t₀ t
  rw [sub_apply, sub_apply, continuousMultilinearCurryLeftEquiv_apply,
    integralCMLM_apply_if_pos hg.continuousOn, integralCMLM_apply_if_pos hg.continuousOn,
    integralCMLM_apply_if_pos hg', ContinuousMap.sub_apply, ContinuousMap.sub_apply,
    integralCM_apply_if_pos hα_add, integralCM_apply_if_pos hα, integralCM_apply_if_pos hα,
    integralFun, integralFun, integralFun, ← intervalIntegral.integral_sub hinteg₁ hinteg₂,
    ← intervalIntegral.integral_sub (hinteg₁.sub hinteg₂) hinteg₃]
  set C := ε / (1 + |tmax - tmin|) * ‖dα₀‖ * ∏ i, ‖dα i‖ with hC
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) _).trans
  · -- repeated
    have : |(t : ℝ) - t₀| ≤ |tmax - tmin| := by
      apply abs_le_abs <;> linarith [t.2.1, t.2.2, t₀.2.1, t₀.2.2]
    rw [hC, mul_comm, ← mul_assoc, ← mul_assoc, mul_div_left_comm]
    gcongr
    apply mul_le_of_le_one_right hε.le
    rw [div_le_one (by positivity)]
    apply (le_add_of_nonneg_left zero_le_one).trans
    gcongr
  · intro τ hτ
    rw [continuousMultilinearCurryLeftEquiv_symm_apply, Fin.cons_zero, Fin.tail_def]
    simp_rw [Fin.cons_succ]
    rw [← ContinuousMultilinearMap.sub_apply, ← ContinuousMultilinearMap.sub_apply, hC]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    apply mul_le_mul _
      (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ (dα _).norm_coe_le_norm  _))
      (by positivity) (by positivity)
    let x := compProj t₀ α τ
    let y := compProj t₀ (α + dα₀) τ
    calc
      _ = ‖g y - g x - (fderiv ℝ g x) (y - x)‖ := by
        simp only [y, x, compProj, ContinuousMap.add_apply, add_sub_cancel_left]
      _ ≤ ε / (1 + |tmax - tmin|) * ‖y - x‖ := by
        apply Convex.norm_image_sub_le_of_norm_fderiv_le' _ _ (convex_segment x y)
          (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
        · intro z hz
          apply (hg.differentiableOn one_ne_zero).differentiableAt (hu.mem_nhds _)
          apply (h x (mem_range_self _) z _).1
          apply (mem_closedBall'.mp (segment_subset_closedBall x y hz)).trans_lt
          rw [dist_comm, dist_eq_norm]
          simp only [y, x, compProj, ContinuousMap.add_apply, add_sub_cancel_left]
          exact (ContinuousMap.norm_coe_le_norm dα₀ _).trans_lt hdα₀
        · intro z hz
          rw [← dist_eq_norm, dist_comm]
          apply (h x (mem_range_self _) z _).2.le
          apply (mem_closedBall'.mp (segment_subset_closedBall x y hz)).trans_lt
          rw [dist_comm, dist_eq_norm]
          simp only [y, x, compProj, ContinuousMap.add_apply, add_sub_cancel_left]
          exact (ContinuousMap.norm_coe_le_norm dα₀ _).trans_lt hdα₀
      _ ≤ ε / (1 + |tmax - tmin|) * ‖dα₀‖ := by
        gcongr
        simp only [y, x, compProj, ContinuousMap.add_apply, add_sub_cancel_left]
        exact ContinuousMap.norm_coe_le_norm dα₀ _

end

end SmoothFlow
