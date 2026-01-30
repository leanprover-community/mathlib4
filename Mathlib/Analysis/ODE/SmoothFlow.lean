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
-- move somewhere
lemma segment_subset_closedBall {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) : segment ℝ x y ⊆ Metric.closedBall x (dist x y) :=
  (convex_closedBall x _).segment_subset (Metric.mem_closedBall_self dist_nonneg)
    (Metric.mem_closedBall.mpr (dist_comm y x ▸ le_refl _))

/-- `f` maps `univ` into `t` if and only if the range of `f` is contained in `t`. -/
-- TODO: move somewhere
lemma Set.mapsTo_univ_iff_range_subset {α : Type*} {β : Type*} {t : Set β} {f : α → β} :
    MapsTo f univ t ↔ range f ⊆ t :=
  mapsTo_univ_iff.trans range_subset_iff.symm

/-- The distance between two points in `Icc tmin tmax` is at most `|tmax - tmin|`. -/
-- TODO: move somewhere
lemma _root_.Set.Icc.abs_sub_le {tmin tmax : ℝ} (t t₀ : Icc tmin tmax) :
    |(t : ℝ) - t₀| ≤ |tmax - tmin| := by
  apply abs_le_abs <;> linarith [t.2.1, t.2.2, t₀.2.1, t₀.2.2]

namespace SmoothFlow

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E]

/-- Precomposition with a projection from `ℝ` to `Icc tmin tmax`, provided with `t₀` in the
non-empty interval.

This helps us work with the space of continuous curves `C(Icc tmin tmax, E)`. We have to use
`C(Icc tmin tmax, E)` instead of the junk value pattern on `ℝ → E` because we need the space of
curves to be a complete normed space. -/
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

/-- The integral
$$\int_{t₀}^t g(\alpha(\tau))(d\alpha_1(\tau),\cdots,d\alpha_n(\tau)) \,d\tau,$$
where `g : x → E [×n]→L[ℝ] E` has the same type as the `n`-th iterated derivative of `f : E → E`.
This is defined so that its derivative with respect to `α` will yield the same integral expression,
but with `n` replaced by `n + 1` and `g` replaced by its derivative. -/
def integralFun {n : ℕ} (g : E → E [×n]→L[ℝ] E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) (dα : Fin n → C(Icc tmin tmax, E)) (t : Icc tmin tmax) : E :=
  ∫ τ in t₀..t, g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ)

/-- The integrand is continuous in the integration variable. -/
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

/-- The integral as a function from continuous curves to continuous curves, enabling us to take
derivatives with respect to the curve -/
def integralCMAux {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) (dα : Fin n → C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) where
  toFun := integralFun g t₀ α dα
  continuous_toFun := continuous_integralFun hg t₀ hα dα

open Classical in
/-- The integral as a global function from continuous curves to continuous curves, using the junk
value pattern, which will allow us to take its iterated derivative with respect to the curve -/
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
  rw [integralCM_def]
  split_ifs with hα
  · simp only [ContinuousMap.ext_iff, ContinuousMap.add_apply]
    intro t
    simp only [integralCMAux, ContinuousMap.coe_mk, integralFun]
    rw [← integral_add (intervalIntegrable_integrand hg t₀ hα _ t₀ t)
        (intervalIntegrable_integrand hg t₀ hα _ t₀ t),
      integral_congr fun τ _ ↦ ?_]
    simpa only [compProj_update] using (g (compProj t₀ α τ)).toMultilinearMap.map_update_add ..
  · simp

lemma integralCM_update_smul {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E))
    (dα : Fin n → C(Icc tmin tmax, E)) (i : Fin n) (c : ℝ) (x : C(Icc tmin tmax, E)) :
    integralCM hg t₀ α (update dα i (c • x)) = c • integralCM hg t₀ α (update dα i x) := by
  rw [integralCM_def]
  split_ifs with hα
  · simp only [ContinuousMap.ext_iff, ContinuousMap.smul_apply]
    intro t
    simp only [integralCMAux, ContinuousMap.coe_mk, integralFun]
    rw [← intervalIntegral.integral_smul, integral_congr fun τ _ ↦ ?_]
    simpa only [compProj_update] using (g (compProj t₀ α τ)).toMultilinearMap.map_update_smul ..
  · simp

lemma continuous_integralCM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)) :
    Continuous (integralCM hg t₀ α) := by
  rw [integralCM_def]
  split_ifs with hα
  · let X := Fin n → C(Icc tmin tmax, E)
    let fparam : (X × Icc tmin tmax) → ℝ → E :=
      fun p τ ↦ g (compProj t₀ α τ) (fun i ↦ compProj t₀ (p.1 i) τ)
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_parametric_intervalIntegral_of_continuous _
      (continuous_induced_dom.comp continuous_snd)
    exact (continuous_integrand_pi₂ hg t₀ hα).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  · exact continuous_const

/-- The integral as a continuous multilinear map on the space of continuous curves, which will allow
us to relate it to `iteratedFDeriv` -/
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
/-- The integral as a continuous multilinear map on the space of continuous curves, as a global
function of `g` (later taken to be the `n`-th derivative of the vector field `E → E`), using the
junk value pattern -/
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

/-- Composition of a function `g : E → F` continuous on `u` with a continuous curve `α : C(I, E)`
whose range is contained in `u`, yielding a continuous curve `C(I, F)`. -/
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

/-- The integral as a continuous multilinear map is continuous in the space of continuous curves. -/
lemma continuousOn_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContinuousOn g u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) :
    ContinuousOn (integralCMLM g u t₀) {α : C(Icc tmin tmax, E) | range α ⊆ u} := by
  -- Embed `ContinuousMultilinearMap` into `UniformOnFun` and use notion of continuity there
  rw [continuousOn_iff_continuous_restrict, isEmbedding_toUniformOnFun.continuous_iff,
    UniformOnFun.continuous_rng_iff]
  intro B hB
  rw [mem_setOf, NormedSpace.isVonNBounded_iff] at hB
  rw [← equicontinuous_iff_continuous]
  simp_rw [comp_apply, restrict_apply, toUniformOnFun_toFun]
  intro α₀
  simp_rw [EquicontinuousAt, Subtype.forall] -- redundant?
  intro U hU
  -- Express in terms of ε-δ
  obtain ⟨ε, hε, hεU⟩ := mem_uniformity_dist.mp hU
  obtain ⟨C, hC⟩ := hB.exists_norm_le
  -- `C` is only guaranteed to be non-negative if `B` is non-empty, so we use `max C 0`
  -- Add 1 to avoid division by zero
  let δ := ε / ((1 + |tmax - tmin|) * (1 + (max C 0) ^ n))
  have hδ : 0 < δ := div_pos hε (mul_pos (by positivity) (by positivity))
  let V := ball (gComp (Icc tmin tmax) hg α₀) δ
  have hV : (gComp (Icc tmin tmax) hg) ⁻¹' V ∈ 𝓝 α₀ :=
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
      exact Icc.abs_sub_le t t₀
    _ = ε * ((|tmax - tmin| * (max C 0 ^ n)) / ((1 + |tmax - tmin|) * (1 + max C 0 ^ n))) := by
      simp_rw [δ]
      field_simp
    _ < ε := by
      apply mul_lt_of_lt_one_right hε
      rw [div_lt_one (by positivity)]
      exact mul_lt_mul' (lt_one_add _).le (lt_one_add _) (by positivity) (by positivity)

omit [CompleteSpace E] in
lemma _root_.ContDiffOn.continuousOn_fderiv_uncurryLeft
    {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContDiffOn ℝ 1 g u) (hu : IsOpen u) :
    ContinuousOn (fun x ↦ (fderiv ℝ g x).uncurryLeft (Ei := fun _ ↦ E)) u :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ E) E).symm.continuous.comp_continuousOn
    (hg.continuousOn_fderiv_of_isOpen hu le_rfl)

/-- If `f` is continuous on an open set `u` containing a compact set `s`, then for any `ε > 0`,
there exists `δ > 0` such that for any `x ∈ s` and any `y` with `dist x y < δ`, we have `y ∈ u`
and `dist (f x) (f y) < ε`.

This combines uniform continuity on compact sets with the fact that
a compact set has positive distance from the complement of an open set containing it. -/
lemma _root_.IsCompact.exists_mem_open_dist_lt_of_continuousOn
    {X : Type*} [PseudoMetricSpace X] {Y : Type*} [PseudoMetricSpace Y]
    {u : Set X} {s : Set X} {f : X → Y} (hs : IsCompact s) (hf : ContinuousOn f u) (hu : IsOpen u)
    (hsu : s ⊆ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y, dist x y < δ → y ∈ u ∧ dist (f x) (f y) < ε := by
  obtain ⟨δ₁, hδ₁, hthick⟩ := hs.exists_thickening_subset_open hu hsu
  -- Each `x ∈ s` is associated with a ball in which the value of `f` is close to `f x`
  have h := fun x (hx : x ∈ s) ↦ Metric.continuousOn_iff.mp hf x (hsu hx) (ε / 2) (half_pos hε)
  choose δₓ hδₓ h using h
  let c : s → Set X := fun ⟨x, hx⟩ ↦ ball x (δₓ x hx)
  have hcover : s ⊆ ⋃ i, c i := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hδₓ x hx)⟩
  -- Lebesgue number lemma extracts a uniform radius for all `x ∈ s`
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
  calc
    _ ≤ dist (f x) (f z) + dist (f z) (f y) := dist_triangle _ _ _
    _ = dist (f x) (f z) + dist (f y) (f z) := by rw [dist_comm (f z) (f y)]
    _ < ε / 2 + ε / 2 := add_lt_add
        (h z hz x (hsu hx) (Metric.mem_ball.mp hx'))
        (h z hz y hy (Metric.mem_ball.mp hy'))
    _ = ε := by ring

omit [CompleteSpace E] in
/-- If `g` is `C^1` on an open set `u` and `h` provides uniform control on the derivative's
variation near a point `x ∈ u`, then `g` is well-approximated by its derivative with error
proportional to the displacement. -/
-- TODO: look at this and maybe add to Mathlib
lemma norm_image_sub_fderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {u : Set E} (hg : ContDiffOn ℝ 1 g u) (hu : IsOpen u)
    {x y : E} {C δ : ℝ} (hxy : ‖y - x‖ < δ)
    (h : ∀ z, dist x z < δ → z ∈ u ∧ dist (fderiv ℝ g x) (fderiv ℝ g z) < C) :
    ‖g y - g x - (fderiv ℝ g x) (y - x)‖ ≤ C * ‖y - x‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le' _ _ (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  · intro z hz
    apply (hg.differentiableOn one_ne_zero).differentiableAt (hu.mem_nhds _)
    apply (h z _).1
    apply (mem_closedBall'.mp (segment_subset_closedBall x y hz)).trans_lt
    rwa [dist_comm, dist_eq_norm]
  · intro z hz
    rw [← dist_eq_norm, dist_comm]
    apply (h z _).2.le
    apply (mem_closedBall'.mp (segment_subset_closedBall x y hz)).trans_lt
    rwa [dist_comm, dist_eq_norm]

/-- Helper lemma which reduces a bound on `integralCMLM`s as `ContinuousLinearMap`s to a bound on
integrands as elements of `E` -/
lemma norm_integralCMLM_sub_fderiv_le {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hg : ContDiffOn ℝ 1 g u) (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    {α α' : C(Icc tmin tmax, E)} (hα : range α ⊆ u) (hα' : range α' ⊆ u) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t, ‖g (compProj t₀ α' t) - g (compProj t₀ α t) -
        (fderiv ℝ g (compProj t₀ α t)) (compProj t₀ (α' - α) t)‖ ≤
      ε / (1 + |tmax - tmin|) * ‖α' - α‖) :
    ‖integralCMLM g u t₀ α' - integralCMLM g u t₀ α -
      (integralCMLM (fun x ↦ (fderiv ℝ g x).uncurryLeft) u t₀ α).curryLeft (α' - α)‖ ≤
      ε * ‖α' - α‖ := by
  refine opNorm_le_bound (by positivity) fun dα ↦ ?_
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have hg' := hg.continuousOn_fderiv_uncurryLeft hu
  have hinteg₁ := intervalIntegrable_integrand hg.continuousOn t₀ hα' dα t₀ t
  have hinteg₂ := intervalIntegrable_integrand hg.continuousOn t₀ hα dα t₀ t
  have hinteg₃ := intervalIntegrable_integrand hg' t₀ hα (Fin.cons (α' - α) dα) t₀ t
  simp only [sub_apply, curryLeft_apply, integralCMLM_apply_if_pos hg.continuousOn,
    integralCMLM_apply_if_pos hg', ContinuousMap.sub_apply, integralCM_apply_if_pos hα',
    integralCM_apply_if_pos hα, integralFun, ← intervalIntegral.integral_sub hinteg₁ hinteg₂,
    ← intervalIntegral.integral_sub (hinteg₁.sub hinteg₂) hinteg₃]
  set C := ε / (1 + |tmax - tmin|) * ‖α' - α‖ * ∏ i, ‖dα i‖ with hC
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_).trans ?_
  · intro τ _
    simp only [ContinuousLinearMap.uncurryLeft_apply, Fin.cons_zero, Fin.tail_def, Fin.cons_succ,
      ← ContinuousMultilinearMap.sub_apply, hC]
    refine (le_opNorm _ _).trans ?_
    apply mul_le_mul (h τ)
      (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ (dα _).norm_coe_le_norm _)
      (by positivity) (by positivity)
  · rw [hC, mul_comm, ← mul_assoc, ← mul_assoc, mul_div_left_comm]
    gcongr
    apply mul_le_of_le_one_right hε.le
    rw [div_le_one (by positivity)]
    linarith [abs_nonneg (tmax - tmin), Icc.abs_sub_le t t₀]

/-- The derivative of `integralCMLM g u t₀` in `C(Icc tmin tmax, E)` is given by
`integralCMLM g' u t₀`, where `g'` is the derivative of `g` in `E`. -/
lemma hasFDerivAt_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContDiffOn ℝ 1 g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) :
    HasFDerivAt (integralCMLM g u t₀)
      ((integralCMLM (fun x ↦ (fderiv ℝ g x).uncurryLeft) u t₀ α).curryLeft) α := by
  rw [HasFDerivAt, hasFDerivAtFilter_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := (isCompact_range α.continuous).exists_mem_open_dist_lt_of_continuousOn
    (hg.continuousOn_fderiv_of_isOpen hu le_rfl) hu hα (by positivity : 0 < ε / (1 + |tmax - tmin|))
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun α' hdist ↦ ?_⟩
  have hα' : range α' ⊆ u := fun _ ⟨t, ht⟩ ↦ ht ▸ (h (α t) (mem_range_self t) _ (by
    rw [dist_comm, dist_eq_norm]
    exact (ContinuousMap.norm_coe_le_norm (α' - α) t).trans_lt (dist_eq_norm α' α ▸ hdist))).1
  -- Reduce bound on `ContinuousLinearMap`s to a bound on elements of `E`
  refine norm_integralCMLM_sub_fderiv_le hg hu t₀ hα hα' hε fun t ↦ ?_
  calc
    _ = ‖g (compProj t₀ α' t) - g (compProj t₀ α t) -
        (fderiv ℝ g (compProj t₀ α t)) (compProj t₀ α' t - compProj t₀ α t)‖ := by
      simp only [compProj, ContinuousMap.sub_apply]
    _ ≤ ε / (1 + |tmax - tmin|) * ‖compProj t₀ α' t - compProj t₀ α t‖ := by
      refine norm_image_sub_fderiv_le hg hu ?_ fun z hz ↦ h _ (mem_range_self _) z hz
      exact (ContinuousMap.norm_coe_le_norm (α' - α) _).trans_lt (dist_eq_norm α' α ▸ hdist)
    _ ≤ ε / (1 + |tmax - tmin|) * ‖α' - α‖ := by
      gcongr; exact ContinuousMap.norm_coe_le_norm (α' - α) _

/-- The derivative of `integralCMLM g u t₀` in `C(Icc tmin tmax, E)` is given by
`integralCMLM g' u t₀`, where `g'` is the derivative of `g` in `E`. Uncurrying of multilinear maps
is needed to ensure the types on both sides of the equation match. -/
lemma fderiv_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContDiffOn ℝ 1 g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) :
    (fderiv ℝ (integralCMLM g u t₀) α).uncurryLeft =
      integralCMLM (fun x ↦ (fderiv ℝ g x).uncurryLeft) u t₀ α := by
  rw [← uncurry_curryLeft (integralCMLM (fun x ↦ (fderiv ℝ g x).uncurryLeft) u t₀ α)]
  congr 1
  exact (hasFDerivAt_integralCMLM hg hu t₀ hα).fderiv

/-- The `k`-th iterated derivative of `g : E → E [×n]→L[ℝ] E`, with uncurrying applied at each step
to preserve the continuous multilinear map structure.
- `iteratedFDerivUncurry g 0 = g`
- `iteratedFDerivUncurry g (k + 1) x = (fderiv ℝ (iteratedFDerivUncurry g k) x).uncurryLeft`

This yields `iteratedFDerivUncurry g k : E → E [×(n + k)]→L[ℝ] E`. -/
noncomputable def iteratedFDerivUncurry {n : ℕ} (g : E → E [×n]→L[ℝ] E) (k : ℕ) :
    E → E [×(n + k)]→L[ℝ] E :=
  k.recOn g fun _ rec x ↦ (fderiv ℝ rec x).uncurryLeft

omit [CompleteSpace E] in
@[simp]
lemma iteratedFDerivUncurry_zero {n : ℕ} (g : E → E [×n]→L[ℝ] E) :
    iteratedFDerivUncurry g 0 = g := rfl

omit [CompleteSpace E] in
@[simp]
lemma iteratedFDerivUncurry_succ {n : ℕ} (g : E → E [×n]→L[ℝ] E) (k : ℕ) :
    iteratedFDerivUncurry g (k + 1) =
      fun x ↦ (fderiv ℝ (iteratedFDerivUncurry g k) x).uncurryLeft := rfl

omit [CompleteSpace E] in
/-- If `g` is `C^(m + k)` on `u`, then `iteratedFDerivUncurry g k` is `C^m` on `u`. -/
lemma contDiffOn_iteratedFDerivUncurry {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hu : IsOpen u) (k : ℕ) {m : ℕ∞} (hg : ContDiffOn ℝ (m + k) g u) :
    ContDiffOn ℝ m (iteratedFDerivUncurry g k) u := by
  induction k generalizing m with
  | zero => simp only [Nat.cast_zero, add_zero] at hg ⊢; exact hg
  | succ k ih =>
    simp only [iteratedFDerivUncurry_succ]
    have hg' : ContDiffOn ℝ (↑(m + 1) + ↑k) g u := by
      convert hg using 1
      simp only [Nat.cast_add, Nat.cast_one, WithTop.coe_add, WithTop.coe_one, add_comm,
        add_assoc]
    have h1 : ContDiffOn ℝ ↑(m + 1) (iteratedFDerivUncurry g k) u := ih hg'
    have h2 : ContDiffOn ℝ m (fderiv ℝ (iteratedFDerivUncurry g k)) u := by
      have : (↑(m + 1) : WithTop ℕ∞) = ↑m + 1 := by simp
      rw [this] at h1
      exact h1.fderiv_of_isOpen hu le_rfl
    exact (LinearIsometryEquiv.contDiff (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n + k).succ ↦ E) E).symm).comp_contDiffOn h2

/-- The `k`-th iterated derivative of `integralCMLM g u t₀` in `C(Icc tmin tmax, E)` is given by
`integralCMLM (iteratedFDerivUncurry g k) u t₀`. This generalizes `fderiv_integralCMLM`, which is
the `k = 1` case. -/
lemma iteratedFDerivUncurry_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) (k : ℕ) (hg : ContDiffOn ℝ k g u) :
    iteratedFDerivUncurry (integralCMLM g u t₀) k α =
      integralCMLM (iteratedFDerivUncurry g k) u t₀ α := by
  induction k generalizing α with
  | zero => simp
  | succ k ih =>
    simp only [iteratedFDerivUncurry_succ]
    -- The IH gives equality on {β | range β ⊆ u}, which is a neighborhood of α
    have heq : iteratedFDerivUncurry (integralCMLM g u t₀) k =ᶠ[𝓝 α]
        integralCMLM (iteratedFDerivUncurry g k) u t₀ := by
      have hopen : IsOpen {β : C(Icc tmin tmax, E) | range β ⊆ u} := by
        simp_rw [← Set.mapsTo_univ_iff_range_subset]
        exact ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu
      exact hopen.eventually_mem hα |>.mono fun β hβ ↦ ih hβ hg.of_succ
    have hsmooth : ContDiffOn ℝ 1 (iteratedFDerivUncurry g k) u := by
      have hg' : ContDiffOn ℝ (1 + k) g u := by simpa [add_comm] using hg
      exact contDiffOn_iteratedFDerivUncurry hu k hg'
    rw [heq.fderiv_eq, fderiv_integralCMLM hsmooth hu t₀ hα]

lemma contDiffOn_integralCMLM_nat {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (k : ℕ) (hg : ContDiffOn ℝ k g u) :
    ContDiffOn ℝ k (integralCMLM g u t₀) {α : C(Icc tmin tmax, E) | range α ⊆ u} := by
  induction k generalizing n g with
  | zero =>
    simp only [CharP.cast_eq_zero, contDiffOn_zero]
    exact continuousOn_integralCMLM hg.continuousOn t₀
  | succ k ih =>
    have hopen : IsOpen {α : C(Icc tmin tmax, E) | range α ⊆ u} := by
      simp_rw [← Set.mapsTo_univ_iff_range_subset]
      exact ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu
    have hcast : (↑(k + 1) : WithTop ℕ∞) = ↑k + 1 := by simp
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hopen]
    refine ⟨?_, ?_, ?_⟩
    · -- DifferentiableOn
      intro α hα
      have hg1 : ContDiffOn ℝ 1 g u := hg.of_le (by norm_cast; omega)
      exact (hasFDerivAt_integralCMLM hg1 hu t₀ hα).differentiableAt.differentiableWithinAt
    · -- k = ⊤ → AnalyticOn (vacuously true for finite k)
      intro h
      exact (WithTop.coe_ne_top h).elim
    · -- ContDiffOn ℝ k (fderiv ℝ (integralCMLM g u t₀))
      -- The derivative is curryLeft ∘ integralCMLM (iteratedFDerivUncurry g 1) u t₀
      have hg' : ContDiffOn ℝ k (iteratedFDerivUncurry g 1) u := by
        have h1 : ContDiffOn ℝ (↑k + 1) g u := by simpa using hg
        exact contDiffOn_iteratedFDerivUncurry hu 1 h1
      have hI := ih hg'
      -- fderiv equals curryLeft ∘ integralCMLM (iteratedFDerivUncurry g 1) u t₀
      have heq : ∀ α ∈ {α : C(Icc tmin tmax, E) | range α ⊆ u},
          fderiv ℝ (integralCMLM g u t₀) α =
            (integralCMLM (iteratedFDerivUncurry g 1) u t₀ α).curryLeft := fun α hα ↦ by
        have hg1 : ContDiffOn ℝ 1 g u := hg.of_le (by norm_cast; omega)
        exact (hasFDerivAt_integralCMLM hg1 hu t₀ hα).fderiv
      refine ContDiffOn.congr ?_ heq
      exact (LinearIsometryEquiv.contDiff (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) ↦ C(Icc tmin tmax, E)) C(Icc tmin tmax, E))).comp_contDiffOn hI

/-- If `g` is `C^k` on `u`, then `integralCMLM g u t₀` is `C^k` on the set of curves whose range is
contained in `u`. -/
lemma contDiffOn_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (k : ℕ∞) (hg : ContDiffOn ℝ k g u) :
    ContDiffOn ℝ k (integralCMLM g u t₀) {α : C(Icc tmin tmax, E) | range α ⊆ u} := by
  induction k using WithTop.recTopCoe with
  | top =>
    exact contDiffOn_infty.mpr fun m ↦ contDiffOn_integralCMLM_nat hu t₀ m
      (hg.of_le (WithTop.coe_le_coe.mpr le_top))
  | coe k => exact contDiffOn_integralCMLM_nat hu t₀ k hg

/-- Specialization of `contDiffOn_integralCMLM` to the case `n = 0`, where `g : E → E [×0]→L[ℝ] E`
corresponds to a function `f : E → E` via `uncurry0`/`curry0`. -/
lemma contDiffOn_integralCMLM_curry0 {f : E → E} {u : Set E}
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (k : ℕ∞) (hf : ContDiffOn ℝ k f u) :
    ContDiffOn ℝ k (fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0)
      {α : C(Icc tmin tmax, E) | range α ⊆ u} := by
  have hg : ContDiffOn ℝ k (fun x ↦ uncurry0 ℝ E (f x)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.contDiff.comp_contDiffOn hf
  exact (LinearIsometryEquiv.contDiff (continuousMultilinearCurryFin0 ℝ
    (C(Icc tmin tmax, E)) (C(Icc tmin tmax, E)))).comp_contDiffOn
    (contDiffOn_integralCMLM hu t₀ k hg)

/-- The implicit equation that defines the flow as its implicit function (when `T = 0`) -/
def T (f : E → E) (u : Set E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (p : E × C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) :=
  ContinuousMap.const _ p.1 - p.2 + (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ p.2).curry0

/-- `T` is `C^k` in `p` when the vector field `f` is `C^k`. -/
lemma contDiffOn_T {f : E → E} {u : Set E} (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (k : ℕ∞) (hf : ContDiffOn ℝ k f u) :
    ContDiffOn ℝ k (T f u t₀) (univ ×ˢ {α : C(Icc tmin tmax, E) | range α ⊆ u}) := by
  unfold T
  -- `ContinuousMap.const _ p.1` is smooth (linear in p.1)
  have h1 : ContDiff ℝ k (fun p : E × C(Icc tmin tmax, E) ↦ ContinuousMap.const _ p.1) :=
    (ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).contDiff.comp contDiff_fst
  -- `p.2` is smooth (projection)
  have h2 : ContDiff ℝ k (fun p : E × C(Icc tmin tmax, E) ↦ p.2) := contDiff_snd
  -- The integral term is C^k by contDiffOn_integralCMLM_curry0
  have h3 : ContDiffOn ℝ k (fun p : E × C(Icc tmin tmax, E) ↦
      (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ p.2).curry0)
      (univ ×ˢ {α : C(Icc tmin tmax, E) | range α ⊆ u}) :=
    (contDiffOn_integralCMLM_curry0 hu t₀ k hf).comp contDiff_snd.contDiffOn
      (fun p hp ↦ hp.2)
  exact (h1.contDiffOn.sub h2.contDiffOn).add h3

/-- `T` is `C^k` at the point `(x, α)` when the vector field `f` is `C^k` and `range α ⊆ u`. -/
lemma contDiffAt_T {f : E → E} {u : Set E} (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (k : ℕ∞) (hf : ContDiffOn ℝ k f u) {x : E} {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    ContDiffAt ℝ k (T f u t₀) (x, α) := by
  have hopen : IsOpen ((univ : Set E) ×ˢ {α : C(Icc tmin tmax, E) | range α ⊆ u}) := by
    apply isOpen_univ.prod
    simp_rw [← Set.mapsTo_univ_iff_range_subset]
    exact ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu
  have hmem : (x, α) ∈ (univ : Set E) ×ˢ {α : C(Icc tmin tmax, E) | range α ⊆ u} :=
    ⟨mem_univ x, hα⟩
  exact (contDiffOn_T hu t₀ k hf).contDiffAt (hopen.mem_nhds hmem)

/-- The derivative of `fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0` at `α`,
which appears as a component of the derivative of `T`. This is the composition of `curry0` with
the derivative of `integralCMLM`. -/
def fderivIntegralCurry0 (f : E → E) (u : Set E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) :=
  (continuousMultilinearCurryFin0 ℝ (C(Icc tmin tmax, E))
      (C(Icc tmin tmax, E))).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((integralCMLM (fun y ↦ (fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) y).uncurryLeft)
      u t₀ α).curryLeft)

/-- The derivative of `T f u t₀` at `(x, α)` is the continuous linear map
`(dx, dα) ↦ const dx - dα + D(integral term)(dα)`, where the derivative of the integral term
is given by `hasFDerivAt_integralCMLM`. -/
lemma hasFDerivAt_T {f : E → E} {u : Set E} (hf : ContDiffOn ℝ 1 f u) (hu : IsOpen u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {x : E} {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    HasFDerivAt (T f u t₀)
      ((ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).comp (ContinuousLinearMap.fst ℝ E _) -
        ContinuousLinearMap.snd ℝ E _ +
        (fderivIntegralCurry0 f u t₀ α).comp (ContinuousLinearMap.snd ℝ E _))
      (x, α) := by
  unfold T
  -- Derivative of `const x` with respect to `(x, α)` is `(dx, dα) ↦ const dx`
  have h1 : HasFDerivAt (fun p : E × C(Icc tmin tmax, E) ↦ ContinuousMap.const _ p.1)
      ((ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).comp (ContinuousLinearMap.fst ℝ E _))
      (x, α) :=
    (ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).hasFDerivAt.comp (x, α) hasFDerivAt_fst
  -- Derivative of `-α` with respect to `(x, α)` is `(dx, dα) ↦ -dα`
  have h2 : HasFDerivAt (fun p : E × C(Icc tmin tmax, E) ↦ -p.2)
      (-(ContinuousLinearMap.snd ℝ E _)) (x, α) :=
    hasFDerivAt_snd.neg
  -- Derivative of the integral term with respect to `(x, α)` is `(dx, dα) ↦ D(integral)(α)(dα)`
  have hg : ContDiffOn ℝ 1 (fun y ↦ uncurry0 ℝ E (f y)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.contDiff.comp_contDiffOn hf
  have h3 : HasFDerivAt (fun p : E × C(Icc tmin tmax, E) ↦
        (integralCMLM (fun y ↦ uncurry0 ℝ E (f y)) u t₀ p.2).curry0)
      ((fderivIntegralCurry0 f u t₀ α).comp (ContinuousLinearMap.snd ℝ E _))
      (x, α) := by
    have hI := hasFDerivAt_integralCMLM hg hu t₀ hα
    have hcurry : HasFDerivAt (fun m : C(Icc tmin tmax, E) [×0]→L[ℝ] C(Icc tmin tmax, E) ↦ m.curry0)
        (continuousMultilinearCurryFin0 ℝ (C(Icc tmin tmax, E))
          (C(Icc tmin tmax, E))).toContinuousLinearEquiv.toContinuousLinearMap
        (integralCMLM (fun y ↦ uncurry0 ℝ E (f y)) u t₀ α) := by
      have := ContinuousLinearMap.hasFDerivAt
        (continuousMultilinearCurryFin0 ℝ (C(Icc tmin tmax, E))
          (C(Icc tmin tmax, E))).toContinuousLinearEquiv.toContinuousLinearMap
        (x := integralCMLM (fun y ↦ uncurry0 ℝ E (f y)) u t₀ α)
      convert this using 2
    have hsnd : HasFDerivAt (fun p : E × C(Icc tmin tmax, E) ↦ p.2)
        (ContinuousLinearMap.snd ℝ E _) (x, α) := hasFDerivAt_snd
    exact (hcurry.comp α hI).comp (x, α) hsnd
  -- Combine: T = const x - α + integral = const x + (-α) + integral
  -- h1 + h2 + h3 gives HasFDerivAt for (const x + (-α) + integral)
  -- We need to show this equals (const x - α + integral) and the derivatives match
  have hfun : (fun p : E × C(Icc tmin tmax, E) ↦ ContinuousMap.const _ p.1 - p.2 +
        (integralCMLM (fun y ↦ uncurry0 ℝ E (f y)) u t₀ p.2).curry0) =
      (fun p ↦ ContinuousMap.const _ p.1) + (fun p ↦ -p.2) +
        (fun p ↦ (integralCMLM (fun y ↦ uncurry0 ℝ E (f y)) u t₀ p.2).curry0) := by
    ext p; simp [sub_eq_add_neg]
  have hderiv : (ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).comp
      (ContinuousLinearMap.fst ℝ E _) - ContinuousLinearMap.snd ℝ E _ +
      (fderivIntegralCurry0 f u t₀ α).comp (ContinuousLinearMap.snd ℝ E _) =
      (ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).comp (ContinuousLinearMap.fst ℝ E _) +
      (-ContinuousLinearMap.snd ℝ E _) +
      (fderivIntegralCurry0 f u t₀ α).comp (ContinuousLinearMap.snd ℝ E _) := by
    simp [sub_eq_add_neg]
  rw [hfun, hderiv]
  exact (h1.add h2).add h3

/-- The derivative of `T` restricted to the second component is
`-id + fderivIntegralCurry0 f u t₀ α`. -/
lemma fderiv_T_comp_inr {f : E → E} {u : Set E}
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)} :
    ((ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).comp (ContinuousLinearMap.fst ℝ E _) -
      ContinuousLinearMap.snd ℝ E _ +
      (fderivIntegralCurry0 f u t₀ α).comp (ContinuousLinearMap.snd ℝ E _)).comp
        (ContinuousLinearMap.inr ℝ E _) =
      -ContinuousLinearMap.id ℝ _ + fderivIntegralCurry0 f u t₀ α := by
  ext y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    _root_.map_zero, zero_sub]

/-- The operator norm of `fderivIntegralCurry0 f u t₀ α` is bounded by
`|tmax - tmin| * C` where `C` bounds `‖fderiv ℝ f x‖` on `range α`. -/
lemma opNorm_fderivIntegralCurry0_le {f : E → E} {u : Set E} (hf : ContDiffOn ℝ 1 f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ range α, ‖fderiv ℝ f x‖ ≤ C) :
    ‖fderivIntegralCurry0 f u t₀ α‖ ≤ |tmax - tmin| * C := by
  -- Define the inner function with explicit type to help inference
  set fderivUncurry : E → E [×1]→L[ℝ] E :=
    fun y ↦ (fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) y).uncurryLeft with hfderivUncurry
  have hg' : ContDiffOn ℝ 1 (fun y ↦ uncurry0 ℝ E (f y)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.contDiff.comp_contDiffOn hf
  have hg : ContinuousOn fderivUncurry u := hg'.continuousOn_fderiv_uncurryLeft hu
  -- Show the goal equals what we want to prove
  have hgoal : fderivIntegralCurry0 f u t₀ α =
      (continuousMultilinearCurryFin0 ℝ (C(Icc tmin tmax, E))
        (C(Icc tmin tmax, E))).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((integralCMLM fderivUncurry u t₀ α).curryLeft) := rfl
  rw [hgoal]
  -- The composition with an isometry preserves the norm
  calc ‖(continuousMultilinearCurryFin0 ℝ (C(Icc tmin tmax, E))
        (C(Icc tmin tmax, E))).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((integralCMLM fderivUncurry u t₀ α).curryLeft)‖
    _ = ‖(integralCMLM fderivUncurry u t₀ α).curryLeft‖ :=
        (continuousMultilinearCurryFin0 ℝ (C(Icc tmin tmax, E))
          (C(Icc tmin tmax, E))).toLinearIsometry.norm_toContinuousLinearMap_comp
    _ ≤ |tmax - tmin| * C := ?_
  -- Bound the norm of curryLeft of integralCMLM
  refine ContinuousLinearMap.opNorm_le_bound (M := |tmax - tmin| * C) (hMp := by positivity)
    (hM := fun dα ↦ ?_)
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  rw [ContinuousMultilinearMap.curryLeft_apply, integralCMLM_apply_if_pos hg,
    integralCM_apply_if_pos hα, integralFun]
  -- Bound the integrand pointwise
  have hboundUncurry : ∀ τ ∈ uIoc (t₀ : ℝ) t,
      ‖fderivUncurry (compProj t₀ α τ)
        (fun (i : Fin 1) ↦ compProj t₀ ((Fin.cons dα v : Fin 1 → _) i) τ)‖ ≤ C * ‖dα‖ := by
    intro τ hτ
    have hτ' : τ ∈ Icc tmin tmax := uIcc_subset_Icc t₀.2 t.2 (uIoc_subset_uIcc hτ)
    have hmem : compProj t₀ α τ ∈ range α := ⟨⟨τ, hτ'⟩, (compProj_of_mem hτ').symm⟩
    have hdiff : DifferentiableAt ℝ f (compProj t₀ α τ) :=
      (hf.differentiableOn one_ne_zero).differentiableAt (hu.mem_nhds (hα hmem))
    -- The derivative of uncurry0 ∘ f equals uncurry0 ∘ fderiv f
    let curry0Inv := (continuousMultilinearCurryFin0 ℝ E E).symm
    have hcomp : fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) (compProj t₀ α τ) =
        curry0Inv.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (fderiv ℝ f (compProj t₀ α τ)) := by
      convert fderiv_comp (compProj t₀ α τ)
        ((continuousMultilinearCurryFin0 ℝ E E).symm.differentiableAt) hdiff using 1
      rw [curry0Inv.fderiv]
    have hfderiv : ‖fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) (compProj t₀ α τ)‖ ≤ C := by
      rw [hcomp]
      have h : ‖curry0Inv.toContinuousLinearEquiv.toContinuousLinearMap.comp
              (fderiv ℝ f (compProj t₀ α τ))‖ = ‖fderiv ℝ f (compProj t₀ α τ)‖ :=
        curry0Inv.toLinearIsometry.norm_toContinuousLinearMap_comp
      rw [h]
      exact hbound _ hmem
    -- Bound ‖fderivUncurry x m‖ ≤ ‖fderivUncurry x‖ * ∏‖m i‖ ≤ C * ‖dα‖
    let m : Fin 1 → E := fun i ↦ compProj t₀ ((Fin.cons dα v : Fin 1 → _) i) τ
    have step1 : ‖fderivUncurry (compProj t₀ α τ) m‖ ≤
        ‖fderivUncurry (compProj t₀ α τ)‖ * ∏ i : Fin 1, ‖m i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    have step2 : ‖fderivUncurry (compProj t₀ α τ)‖ =
        ‖fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) (compProj t₀ α τ)‖ := by
      simp only [hfderivUncurry, ContinuousLinearMap.uncurryLeft_norm]
    have step3 : ∏ i : Fin 1, ‖m i‖ = ‖compProj t₀ dα τ‖ := by
      simp only [Fin.prod_univ_one, m, Fin.cons_zero]
    have step4 : ‖compProj t₀ dα τ‖ ≤ ‖dα‖ := dα.norm_coe_le_norm _
    calc _ ≤ ‖fderivUncurry (compProj t₀ α τ)‖ * ∏ i : Fin 1, ‖m i‖ := step1
      _ = ‖fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) (compProj t₀ α τ)‖ * ‖compProj t₀ dα τ‖ := by
          rw [step2, step3]
      _ ≤ C * ‖compProj t₀ dα τ‖ := mul_le_mul_of_nonneg_right hfderiv (norm_nonneg _)
      _ ≤ C * ‖dα‖ := mul_le_mul_of_nonneg_left step4 hC
  -- Since v : Fin 0 → _, the product ∏ i, ‖v i‖ = 1
  simp only [Fin.prod_univ_zero, mul_one]
  calc ‖∫ τ in (t₀ : ℝ)..t, fderivUncurry (compProj t₀ α τ)
        (fun (i : Fin 1) ↦ compProj t₀ ((Fin.cons dα v : Fin 1 → _) i) τ)‖
    _ ≤ C * ‖dα‖ * |↑t - ↑t₀| := intervalIntegral.norm_integral_le_of_norm_le_const hboundUncurry
    _ ≤ C * ‖dα‖ * |tmax - tmin| := mul_le_mul_of_nonneg_left (Icc.abs_sub_le t t₀)
        (mul_nonneg hC (norm_nonneg _))
    _ = |tmax - tmin| * C * ‖dα‖ := by ring

/-- The operator norm of `fderivIntegralCurry0 f u t₀ α` is less than 1 when the time interval is
sufficiently small relative to the derivative bound on `range α`. -/
lemma opNorm_fderivIntegralCurry0_lt_one {f : E → E} {u : Set E} (hf : ContDiffOn ℝ 1 f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ range α, ‖fderiv ℝ f x‖ ≤ C)
    (hsmall : |tmax - tmin| * C < 1) :
    ‖fderivIntegralCurry0 f u t₀ α‖ < 1 :=
  (opNorm_fderivIntegralCurry0_le hf hu t₀ hα hC hbound).trans_lt hsmall

/-- For `f` that is `C^1` at `x₀`, there exist `a > 0` and `ε > 0` such that for any
time interval `[tmin, tmax]` of size less than `ε` and any continuous curve `α` with
`range α ⊆ ball x₀ a`, the operator norm `‖fderivIntegralCurry0 f (ball x₀ a) t₀ α‖ < 1`. -/
lemma exists_ball_eps_opNorm_fderivIntegralCurry0_lt_one {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ a > 0, ∃ ε > 0,
      ∀ (tmin tmax : ℝ) (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)),
        range α ⊆ ball x₀ a → |tmax - tmin| < ε →
          ‖fderivIntegralCurry0 f (ball x₀ a) t₀ α‖ < 1 := by
  -- Extract an open neighborhood where f is C^1
  obtain ⟨u, hu_mem, hfu⟩ := hf.contDiffOn le_rfl nofun
  obtain ⟨a', ha'pos, ha'u⟩ := Metric.mem_nhds_iff.mp hu_mem
  -- Restrict to the open ball
  have hfball : ContDiffOn ℝ 1 f (ball x₀ a') := hfu.mono ha'u
  -- The derivative is continuous on ball x₀ a'
  have hfderiv_cont : ContinuousOn (fderiv ℝ f) (ball x₀ a') :=
    hfball.continuousOn_fderiv_of_isOpen isOpen_ball (le_refl 1)
  have hx₀ball : x₀ ∈ ball x₀ a' := mem_ball_self ha'pos
  -- Use continuity at x₀ to get a ball where the derivative is bounded
  set C := ‖fderiv ℝ f x₀‖ + 1 with hC_def
  have hCpos : 0 < C := by positivity
  obtain ⟨δ, hδpos, hδbound⟩ := Metric.continuousOn_iff.mp hfderiv_cont x₀ hx₀ball 1 one_pos
  -- Choose a to be small enough for both conditions
  set a := min (a' / 2) (δ / 2) with ha_def
  have hapos : 0 < a := lt_min (by linarith) (by linarith)
  have ha_lt_a' : a < a' := (min_le_left _ _).trans_lt (by linarith)
  have ha_lt_δ : a < δ := (min_le_right _ _).trans_lt (by linarith)
  have hball_sub : ball x₀ a ⊆ ball x₀ a' := ball_subset_ball (le_of_lt ha_lt_a')
  have hfu' : ContDiffOn ℝ 1 f (ball x₀ a) := hfball.mono hball_sub
  -- On ball x₀ a, the derivative is bounded by C
  have hbound : ∀ x ∈ ball x₀ a, ‖fderiv ℝ f x‖ ≤ C := fun x hx ↦ by
    have hxball : x ∈ ball x₀ a' := hball_sub hx
    have hdist : dist x x₀ < δ := (mem_ball.mp hx).trans ha_lt_δ
    have hnorm_diff : dist (fderiv ℝ f x) (fderiv ℝ f x₀) < 1 := hδbound x hxball hdist
    have h1 : ‖fderiv ℝ f x‖ ≤ ‖fderiv ℝ f x₀‖ + ‖fderiv ℝ f x - fderiv ℝ f x₀‖ :=
      norm_le_insert' _ _
    have h2 : ‖fderiv ℝ f x - fderiv ℝ f x₀‖ < 1 := by rwa [← dist_eq_norm]
    linarith
  -- Choose ε so that ε * C < 1
  set ε := 1 / (C + 1) with hε_def
  have hεpos : 0 < ε := by positivity
  refine ⟨a, hapos, ε, hεpos, ?_⟩
  intro tmin tmax t₀ α hαball hsmall
  have hbound' : ∀ x ∈ range α, ‖fderiv ℝ f x‖ ≤ C := fun x hx ↦ hbound x (hαball hx)
  apply opNorm_fderivIntegralCurry0_lt_one hfu' isOpen_ball t₀ hαball hCpos.le hbound'
  calc |tmax - tmin| * C
    _ < ε * C := mul_lt_mul_of_pos_right hsmall hCpos
    _ = C / (C + 1) := by rw [hε_def]; ring
    _ < 1 := (div_lt_one (by positivity : 0 < C + 1)).mpr (lt_add_one C)

/-
Lang Lemma 1.13 doesn't make any sense!

Clarify:
`of_contDiffAt_one` gives `ε > 0`, `a ≥ 0`, `r > 0`, `L ≥ 0`, `K ≥ 0`.
`ε` for nontrivial time interval `Icc (t₀ - ε) (t₀ + ε)` (can be shrunken arbitrarily)
`a` for how far away from `x₀` an integral curve `α` can travel
`r` for how far away from `x₀` an integral curve `α` can begin
`L` for bounding `‖f‖` within `closedBall x₀ a`
`K` for Lipschitz constant of `f` within `closedBall x₀ a` (can be enlarged arbitrarily)

Then any integral curve `α` of `f` starting in `closedBall x₀ r` and defined on
`Icc (t₀ - ε) (t₀ + ε)` is `L`-Lipschitz and stays within `closedBall x₀ a`. (missing lemmas?)

`‖f'‖ ≤ K < K + 1` at `x₀`.
Shrink `a` (shrink `r` proportionally and shrink `ε` appropriately) so that `f` is `C^1` and
`‖f'‖ < K + 1` within `closedBall x₀ a`. (missing lemmas?)
Shrink `ε` more so that `|tmax - tmin| * (K + 1) < 1`.
Shrink `ε` even more so that `L * max (tmax - t₀) (t₀ - tmin) < a - r`
(need a modified `mem_closedBall` for `ball`)

`IsPicardLindelof` still holds with new constants.
Let `α` be an integral curve beginning within `r` from `x₀`.
`range α ⊆ ball x₀ a`, so we can apply lemmas with `u := ball x₀ a`.

Conclude that `‖fderivIntegralCurry0 f u t₀ α‖ < 1` for all integral curves `α` of `f` beginning
within `r` from `x₀`.
-/





/-- The derivative of `T` restricted to the second component is bijective when the norm of
`fderivIntegralCurry0 f u t₀ α` is less than 1. This is the key condition for the implicit function
theorem to apply. -/
lemma bijective_fderiv_T_comp_inr {f : E → E} {u : Set E}
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hnorm : ‖fderivIntegralCurry0 f u t₀ α‖ < 1) :
    Function.Bijective
      (((ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).comp
          (ContinuousLinearMap.fst ℝ E _) - ContinuousLinearMap.snd ℝ E _ +
        (fderivIntegralCurry0 f u t₀ α).comp (ContinuousLinearMap.snd ℝ E _)).comp
          (ContinuousLinearMap.inr ℝ E _)) := by
  rw [fderiv_T_comp_inr t₀]
  -- Show -id + A = -(id - A), and bijectivity of negation preserves bijectivity
  have heq : -ContinuousLinearMap.id ℝ (C(Icc tmin tmax, E)) + fderivIntegralCurry0 f u t₀ α =
      -(ContinuousLinearMap.id ℝ _ - fderivIntegralCurry0 f u t₀ α) := by
    ext; simp [sub_eq_add_neg, add_comm]
  rw [heq]
  -- Use isUnit_one_sub_of_norm_lt_one to show id - A is invertible
  have hunit : IsUnit (ContinuousLinearMap.id ℝ _ - fderivIntegralCurry0 f u t₀ α) :=
    isUnit_one_sub_of_norm_lt_one hnorm
  -- IsUnit implies bijective
  have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  -- Negation is a bijection, so (-f) is bijective iff f is bijective
  -- ⇑(-g) = Neg.neg ∘ ⇑g
  change Function.Bijective
    (Neg.neg ∘ ⇑(ContinuousLinearMap.id ℝ (C(Icc tmin tmax, E)) - fderivIntegralCurry0 f u t₀ α))
  exact (ContinuousLinearEquiv.neg ℝ (M := C(Icc tmin tmax, E))).bijective.comp hbij

/-- The implicit function theorem applies to `T f u t₀` at a point `a = (x₀, α₀)` satisfying:
- `range α₀ ⊆ u` (the curve stays in the domain)
- `‖fderivIntegralCurry0 f u t₀ α₀‖ < 1` (the integral operator has small norm)
- `n ≥ 1` (we need at least `C^1` for the implicit function theorem) -/
lemma isContDiffImplicitAt_T {n : ℕ∞} {f : E → E} {u : Set E} (hf : ContDiffOn ℝ n f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) {α₀ : C(Icc tmin tmax, E)}
    (hα₀ : range α₀ ⊆ u) (hnorm : ‖fderivIntegralCurry0 f u t₀ α₀‖ < 1) (hn : 1 ≤ n) :
    IsContDiffImplicitAt n (T f u t₀)
      ((ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).comp (ContinuousLinearMap.fst ℝ E _) -
        ContinuousLinearMap.snd ℝ E _ +
        (fderivIntegralCurry0 f u t₀ α₀).comp (ContinuousLinearMap.snd ℝ E _))
      (x₀, α₀) where
  hasFDerivAt := hasFDerivAt_T (hf.of_le (mod_cast hn)) hu t₀ hα₀
  contDiffAt := contDiffAt_T hu t₀ n hf hα₀
  bijective := bijective_fderiv_T_comp_inr t₀ hnorm
  ne_zero := by
    simp only [ne_eq, WithTop.coe_eq_zero]
    exact (one_pos.trans_le hn).ne'

/-- The implicit function `E → C(Icc tmin tmax, E)` extracted from the implicit function theorem
applied to `T`. This is the local flow of the ODE near `x₀`. -/
noncomputable def localFlow {n : ℕ∞} {f : E → E} {u : Set E} (hf : ContDiffOn ℝ n f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) {α₀ : C(Icc tmin tmax, E)}
    (hα₀ : range α₀ ⊆ u) (hnorm : ‖fderivIntegralCurry0 f u t₀ α₀‖ < 1) (hn : 1 ≤ n) :
    E → C(Icc tmin tmax, E) :=
  (isContDiffImplicitAt_T hf hu t₀ x₀ hα₀ hnorm hn).implicitFunction

/-- The local flow satisfies `T f u t₀ (x, localFlow x) = T f u t₀ (x₀, α₀)` in a neighborhood of
`x₀`. -/
lemma T_localFlow {n : ℕ∞} {f : E → E} {u : Set E} (hf : ContDiffOn ℝ n f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) {α₀ : C(Icc tmin tmax, E)}
    (hα₀ : range α₀ ⊆ u) (hnorm : ‖fderivIntegralCurry0 f u t₀ α₀‖ < 1) (hn : 1 ≤ n) :
    ∀ᶠ x in 𝓝 x₀, T f u t₀ (x, localFlow hf hu t₀ x₀ hα₀ hnorm hn x) = T f u t₀ (x₀, α₀) :=
  (isContDiffImplicitAt_T hf hu t₀ x₀ hα₀ hnorm hn).apply_implicitFunction

/-- The local flow is `C^n` at `x₀`. -/
lemma contDiffAt_localFlow {n : ℕ∞} {f : E → E} {u : Set E} (hf : ContDiffOn ℝ n f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) {α₀ : C(Icc tmin tmax, E)}
    (hα₀ : range α₀ ⊆ u) (hnorm : ‖fderivIntegralCurry0 f u t₀ α₀‖ < 1) (hn : 1 ≤ n) :
    ContDiffAt ℝ n (localFlow hf hu t₀ x₀ hα₀ hnorm hn) x₀ :=
  (isContDiffImplicitAt_T hf hu t₀ x₀ hα₀ hnorm hn).contDiffAt_implicitFunction

end

end SmoothFlow
