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

/-- The set of continuous maps whose range is contained in an open set is open,
provided the domain is compact. -/
-- TODO: move to Mathlib/Topology/CompactOpen.lean
theorem ContinuousMap.isOpen_setOf_range_subset {X : Type*} {Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [TopologicalSpace Y] {U : Set Y} (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | range f ⊆ U} := by
  simp_rw [← mapsTo_univ_iff_range_subset]
  exact ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hU

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
-- TODO: this lemma's existence is due to missing lemmas about `= (_).curryLeft`
lemma fderiv_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} (hg : ContDiffOn ℝ 1 g u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) :
    (fderiv ℝ (integralCMLM g u t₀) α).uncurryLeft =
      (integralCMLM (fun x ↦ (fderiv ℝ g x).uncurryLeft) u t₀ α) := by
  rw [← uncurry_curryLeft (integralCMLM (fun x ↦ (fderiv ℝ g x).uncurryLeft) u t₀ α)]
  congr 1
  exact (hasFDerivAt_integralCMLM hg hu t₀ hα).fderiv

/-- The `k`-th iterated derivative of `g : E → E [×n]→L[ℝ] E`, with uncurrying applied at each step
to preserve the continuous multilinear map structure.
- `iteratedFDerivUncurry g 0 = g`
- `iteratedFDerivUncurry g (k + 1) x = (fderiv ℝ (iteratedFDerivUncurry g k) x).uncurryLeft`

This yields `iteratedFDerivUncurry g k : E → E [×(n + k)]→L[ℝ] E`. -/
-- TODO: add to mathlib?
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
lemma contDiffOn_iteratedFDerivUncurry {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {k : ℕ}
    {m m' : WithTop ℕ∞} (hg : ContDiffOn ℝ m' g u) (hu : IsOpen u) (hm' : m + k ≤ m') :
    ContDiffOn ℝ m (iteratedFDerivUncurry g k) u := by
  induction k generalizing m with
  | zero => exact hg.of_le (by simp_all)
  | succ k ih =>
    rw [iteratedFDerivUncurry_succ]
    apply (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + k + 1) ↦ E) E).symm
      |>.contDiff.comp_contDiffOn
    apply ContDiffOn.fderiv_of_isOpen _ hu le_rfl
    apply ih
    apply le_trans _ hm'
    simp [add_assoc, add_comm k]

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
    rw [← fderiv_integralCMLM
      (contDiffOn_iteratedFDerivUncurry hg hu (by simp [add_comm])) hu t₀ hα]
    congr 1
    apply Filter.EventuallyEq.fderiv_eq
    exact (ContinuousMap.isOpen_setOf_range_subset hu).eventually_mem hα |>.mono
      fun β hβ ↦ ih hβ hg.of_succ

lemma contDiffOn_integralCMLM_nat {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (k : ℕ) (hg : ContDiffOn ℝ k g u) :
    ContDiffOn ℝ k (integralCMLM g u t₀) {α : C(Icc tmin tmax, E) | range α ⊆ u} := by
  induction k generalizing n g with
  | zero =>
    rw [CharP.cast_eq_zero, contDiffOn_zero]
    exact continuousOn_integralCMLM hg.continuousOn t₀
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one,
      contDiffOn_succ_iff_fderiv_of_isOpen (ContinuousMap.isOpen_setOf_range_subset hu)]
    refine ⟨?_, fun h ↦ (WithTop.coe_ne_top h).elim, ?_⟩
    · intro α hα
      apply (hasFDerivAt_integralCMLM _ hu t₀ hα).differentiableAt.differentiableWithinAt
      exact hg.of_le (by simp)
    · rw [Nat.cast_add, Nat.cast_one] at hg
      have hg' : ContDiffOn ℝ k (iteratedFDerivUncurry g 1) u :=
        contDiffOn_iteratedFDerivUncurry hg hu (by simp)
      apply (continuousMultilinearCurryLeftEquiv ℝ _ _).contDiff.comp_contDiffOn (ih hg') |>.congr
      intro α hα
      rw [(hasFDerivAt_integralCMLM hg.one_of_succ hu t₀ hα).fderiv]
      simp
      rfl -- TODO: missing lemmas about `continuousMultilinearCurryLeftEquiv_apply`

/-- If `g` is `C^k` on `u`, then `integralCMLM g u t₀` is `C^k` on the set of curves whose range is
contained in `u`. -/
lemma contDiffOn_integralCMLM {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E}
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (k : ℕ∞) (hg : ContDiffOn ℝ k g u) :
    ContDiffOn ℝ k (integralCMLM g u t₀) {α : C(Icc tmin tmax, E) | range α ⊆ u} := by
  induction k with
  | top =>
    rw [contDiffOn_infty]
    intro m
    apply contDiffOn_integralCMLM_nat hu t₀ m (hg.of_le _)
    simp [← WithTop.coe_natCast]
  | coe k => exact contDiffOn_integralCMLM_nat hu t₀ k hg

/-- Specialization of `contDiffOn_integralCMLM` to the case `n = 0`, where `g : E → E [×0]→L[ℝ] E`
corresponds to a function `f : E → E` via `uncurry0`/`curry0`. -/
lemma contDiffOn_integralCMLM_curry0 {f : E → E} {u : Set E}
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (k : ℕ∞) (hf : ContDiffOn ℝ k f u) :
    ContDiffOn ℝ k (fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0)
      {α : C(Icc tmin tmax, E) | range α ⊆ u} :=
  continuousMultilinearCurryFin0 ℝ C(Icc tmin tmax, E) C(Icc tmin tmax, E)
    |>.contDiff.comp_contDiffOn <| contDiffOn_integralCMLM hu _ _
      <| (continuousMultilinearCurryFin0 ℝ E E).symm.contDiff.comp_contDiffOn hf

/-- The implicit equation that defines the flow as its implicit function (when `T = 0`) -/
def T (f : E → E) (u : Set E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (p : E × C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) :=
  ContinuousMap.const _ p.1 - p.2 + (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ p.2).curry0

/-- `T` is `C^k` in `p` when the vector field `f` is `C^k`. -/
lemma contDiffOn_T {f : E → E} {u : Set E} (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (k : ℕ∞) (hf : ContDiffOn ℝ k f u) :
    ContDiffOn ℝ k (T f u t₀) (univ ×ˢ {α : C(Icc tmin tmax, E) | range α ⊆ u}) :=
  ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E) |>.contDiff.comp contDiff_fst
    |>.contDiffOn.sub contDiffOn_snd |>.add
      <| (contDiffOn_integralCMLM_curry0 hu t₀ k hf).comp contDiff_snd.contDiffOn (fun _ h ↦ h.2)

/-- `T` is `C^k` at the point `(x, α)` when the vector field `f` is `C^k` and `range α ⊆ u`. -/
lemma contDiffAt_T {f : E → E} {u : Set E} (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (k : ℕ∞) (hf : ContDiffOn ℝ k f u) {x : E} {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    ContDiffAt ℝ k (T f u t₀) (x, α) :=
  (contDiffOn_T hu t₀ k hf).contDiffAt <| prod_mem_nhds Filter.univ_mem
    <| (ContinuousMap.isOpen_setOf_range_subset hu).mem_nhds hα

/-- If `α : FunSpace t₀ x₀ 0 L` is a fixed point of `next hPL hx₀`, then
`T f u t₀ (x₀, α.toContinuousMap) = 0`. This connects the Picard-Lindelöf fixed point to the
implicit function theorem formulation. -/
lemma T_eq_zero_of_isFixedPt_next {f : E → E} {u : Set E} (hfu : ContinuousOn f u)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a L K : ℝ≥0}
    (hPL : IsPicardLindelof (fun _ ↦ f) t₀ x₀ a 0 L K) {α : ODE.FunSpace t₀ x₀ 0 L}
    (hα : range α ⊆ u) (h : IsFixedPt (ODE.FunSpace.next hPL (mem_closedBall_self le_rfl)) α) :
    T f u t₀ (x₀, α.toContinuousMap) = 0 := by
  ext t
  -- TODO: repetitive
  have hg : ContinuousOn (fun x ↦ uncurry0 ℝ E (f x)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp_continuousOn hfu
  rw [T, curry0_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ODE.FunSpace.toContinuousMap_apply_eq_apply, ContinuousMap.zero_apply,
    α.eq_picard_of_isFixedPt hPL (mem_closedBall_self le_rfl) h, ODE.picard_apply,
    integralCMLM_apply_if_pos hg, integralCM_apply_if_pos hα, integralFun, sub_add_cancel_left,
    neg_add_eq_zero]
  congr

/-- If `T f u t₀ (x₀, α) = 0`, then `α` satisfies the integral equation for the ODE `α' = f ∘ α`
with initial condition `α t₀ = x₀`. This is equivalent to saying `α` is an integral curve of `f`. -/
lemma eq_picard_of_T_eq_zero {f : E → E} {u : Set E} (hf : ContinuousOn f u)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) (hT : T f u t₀ (x₀, α) = 0) (t : Icc tmin tmax) :
    α t = ODE.picard (fun _ ↦ f) t₀ x₀ (fun t ↦ compProj t₀ α t) t := by
  -- TODO: repetitive
  have hg : ContinuousOn (fun x ↦ uncurry0 ℝ E (f x)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp_continuousOn hf
  replace hT := ContinuousMap.ext_iff.mp hT t
  rw [T, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.zero_apply, ContinuousMultilinearMap.curry0_apply, integralCMLM_apply_if_pos hg,
    integralCM_apply_if_pos hα, integralFun, sub_add_eq_add_sub, sub_eq_zero] at hT
  simp [← hT]

/-- If `T f u t₀ (x₀, α) = 0`, then `α t₀ = x₀`. This follows from the fact that the integral
from `t₀` to `t₀` vanishes. -/
lemma eq_of_T_eq_zero {f : E → E} {u : Set E} (hf : ContinuousOn f u)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) (hT : T f u t₀ (x₀, α) = 0) :
    α t₀ = x₀ := by
  rw [eq_picard_of_T_eq_zero hf hα hT, ODE.picard_apply₀]

/-- If `T f u t₀ (x₀, α) = 0`, then `compProj t₀ α` (the extension of `α` to `ℝ`) has derivative
`f (α t)` within `Icc tmin tmax` at each point `t`. This shows that `α` is an integral curve of
the vector field `f`. -/
lemma hasDerivWithinAt_of_T_eq_zero {f : E → E} {u : Set E} (hf : ContinuousOn f u)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) (hT : T f u t₀ (x₀, α) = 0)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (compProj t₀ α) (f (α ⟨t, ht⟩)) (Icc tmin tmax) t := by
  have hf' : ContinuousOn (uncurry fun _ ↦ f) (Icc tmin tmax ×ˢ u) :=
    hf.comp continuousOn_snd fun _ h ↦ h.2
  have hmem : ∀ t' ∈ Icc tmin tmax, compProj t₀ α t' ∈ u := fun t' ht' ↦
    hα ⟨⟨t', ht'⟩, (compProj_of_mem ht').symm⟩
  have hderiv := ODE.hasDerivWithinAt_picard_Icc t₀.2 hf' (continuous_compProj t₀ α).continuousOn
    hmem x₀ ht
  rw [compProj_of_mem ht] at hderiv
  have heq := eq_picard_of_T_eq_zero hf hα hT
  exact hderiv.congr (fun s hs ↦ by rw [compProj_of_mem hs, heq, ODE.picard_apply])
    (by rw [compProj_of_mem ht, heq, ODE.picard_apply])

/-- The derivative of `fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0` at `α`,
which appears as a component of the derivative of `T`. This is the composition of `curry0` with
the derivative of `integralCMLM`. -/
def fderivIntegralCurry0 (f : E → E) (u : Set E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) :=
  (continuousMultilinearCurryFin0 ℝ C(Icc tmin tmax, E)
      C(Icc tmin tmax, E)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((integralCMLM (fun y ↦ (fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) y).uncurryLeft)
      u t₀ α).curryLeft)

/-- `fderivIntegralCurry0 f u t₀ α` is the Fréchet derivative of
`fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0` at `α`. -/
lemma hasFDerivAt_integralCMLM_curry0 {f : E → E} {u : Set E} (hf : ContDiffOn ℝ 1 f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) :
    HasFDerivAt (fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0)
      (fderivIntegralCurry0 f u t₀ α) α :=
  -- TODO: repetitive
  have hg : ContDiffOn ℝ 1 (fun y ↦ uncurry0 ℝ E (f y)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.contDiff.comp_contDiffOn hf
  continuousMultilinearCurryFin0 ℝ C(Icc tmin tmax, E) C(Icc tmin tmax, E)
    |>.toContinuousLinearEquiv.hasFDerivAt.comp α <| hasFDerivAt_integralCMLM hg hu t₀ hα

/-- The Fréchet derivative of `T f u t₀` at `(x, α)`. This is the continuous linear map
`(dx, dα) ↦ const dx - dα + D(integral term)(dα)`. -/
def fderivT (f : E → E) (u : Set E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) : E × C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) :=
  (ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)).comp (ContinuousLinearMap.fst ℝ E _) -
    ContinuousLinearMap.snd ℝ E _ +
    (fderivIntegralCurry0 f u t₀ α).comp (ContinuousLinearMap.snd ℝ E _)

/-- The derivative of `T f u t₀` at `(x, α)` is `fderivT f u t₀ α`, which is the continuous linear
map `(dx, dα) ↦ const dx - dα + D(integral term)(dα)`, where the derivative of the integral term
is given by `hasFDerivAt_integralCMLM`. -/
lemma hasFDerivAt_T {f : E → E} {u : Set E} (hf : ContDiffOn ℝ 1 f u) (hu : IsOpen u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {x : E} {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    HasFDerivAt (T f u t₀) (fderivT f u t₀ α) (x, α) := by
  apply (HasFDerivAt.sub _ hasFDerivAt_snd).add _
  · exact ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)
      |>.hasFDerivAt.comp (x, α) hasFDerivAt_fst
  · exact (hasFDerivAt_integralCMLM_curry0 hf hu t₀ hα).comp (𝕜 := ℝ) (x, α) hasFDerivAt_snd

/-- The derivative of `T` restricted to the second component is
`-id + fderivIntegralCurry0 f u t₀ α`. We will show that this is invertible under certain
conditions. -/
lemma fderivT_comp_inr {f : E → E} {u : Set E}
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)} :
    (fderivT f u t₀ α).comp (ContinuousLinearMap.inr ℝ E _) =
      -ContinuousLinearMap.id ℝ _ + fderivIntegralCurry0 f u t₀ α := by
  ext y
  simp [fderivT]

/-- The operator norm of `fderivIntegralCurry0 f u t₀ α` is less than 1 when the time interval is
sufficiently small relative to the derivative bound on `range α`. -/
lemma opNorm_fderivIntegralCurry0_lt_one {f : E → E} {u : Set E} (hf : ContDiffOn ℝ 1 f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ range α, ‖fderiv ℝ f x‖ ≤ C)
    (hsmall : |tmax - tmin| * C < 1) :
    ‖fderivIntegralCurry0 f u t₀ α‖ < 1 := by
  let fderivUncurry : E → E [×1]→L[ℝ] E :=
    fun y ↦ (fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) y).uncurryLeft
  have hg' : ContDiffOn ℝ 1 (fun y ↦ uncurry0 ℝ E (f y)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.contDiff.comp_contDiffOn hf
  have hg : ContinuousOn fderivUncurry u := hg'.continuousOn_fderiv_uncurryLeft hu
  -- Use isometry to reduce to bounding ‖(integralCMLM fderivUncurry u t₀ α).curryLeft‖
  calc ‖fderivIntegralCurry0 f u t₀ α‖
    _ = ‖(integralCMLM fderivUncurry u t₀ α).curryLeft‖ :=
        (continuousMultilinearCurryFin0 ℝ C(Icc tmin tmax, E)
          C(Icc tmin tmax, E)).toLinearIsometry.norm_toContinuousLinearMap_comp
    _ ≤ |tmax - tmin| * C := ?_
    _ < 1 := hsmall
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun dα ↦ ?_
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  rw [ContinuousMultilinearMap.curryLeft_apply, integralCMLM_apply_if_pos hg,
    integralCM_apply_if_pos hα, integralFun]
  simp only [Fin.prod_univ_zero, mul_one]
  -- Bound integrand: ‖fderivUncurry x (cons dα v)‖ ≤ C * ‖dα‖
  have : ∀ τ ∈ uIoc (t₀ : ℝ) t,
      ‖fderivUncurry (compProj t₀ α τ)
        (fun i ↦ compProj t₀ ((Fin.cons dα v : Fin 1 → _) i) τ)‖ ≤ C * ‖dα‖ := by
    intro τ hτ
    have hτ' : τ ∈ Icc tmin tmax := uIcc_subset_Icc t₀.2 t.2 (uIoc_subset_uIcc hτ)
    have hmem : compProj t₀ α τ ∈ range α := ⟨⟨τ, hτ'⟩, (compProj_of_mem hτ').symm⟩
    have hdiff : DifferentiableAt ℝ f (compProj t₀ α τ) :=
      (hf.differentiableOn one_ne_zero).differentiableAt (hu.mem_nhds (hα hmem))
    let curry0Inv := (continuousMultilinearCurryFin0 ℝ E E).symm
    have heq : fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) (compProj t₀ α τ) =
        curry0Inv.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (fderiv ℝ f (compProj t₀ α τ)) := by
      convert fderiv_comp (compProj t₀ α τ) curry0Inv.differentiableAt hdiff using 1
      rw [curry0Inv.fderiv]
    calc ‖fderivUncurry (compProj t₀ α τ)
            (fun i ↦ compProj t₀ ((Fin.cons dα v : Fin 1 → _) i) τ)‖
      _ ≤ ‖fderivUncurry (compProj t₀ α τ)‖ *
            ∏ i : Fin 1, ‖compProj t₀ ((Fin.cons dα v : Fin 1 → _) i) τ‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fun z ↦ uncurry0 ℝ E (f z)) (compProj t₀ α τ)‖ * ‖compProj t₀ dα τ‖ := by
          congr 1
          · exact ContinuousLinearMap.uncurryLeft_norm _
          · simp only [Fin.prod_univ_one, Fin.cons_zero]
      _ = ‖fderiv ℝ f (compProj t₀ α τ)‖ * ‖compProj t₀ dα τ‖ := by
          rw [heq]; congr 1
          exact curry0Inv.toLinearIsometry.norm_toContinuousLinearMap_comp
      _ ≤ C * ‖dα‖ := by gcongr; exacts [hbound _ hmem, dα.norm_coe_le_norm _]
  calc
    _ ≤ C * ‖dα‖ * |↑t - ↑t₀| := intervalIntegral.norm_integral_le_of_norm_le_const this
    _ ≤ C * ‖dα‖ * |tmax - tmin| :=
        mul_le_mul_of_nonneg_left (Icc.abs_sub_le t t₀) (mul_nonneg hC (norm_nonneg _))
    _ = |tmax - tmin| * C * ‖dα‖ := by ring

/-- For `f` that is `C^1` at `x₀`, there exist `a > 0` and `ε > 0` such that for any
time interval `[tmin, tmax]` of size less than `ε` and any continuous curve `α` with
`range α ⊆ ball x₀ a`, the operator norm `‖fderivIntegralCurry0 f (ball x₀ a) t₀ α‖ < 1`. -/
lemma exists_ball_eps_opNorm_fderivIntegralCurry0_lt_one {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ a > 0, ∃ ε > 0, ContDiffOn ℝ 1 f (ball x₀ a) ∧
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
  refine ⟨a, hapos, ε, hεpos, hfu', ?_⟩
  intro tmin tmax t₀ α hαball hsmall
  have hbound' : ∀ x ∈ range α, ‖fderiv ℝ f x‖ ≤ C := fun x hx ↦ hbound x (hαball hx)
  apply opNorm_fderivIntegralCurry0_lt_one hfu' isOpen_ball t₀ hαball hCpos.le hbound'
  calc |tmax - tmin| * C
    _ < ε * C := mul_lt_mul_of_pos_right hsmall hCpos
    _ = C / (C + 1) := by rw [hε_def]; ring
    _ < 1 := (div_lt_one (by positivity : 0 < C + 1)).mpr (lt_add_one C)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- `IsPicardLindelof` is preserved when shrinking the time interval for time-independent ODEs. -/
lemma IsPicardLindelof.shrink_time_indep {f : E → E} {t₀ : ℝ} {x₀ : E} {a r L K : ℝ≥0}
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    (hf : IsPicardLindelof (fun _ ↦ f) (tmin := t₀ - ε) (tmax := t₀ + ε)
      ⟨t₀, by simp [le_of_lt hε]⟩ x₀ a r L K) :
    IsPicardLindelof (fun _ ↦ f) (tmin := t₀ - ε') (tmax := t₀ + ε')
      ⟨t₀, by simp [le_of_lt hε']⟩ x₀ a r L K where
  lipschitzOnWith t _ := hf.lipschitzOnWith t (by simp at *; constructor <;> linarith)
  continuousOn x hx :=
    (hf.continuousOn x hx).mono fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  norm_le t ht x hx := hf.norm_le t (by simp at *; constructor <;> linarith) x hx
  mul_max_le := by
    calc (L : ℝ) * max ((t₀ + ε') - t₀) (t₀ - (t₀ - ε'))
      _ = L * ε' := by simp
      _ ≤ L * ε := by gcongr
      _ = L * max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) := by simp
      _ ≤ a - r := hf.mul_max_le

/-- When f is C^1 at x₀, there exist ε > 0, a > 0, a' ≥ a, and an integral curve α starting at x₀
defined on `Icc (t₀ - ε) (t₀ + ε)`, such that the range of α is in `ball x₀ a` and
`‖fderivIntegralCurry0 f (ball x₀ a') t₀' α‖ < 1`.

The integral curve is given as a `FunSpace` satisfying `IsFixedPt (next hPL hx₀) α`,
which can be converted to a continuous map via `toContinuousMap`. -/
lemma exists_integralCurve_opNorm_fderivIntegralCurry0_lt_one {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a a' : ℝ≥0) (L K : ℝ≥0) (_ : 0 < a) (_ : a ≤ a')
      (_ : ContDiffOn ℝ 1 f (ball x₀ a'))
      (hPL : IsPicardLindelof (fun _ ↦ f) (tmin := t₀ - ε) (tmax := t₀ + ε)
        ⟨t₀, by simp [le_of_lt hε]⟩ x₀ a 0 L K),
      ∃ α : ODE.FunSpace ⟨t₀, by simp [le_of_lt hε]⟩ x₀ 0 L,
        IsFixedPt (ODE.FunSpace.next hPL (mem_closedBall_self le_rfl)) α ∧
        (∀ t, α t ∈ ball x₀ a) ∧
        ‖fderivIntegralCurry0 f (ball x₀ a') ⟨t₀, by simp [le_of_lt hε]⟩ α.toContinuousMap‖
          < 1 := by
  -- Get parameters from the two key lemmas
  obtain ⟨a₁, ha₁pos, ε₁, hε₁pos, hf_diff, hfderiv_bound⟩ :=
    exists_ball_eps_opNorm_fderivIntegralCurry0_lt_one hf
  obtain ⟨ε₂, hε₂pos, a₂, r, L, K, hrpos, hPL⟩ := IsPicardLindelof.of_contDiffAt_one hf t₀
  -- We have a₂ > 0 since r > 0 and a₂ ≥ r (from the mul_max_le constraint)
  have ha₂pos : (0 : ℝ) < a₂ := by
    have h := hPL.mul_max_le; simp only at h
    have hL : (0 : ℝ) ≤ L := L.2
    have hmax : 0 < max (t₀ + ε₂ - t₀) (t₀ - (t₀ - ε₂)) := by simp; linarith
    have hrpos' : (0 : ℝ) < r := hrpos
    nlinarith
  -- Choose a = min a₁ (a₂ / 2) so that closedBall x₀ a ⊆ closedBall x₀ a₂ (for Lipschitz/bound)
  -- and ball x₀ a ⊆ ball x₀ a₁ (for the fderiv bound)
  have ha_pos_real : 0 < min a₁ ((a₂ : ℝ) / 2) := lt_min ha₁pos (by linarith)
  set a : ℝ≥0 := ⟨min a₁ (a₂ / 2), le_of_lt ha_pos_real⟩ with ha_def
  set a' : ℝ≥0 := ⟨a₁, le_of_lt ha₁pos⟩ with ha'_def
  have hapos : 0 < a := by simp only [a]; exact ha_pos_real
  have ha_le_a₁ : (a : ℝ) ≤ a₁ := min_le_left _ _
  have haa' : a ≤ a' := NNReal.coe_le_coe.mp ha_le_a₁
  have ha_lt_a₂ : (a : ℝ) < a₂ := (min_le_right _ _).trans_lt (by linarith)
  -- Choose ε small enough for both conditions
  -- Need: 2ε < ε₁ (for fderiv bound), ε ≤ ε₂ (for PicardLindelof),
  -- and L * ε < a (strict, for mem_ball)
  set ε := min (min (ε₁ / 4) (ε₂ / 2)) ((a : ℝ) / (L + 1)) with hε_def
  have hεpos : 0 < ε := by
    apply lt_min (lt_min (by positivity) (by positivity))
    exact div_pos (NNReal.coe_pos.mpr hapos) (by positivity)
  have hε_lt_ε₁ : 2 * ε < ε₁ := by
    calc 2 * ε ≤ 2 * (ε₁ / 4) := by gcongr; exact (min_le_left _ _).trans (min_le_left _ _)
      _ = ε₁ / 2 := by ring
      _ < ε₁ := by linarith
  have hε_le_ε₂ : ε ≤ ε₂ := by
    calc ε ≤ ε₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
      _ ≤ ε₂ := by linarith
  have hLε_lt_a : (L : ℝ) * ε < a := by
    have hapos' : (0 : ℝ) < a := NNReal.coe_pos.mpr hapos
    calc (L : ℝ) * ε
      _ ≤ L * ((a : ℝ) / (L + 1)) := by gcongr; exact min_le_right _ _
      _ = L * a / (L + 1) := by ring
      _ < a := by
        rcases eq_or_lt_of_le L.2 with hL | hL
        · have : (L : ℝ) = 0 := hL.symm; simp only [this, zero_mul, zero_div, hapos']
        · have hLnonneg : (0 : ℝ) ≤ L := L.2
          have hLpos1 : (0 : ℝ) < (L : ℝ) + 1 := by linarith
          have hLne : (L : ℝ) + 1 ≠ 0 := ne_of_gt hLpos1
          field_simp [hLne]
          nlinarith
  -- Shrink PicardLindelof to the smaller time interval with r = 0 and smaller a
  have hPL' : IsPicardLindelof (fun _ ↦ f) (tmin := t₀ - ε) (tmax := t₀ + ε)
      ⟨t₀, by simp [le_of_lt hεpos]⟩ x₀ a 0 L K := by
    have hPL_shrink := IsPicardLindelof.shrink_time_indep hε₂pos hεpos hε_le_ε₂ hPL
    refine IsPicardLindelof.of_time_independent ?_ ?_ ?_
    · intro x hx
      apply hPL_shrink.norm_le t₀ (by simp [le_of_lt hεpos]) x
      exact closedBall_subset_closedBall (le_of_lt ha_lt_a₂) hx
    · apply (hPL_shrink.lipschitzOnWith t₀ (by simp [le_of_lt hεpos])).mono
      exact closedBall_subset_closedBall (le_of_lt ha_lt_a₂)
    · simp only [NNReal.coe_zero, sub_zero, add_sub_cancel_left, sub_sub_cancel, max_self]
      exact le_of_lt hLε_lt_a
  -- Get the fixed point (integral curve) from Picard-Lindelöf
  have hx₀ : x₀ ∈ closedBall x₀ (0 : ℝ≥0) := mem_closedBall_self le_rfl
  obtain ⟨α_fun, hα_fixed⟩ := ODE.FunSpace.exists_isFixedPt_next hPL' hx₀
  -- Show α t ∈ ball x₀ a for all t
  have hα_ball : ∀ t, α_fun t ∈ ball x₀ a := fun t ↦ by
    rw [mem_ball, dist_eq_norm]
    calc ‖α_fun t - x₀‖
        ≤ ‖α_fun t - α_fun ⟨t₀, by simp [le_of_lt hεpos]⟩‖ +
            ‖α_fun ⟨t₀, by simp [le_of_lt hεpos]⟩ - x₀‖ :=
          norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ L * |t.1 - t₀| + 0 := by
          apply add_le_add
          · rw [← dist_eq_norm]; exact α_fun.lipschitzWith.dist_le_mul t _
          · have := α_fun.mem_closedBall₀
            simp only [NNReal.coe_zero, mem_closedBall] at this
            rw [dist_le_zero.mp this, sub_self, norm_zero]
      _ ≤ L * max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) := by
          simp only [add_zero]
          gcongr
          exact abs_sub_le_max_sub t.2.1 t.2.2 _
      _ < a := by simp only [add_sub_cancel_left, sub_sub_cancel, max_self]; exact hLε_lt_a
  -- Show the operator norm bound
  have hα_norm :
      ‖fderivIntegralCurry0 f (ball x₀ a') ⟨t₀, by simp [le_of_lt hεpos]⟩ α_fun.toContinuousMap‖
        < 1 := by
    have hα_range : range α_fun.toContinuousMap ⊆ ball x₀ a' := by
      intro y hy
      obtain ⟨t, ht⟩ := hy
      rw [← ht, ODE.FunSpace.toContinuousMap_apply_eq_apply]
      exact ball_subset_ball ha_le_a₁ (hα_ball t)
    have hinterval : |(t₀ + ε) - (t₀ - ε)| < ε₁ := by
      have h1 : (t₀ + ε) - (t₀ - ε) = 2 * ε := by ring
      rw [h1, abs_of_pos (by linarith)]
      linarith
    have ht₀mem : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := by simp [le_of_lt hεpos]
    exact hfderiv_bound (t₀ - ε) (t₀ + ε) ⟨t₀, ht₀mem⟩ α_fun.toContinuousMap hα_range hinterval
  exact ⟨ε, hεpos, a, a', L, K, hapos, haa', hf_diff, hPL', α_fun, hα_fixed, hα_ball, hα_norm⟩

/-- When f is C^1 at x₀, there exist ε > 0, a > 0, and a continuous map
`α : C(Icc (t₀ - ε) (t₀ + ε), E)` such that `f` is C^1 on `ball x₀ a`, the range of α is in
`ball x₀ a`, `T f (ball x₀ a) t₀ (x₀, α) = 0`, and `‖fderivIntegralCurry0 f (ball x₀ a) t₀ α‖ < 1`.

Note that `T = 0` implies `α(t₀) = x₀` since the integral from `t₀` to `t₀` vanishes.

This is a reformulation of `exists_integralCurve_opNorm_fderivIntegralCurry0_lt_one` that avoids
mentioning `ODE.FunSpace`, expressing everything in terms of continuous maps. -/
lemma exists_contMap_T_eq_zero_opNorm_lt_one {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a : ℝ) (_ : 0 < a)
      (α : C(Icc (t₀ - ε) (t₀ + ε), E)),
        ContDiffOn ℝ 1 f (ball x₀ a) ∧
        range α ⊆ ball x₀ a ∧
        T f (ball x₀ a) ⟨t₀, by simp [le_of_lt hε]⟩ (x₀, α) = 0 ∧
        ‖fderivIntegralCurry0 f (ball x₀ a) ⟨t₀, by simp [le_of_lt hε]⟩ α‖ < 1 := by
  obtain ⟨ε, hεpos, a, a', L, K, hapos, haa', hf_diff, hPL, α, hα_fixed, hα_ball, hα_norm⟩ :=
    exists_integralCurve_opNorm_fderivIntegralCurry0_lt_one hf t₀
  refine ⟨ε, hεpos, a', NNReal.coe_pos.mp (hapos.trans_le (NNReal.coe_le_coe.mpr haa')),
    α.toContinuousMap, hf_diff, ?_, ?_, ?_⟩
  · -- range α ⊆ ball x₀ a'
    intro y hy
    obtain ⟨t, ht⟩ := hy
    rw [← ht, ODE.FunSpace.toContinuousMap_apply_eq_apply]
    exact ball_subset_ball (NNReal.coe_le_coe.mpr haa') (hα_ball t)
  · -- T f (ball x₀ a') t₀ (x₀, α.toContinuousMap) = 0
    have hfu : ContinuousOn f (ball x₀ a') := hf_diff.continuousOn
    have hrange : range α.toContinuousMap ⊆ ball x₀ a' := by
      intro y hy
      obtain ⟨t, ht⟩ := hy
      rw [← ht, ODE.FunSpace.toContinuousMap_apply_eq_apply]
      exact ball_subset_ball (NNReal.coe_le_coe.mpr haa') (hα_ball t)
    exact T_eq_zero_of_isFixedPt_next hfu hPL hrange hα_fixed
  · -- ‖fderivIntegralCurry0 f (ball x₀ a') t₀ α.toContinuousMap‖ < 1
    exact hα_norm

/-- The derivative of `T` restricted to the second component is bijective when the norm of
`fderivIntegralCurry0 f u t₀ α` is less than 1. This is the key condition for the implicit function
theorem to apply. -/
lemma bijective_fderivT_comp_inr {f : E → E} {u : Set E}
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hnorm : ‖fderivIntegralCurry0 f u t₀ α‖ < 1) :
    Function.Bijective ((fderivT f u t₀ α).comp (ContinuousLinearMap.inr ℝ E _)) := by
  rw [fderivT_comp_inr t₀]
  -- Show -id + A = -(id - A), and bijectivity of negation preserves bijectivity
  have heq : -ContinuousLinearMap.id ℝ C(Icc tmin tmax, E) + fderivIntegralCurry0 f u t₀ α =
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
    (Neg.neg ∘ ⇑(ContinuousLinearMap.id ℝ C(Icc tmin tmax, E) - fderivIntegralCurry0 f u t₀ α))
  exact (ContinuousLinearEquiv.neg ℝ (M := C(Icc tmin tmax, E))).bijective.comp hbij

/-- The implicit function theorem applies to `T f u t₀` at a point `a = (x₀, α₀)` satisfying:
- `range α₀ ⊆ u` (the curve stays in the domain)
- `‖fderivIntegralCurry0 f u t₀ α₀‖ < 1` (the integral operator has small norm)
- `n ≥ 1` (we need at least `C^1` for the implicit function theorem) -/
lemma isContDiffImplicitAt_T {n : ℕ∞} {f : E → E} {u : Set E} (hf : ContDiffOn ℝ n f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) {α₀ : C(Icc tmin tmax, E)}
    (hα₀ : range α₀ ⊆ u) (hnorm : ‖fderivIntegralCurry0 f u t₀ α₀‖ < 1) (hn : 1 ≤ n) :
    IsContDiffImplicitAt n (T f u t₀) (fderivT f u t₀ α₀) (x₀, α₀) where
  hasFDerivAt := hasFDerivAt_T (hf.of_le (mod_cast hn)) hu t₀ hα₀
  contDiffAt := contDiffAt_T hu t₀ n hf hα₀
  bijective := bijective_fderivT_comp_inr t₀ hnorm
  ne_zero := by
    simp only [ne_eq, WithTop.coe_eq_zero]
    exact (one_pos.trans_le hn).ne'

/-- When f is C^1 at x₀, the implicit function theorem provides a local flow: there exist
ε > 0, a > 0, and a function `lf : E → C(Icc (t₀ - ε) (t₀ + ε), E)` such that for x near x₀:
- `lf x` is an integral curve of `f` on `Icc (t₀ - ε) (t₀ + ε)`
- `lf x` passes through `x` at time `t₀`
Furthermore, `lf` is C^1 at x₀.

This is the key result connecting the ODE theory to the implicit function theorem. -/
lemma exists_localFlow {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (lf : E → C(Icc (t₀ - ε) (t₀ + ε), E)),
        (∀ᶠ x in 𝓝 x₀,
          (∀ t (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)),
            HasDerivWithinAt (compProj ⟨t₀, by simp [le_of_lt hε]⟩ (lf x))
              (f ((lf x) ⟨t, ht⟩)) (Icc (t₀ - ε) (t₀ + ε)) t) ∧
          (lf x) ⟨t₀, by simp [le_of_lt hε]⟩ = x) ∧
        ContDiffAt ℝ 1 lf x₀ := by
  obtain ⟨ε, hεpos, a, _, α₀, hf_diff, hα₀_range, hT_zero, hnorm⟩ :=
    exists_contMap_T_eq_zero_opNorm_lt_one hf t₀
  set t₀' : Icc (t₀ - ε) (t₀ + ε) := ⟨t₀, by simp [le_of_lt hεpos]⟩
  set h := isContDiffImplicitAt_T hf_diff isOpen_ball t₀' x₀ hα₀_range hnorm le_rfl
  refine ⟨ε, hεpos, h.implicitFunction, ?_, h.contDiffAt_implicitFunction⟩
  -- α₀ = h.implicitFunction x₀ by the implicit function theorem
  have hα₀_eq : h.implicitFunction x₀ = α₀ := h.implicitFunction_apply_self
  -- Since lf is continuous and range α₀ ⊆ ball x₀ a (open), range (lf x) ⊆ ball x₀ a for x near x₀
  have hcont_lf : ContinuousAt h.implicitFunction x₀ :=
    h.contDiffAt_implicitFunction.continuousAt
  have hrange_near : ∀ᶠ x in 𝓝 x₀, range (h.implicitFunction x) ⊆ ball x₀ a := by
    -- Use continuity: for x near x₀, ‖lf x - lf x₀‖ is small, so range (lf x) ⊆ ball x₀ a
    -- Since range α₀ ⊆ ball x₀ a and ball is open, there's room for perturbation
    have hcompact : IsCompact (range α₀) := isCompact_range α₀.continuous
    -- Find δ > 0 such that thickening δ (range α₀) ⊆ ball x₀ a
    obtain ⟨δ, hδpos, hthickening⟩ := hcompact.exists_thickening_subset_open isOpen_ball hα₀_range
    -- For x near x₀, ‖lf x - α₀‖ < δ (in sup norm)
    have hcont_near : ∀ᶠ x in 𝓝 x₀, dist (h.implicitFunction x) α₀ < δ := by
      have := hcont_lf.eventually (Metric.ball_mem_nhds (h.implicitFunction x₀) hδpos)
      simp only [hα₀_eq] at this
      exact this
    filter_upwards [hcont_near] with x hx
    intro y hy
    obtain ⟨t, rfl⟩ := hy
    apply hthickening
    rw [Metric.mem_thickening_iff]
    exact ⟨α₀ t, mem_range_self t, (ContinuousMap.dist_apply_le_dist t).trans_lt hx⟩
  filter_upwards [h.apply_implicitFunction, hrange_near] with x hT_eq hrange
  have hfu : ContinuousOn f (ball x₀ a) := hf_diff.continuousOn
  constructor
  · intro t ht
    exact hasDerivWithinAt_of_T_eq_zero hfu hrange (by rw [hT_eq, hT_zero]) ht
  · exact eq_of_T_eq_zero hfu hrange (by rw [hT_eq, hT_zero])

end

end SmoothFlow
