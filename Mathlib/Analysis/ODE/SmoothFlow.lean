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

/-- The distance between two points in `Icc tmin tmax` is at most `|tmax - tmin|`. -/
-- TODO: move somewhere
lemma _root_.Set.Icc.abs_sub_le {tmin tmax : ℝ} (t t₀ : Icc tmin tmax) :
    |(t : ℝ) - t₀| ≤ |tmax - tmin| := by
  apply abs_le_abs <;> linarith [t.2.1, t.2.2, t₀.2.1, t₀.2.2]

namespace SmoothFlow

noncomputable section

/-! ## Technical definitions and lemmas for converting `C(Icc tmin tmax, E)` to `ℝ → E` -/

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

/-- Joint continuity of evaluating a family of curves via `compProj`. -/
lemma _root_.Continuous.continuous_compProj_pi_apply₂ {X : Type*} [TopologicalSpace X]
    {ι : Type*} {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {f : X → ι → C(Icc tmin tmax, E)}
    (hf : Continuous f) :
    Continuous (fun p : X × ℝ ↦ fun i ↦ compProj t₀ (f p.1 i) p.2) :=
  continuous_pi fun i ↦ ((continuous_apply i).comp hf).continuous_compProj_pi₂ t₀

/-! ## Construction of the integral term as a continuous multilinear map on the space of curves -/

variable [NormedSpace ℝ E]

/-- The integral
$$\int_{t₀}^t g(\alpha(\tau))(d\alpha_1(\tau),\cdots,d\alpha_n(\tau)) \,d\tau,$$
where `g : x → E [×n]→L[ℝ] E` has the same type as the `n`-th iterated derivative of `f : E → E`.

This is defined so that its derivative with respect to the curve `α` will yield the same integral
expression, but with `n` replaced by `n + 1` and `g` replaced by its derivative. -/
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
  exact fun t ↦ (continuous_integrand hg t₀ hα dα).integral_hasStrictDerivAt t₀ t
    |>.hasDerivAt.continuousAt

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

lemma integralCM_apply_if_pos {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {hg : ContinuousOn g u}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u)
    {dα : Fin n → C(Icc tmin tmax, E)} {t : Icc tmin tmax} :
    integralCM hg t₀ α dα t = integralFun g t₀ α dα t := by
  simp [integralCM_def, dif_pos hα, integralCMAux]

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
  · apply ContinuousMap.continuous_of_continuous_uncurry
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

lemma integralCMLM_apply {n : ℕ} {g : E → E [×n]→L[ℝ] E} {u : Set E} {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax} {α : C(Icc tmin tmax, E)}
    (hg : ContinuousOn g u) (hα : range α ⊆ u)
    {dα : Fin n → C(Icc tmin tmax, E)} {t : Icc tmin tmax} :
    integralCMLM g u t₀ α dα t =
      ∫ τ in (t₀ : ℝ)..(t : ℝ), g (compProj t₀ α τ) (fun i ↦ compProj t₀ (dα i) τ) := by
  rw [integralCMLM_apply_if_pos hg, integralCM_apply_if_pos hα, integralFun]

/-! ## Derivative of `integralCMLM` -/

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
  have hg' : ContinuousOn (fun x ↦ (fderiv ℝ g x).uncurryLeft (Ei := fun _ ↦ E)) u :=
    continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ E) E |>.symm.continuous.comp_continuousOn
      <| hg.continuousOn_fderiv_of_isOpen hu le_rfl
  have hinteg₁ := intervalIntegrable_integrand hg.continuousOn t₀ hα' dα t₀ t
  have hinteg₂ := intervalIntegrable_integrand hg.continuousOn t₀ hα dα t₀ t
  have hinteg₃ := intervalIntegrable_integrand hg' t₀ hα (Fin.cons (α' - α) dα) t₀ t
  simp only [sub_apply, curryLeft_apply, integralCMLM_apply hg.continuousOn hα',
    integralCMLM_apply hg.continuousOn hα, integralCMLM_apply hg' hα, ContinuousMap.sub_apply,
    ← intervalIntegral.integral_sub hinteg₁ hinteg₂,
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
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let ε' := ε / (1 + |tmax - tmin|)
  have hε' : 0 < ε' := by positivity
  have hs : IsCompact (range α) := isCompact_range α.continuous
  have hfderiv : ContinuousOn (fderiv ℝ g) u := hg.continuousOn_fderiv_of_isOpen hu le_rfl
  obtain ⟨δ₁, hδ₁, hthick⟩ := hs.exists_thickening_subset_open hu hα
  obtain ⟨δ₂, hδ₂, hdist⟩ := hs.exists_forall_le_dist
    (fun x hx ↦ hfderiv.continuousAt (hu.mem_nhds (hα hx))) hε'
  rw [Metric.eventually_nhds_iff]
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun α' hdist' ↦ ?_⟩
  have h1 : ∀ x ∈ range α, ∀ z, dist x z < min δ₁ δ₂ → z ∈ u := fun x hx z hz ↦
    hthick (mem_thickening_iff.mpr ⟨x, hx, dist_comm x z ▸ hz.trans_le (min_le_left _ _)⟩)
  have h2 : ∀ x ∈ range α, ∀ z, dist x z < min δ₁ δ₂ → dist (fderiv ℝ g x) (fderiv ℝ g z) < ε' :=
    fun x hx z hz ↦ hdist x hx z (hz.trans_le (min_le_right _ _))
  have hα' : range α' ⊆ u := fun _ ⟨t, ht⟩ ↦ ht ▸ h1 (α t) (mem_range_self t) _ (by
    rw [dist_comm, dist_eq_norm]
    exact (ContinuousMap.norm_coe_le_norm (α' - α) t).trans_lt (dist_eq_norm α' α ▸ hdist'))
  -- Reduce bound on `ContinuousLinearMap`s to a bound on elements of `E`
  refine norm_integralCMLM_sub_fderiv_le hg hu t₀ hα hα' hε fun t ↦ ?_
  calc
    _ = ‖g (compProj t₀ α' t) - g (compProj t₀ α t) -
        (fderiv ℝ g (compProj t₀ α t)) (compProj t₀ α' t - compProj t₀ α t)‖ := by
      simp only [compProj, ContinuousMap.sub_apply]
    _ ≤ ε' * ‖compProj t₀ α' t - compProj t₀ α t‖ := ?_
    _ ≤ ε' * ‖α' - α‖ := by
      gcongr; exact ContinuousMap.norm_coe_le_norm (α' - α) _
  -- Apply the mean value theorem
  let x := compProj t₀ α t
  let y := compProj t₀ α' t
  have hseg : ∀ z ∈ segment ℝ x y, dist x z < min δ₁ δ₂ := fun z hz ↦ calc
    dist x z ≤ dist x y := mem_closedBall'.mp (segment_subset_closedBall_left x y hz)
    _ = ‖y - x‖ := dist_eq_norm' x y
    _ ≤ ‖α' - α‖ := (α' - α).norm_coe_le_norm _
    _ < min δ₁ δ₂ := dist_eq_norm α' α ▸ hdist'
  apply (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le' _ _
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  · intro z hz
    apply (hg.differentiableOn one_ne_zero).differentiableAt (hu.mem_nhds _)
    exact h1 x (mem_range_self _) z (hseg z hz)
  · intro z hz
    rw [norm_sub_rev, ← dist_eq_norm]
    exact h2 x (mem_range_self _) z (hseg z hz) |>.le

/-! ## Smoothness of `integralCMLM` -/

/-- Composition of a function `g : E → F` continuous on `u` with a continuous curve `α : C(I, E)`
whose range is contained in `u`, yielding a continuous curve `C(I, F)`. -/
def gComp (I : Type*) {F : Type*} [TopologicalSpace I] [TopologicalSpace F] {g : E → F} {u : Set E}
    (hg : ContinuousOn g u) (α : {α : C(I, E) | range α ⊆ u}) : C(I, F) :=
  ⟨g ∘ α, hg.comp_continuous α.1.continuous_toFun (fun _ ↦ α.2 (mem_range_self _))⟩

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
  intro α₀ U hU
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
  intro α hα ⟨dα, hdα⟩
  rw [mem_preimage, mem_ball, ContinuousMap.dist_lt_iff hδ] at hα
  apply hεU
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  rw [integralCMLM_apply hg α₀.2, integralCMLM_apply hg α.2, dist_eq_norm,
    ← integral_sub (intervalIntegrable_integrand hg _ α₀.2 ..)
      (intervalIntegrable_integrand hg _ α.2 ..), Subtype.coe_mk dα]
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
      -- TODO: replace with `prod_le_pow_card'` that works on `ℝ`, not just `ℝ≥0`
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
      have hg' : ContDiffOn ℝ k (fun x ↦ (fderiv ℝ g x).uncurryLeft (Ei := fun _ ↦ E)) u :=
        continuousMultilinearCurryLeftEquiv ℝ (fun _ ↦ E) E
          |>.symm.contDiff.comp_contDiffOn <| hg.fderiv_of_isOpen hu le_rfl
      apply (continuousMultilinearCurryLeftEquiv ℝ _ _).contDiff.comp_contDiffOn (ih hg') |>.congr
      intro α hα
      rw [(hasFDerivAt_integralCMLM hg.one_of_succ hu t₀ hα).fderiv]
      rfl

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

/-! ## Implicit equation `T` -/

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
lemma T_eq_zero_of_isFixedPt_next {f : E → E} {u : Set E} (hf : ContinuousOn f u)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a L K : ℝ≥0}
    (hPL : IsPicardLindelof (fun _ ↦ f) t₀ x₀ a 0 L K) {α : ODE.FunSpace t₀ x₀ 0 L}
    (hα : range α ⊆ u) (h : IsFixedPt (ODE.FunSpace.next hPL (mem_closedBall_self le_rfl)) α) :
    T f u t₀ (x₀, α.toContinuousMap) = 0 := by
  ext t
  have heq := (ODE.FunSpace.isFixedPt_next_iff hPL (mem_closedBall_self le_rfl)).mp h t
  have hf' : ContinuousOn (fun x ↦ uncurry0 ℝ E (f x)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp_continuousOn hf
  rw [T, curry0_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ODE.FunSpace.toContinuousMap_apply_eq_apply, ContinuousMap.zero_apply, heq, ODE.picard_apply,
    integralCMLM_apply hf' hα, sub_add_cancel_left, neg_add_eq_zero]
  rfl

/-- If `T f u t₀ (x₀, α) = 0`, then `α` satisfies the integral equation for the ODE `α' = f ∘ α`
with initial condition `α t₀ = x₀`. This is equivalent to saying `α` is an integral curve of `f`. -/
lemma eq_picard_of_T_eq_zero {f : E → E} {u : Set E} (hf : ContinuousOn f u)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) (hT : T f u t₀ (x₀, α) = 0) (t : Icc tmin tmax) :
    α t = ODE.picard (fun _ ↦ f) t₀ x₀ (fun t ↦ compProj t₀ α t) t := by
  replace hT := ContinuousMap.ext_iff.mp hT t
  have hf' : ContinuousOn (fun x ↦ uncurry0 ℝ E (f x)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp_continuousOn hf
  rw [T, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.zero_apply, ContinuousMultilinearMap.curry0_apply, integralCMLM_apply hf' hα,
    sub_add_eq_add_sub, sub_eq_zero] at hT
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

/-- Restrict a continuous map from `Icc tmin tmax` to a smaller interval `Icc tmin' tmax'`. -/
def restrictIcc {tmin tmax tmin' tmax' : ℝ}
    (α : C(Icc tmin tmax, E)) (htmin : tmin ≤ tmin') (htmax : tmax' ≤ tmax) :
    C(Icc tmin' tmax', E) :=
  α.comp ⟨fun t ↦ ⟨t.1, ⟨htmin.trans t.2.1, t.2.2.trans htmax⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp]
lemma restrictIcc_apply {tmin tmax tmin' tmax' : ℝ}
    (α : C(Icc tmin tmax, E)) (htmin : tmin ≤ tmin') (htmax : tmax' ≤ tmax)
    (t : Icc tmin' tmax') :
    restrictIcc α htmin htmax t = α ⟨t.1, ⟨htmin.trans t.2.1, t.2.2.trans htmax⟩⟩ := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma range_restrictIcc_subset {tmin tmax tmin' tmax' : ℝ}
    (α : C(Icc tmin tmax, E)) (htmin : tmin ≤ tmin') (htmax : tmax' ≤ tmax) :
    range (restrictIcc α htmin htmax) ⊆ range α := by
  intro y hy
  obtain ⟨t, ht⟩ := hy
  exact ⟨⟨t.1, ⟨htmin.trans t.2.1, t.2.2.trans htmax⟩⟩, ht⟩

/-- If `T f u t₀ (x₀, α) = 0` on `[tmin, tmax]`, then it also holds on any smaller interval
`[tmin', tmax']` containing `t₀`. This reflects the fact that being an integral curve is a local
property: the ODE `α' = f ∘ α` with initial condition `α t₀ = x₀` has the same solution on any
interval containing `t₀`. -/
lemma T_restrictIcc_eq_zero {f : E → E} {u : Set E} (hf : ContinuousOn f u)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) (hT : T f u t₀ (x₀, α) = 0)
    {tmin' tmax' : ℝ} (htmin : tmin ≤ tmin') (htmax : tmax' ≤ tmax)
    (ht₀min : tmin' ≤ t₀.1) (ht₀max : t₀.1 ≤ tmax') :
    T f u ⟨t₀.1, ⟨ht₀min, ht₀max⟩⟩ (x₀, restrictIcc α htmin htmax) = 0 := by
  ext t
  have hf' : ContinuousOn (fun x ↦ uncurry0 ℝ E (f x)) u :=
    (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp_continuousOn hf
  have hα' : range (restrictIcc α htmin htmax) ⊆ u :=
    (range_restrictIcc_subset α htmin htmax).trans hα
  rw [T, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.zero_apply, curry0_apply, integralCMLM_apply hf' hα', restrictIcc_apply]
  simp_rw [uncurry0_apply]
  rw [eq_picard_of_T_eq_zero hf hα hT ⟨t.1, ⟨htmin.trans t.2.1, t.2.2.trans htmax⟩⟩,
    ODE.picard_apply, sub_add_cancel_left, neg_add_eq_zero]
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hτ' : τ ∈ Icc tmin tmax :=
    uIcc_subset_Icc t₀.2 ⟨htmin.trans t.2.1, t.2.2.trans htmax⟩ hτ
  simp only [compProj, restrictIcc_apply, projIcc_of_mem (t₀.2.1.trans t₀.2.2) hτ',
    projIcc_of_mem (ht₀min.trans ht₀max) (uIcc_subset_Icc ⟨ht₀min, ht₀max⟩ t.2 hτ)]

/-- Given a `C^k` vector field at `x₀` (`k ≥ 1`) and any neighborhood `u` of `x₀` on which `f` is
continuous, there exists an integral curve on some time interval whose range is contained in `u`
and satisfies `T f u t₀ (x₀, α) = 0`.

This lemma packages the Picard-Lindelöf construction in a filter-friendly form: the caller provides
a neighborhood, and the lemma returns an integral curve staying within that neighborhood. -/
lemma exists_integralCurve_T_eq_zero {f : E → E} {x₀ : E} {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiffAt ℝ k f x₀) (t₀ : ℝ) {u : Set E} (hu : u ∈ 𝓝 x₀) (hfu : ContinuousOn f u) :
    ∃ (ε : ℝ) (hε : 0 < ε) (α : C(Icc (t₀ - ε) (t₀ + ε), E)),
      range α ⊆ u ∧ T f u ⟨t₀, by simp [le_of_lt hε]⟩ (x₀, α) = 0 := by
  -- Get Picard-Lindelöf parameters from the C^1 condition
  obtain ⟨ε₀, hε₀pos, a, r, L, K, hrpos, hPL⟩ :=
    IsPicardLindelof.of_contDiffAt_one (hf.of_le (by exact_mod_cast hk))
  have hapos : (0 : ℝ) < a := by
    have := (hPL t₀).mul_max_le
    simp only [add_sub_cancel_left, sub_sub_cancel, max_self] at this
    have hLε : (0 : ℝ) ≤ L * ε₀ := by positivity
    have hrpos' : (0 : ℝ) < r := hrpos
    linarith
  -- Extract a ball from the neighborhood `u`
  obtain ⟨δ, hδpos, hδ_sub⟩ := Metric.mem_nhds_iff.mp hu
  -- Choose `a'` to fit inside both the Picard-Lindelöf ball and `u`
  have ha'pos : 0 < min ((a : ℝ) / 2) (δ / 2) := by positivity
  let a' : ℝ≥0 := ⟨min (a / 2) (δ / 2), le_of_lt ha'pos⟩
  have ha'le : a' ≤ a := (min_le_left _ _).trans (half_le_self hapos.le)
  have ha'lt : (a' : ℝ) < δ := (min_le_right _ _).trans_lt (half_lt_self hδpos)
  -- Shrink Picard-Lindelöf to a smaller time interval with `r = 0` and smaller `a'`
  obtain ⟨ε, hεpos, hPL'⟩ :=
    (hPL t₀).exists_shrink_radius hε₀pos ha'le (zero_lt_iff.mpr (ne_of_gt ha'pos))
  -- Get the fixed point (integral curve) from Picard-Lindelöf
  obtain ⟨α_fun, hα_fixed⟩ := ODE.FunSpace.exists_isFixedPt_next hPL' (mem_closedBall_self le_rfl)
  let α := α_fun.toContinuousMap
  have hα_range : range α ⊆ u := by
    rintro _ ⟨t, rfl⟩
    rw [ODE.FunSpace.toContinuousMap_apply_eq_apply]
    exact hδ_sub <| closedBall_subset_ball ha'lt <| α_fun.mem_closedBall hPL'.mul_max_le
  exact ⟨ε, hεpos, α, hα_range, T_eq_zero_of_isFixedPt_next hfu hPL' hα_range hα_fixed⟩

/-! ## Derivative of `T` -/

/-- The derivative of `fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0` at `α`,
which appears as a component of the derivative of `T`. This is the composition of `curry0` with
the derivative of `integralCMLM`. -/
def fderivIntegralCurry0 (f : E → E) (u : Set E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (α : C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) :=
  (continuousMultilinearCurryFin0 ℝ C(Icc tmin tmax, E)
      C(Icc tmin tmax, E)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((integralCMLM (iteratedFDeriv ℝ 1 f) u t₀ α).curryLeft)

/-- `fderivIntegralCurry0 f u t₀ α` is the Fréchet derivative of
`fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0` at `α`. -/
lemma hasFDerivAt_integralCMLM_curry0 {f : E → E} {u : Set E} {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) :
    HasFDerivAt (fun α ↦ (integralCMLM (fun x ↦ uncurry0 ℝ E (f x)) u t₀ α).curry0)
      (fderivIntegralCurry0 f u t₀ α) α := by
  have hf₁ : ContDiffOn ℝ 1 f u := hf.of_le (by exact_mod_cast hk)
  have hf' : ContDiffOn ℝ 1 (fun y ↦ uncurry0 ℝ E (f y)) u :=
    continuousMultilinearCurryFin0 ℝ E E |>.symm.contDiff.comp_contDiffOn hf₁
  have heq : iteratedFDeriv ℝ 1 f =
      fun x ↦ (fderiv ℝ (fun y ↦ uncurry0 ℝ E (f y)) x).uncurryLeft := by
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_zero_eq_comp]; rfl
  rw [fderivIntegralCurry0, heq]
  exact continuousMultilinearCurryFin0 ℝ C(Icc tmin tmax, E) C(Icc tmin tmax, E)
    |>.toContinuousLinearEquiv.hasFDerivAt.comp α <| hasFDerivAt_integralCMLM hf' hu t₀ hα

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
lemma hasFDerivAt_T {f : E → E} {u : Set E} {k : ℕ} (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f u)
    (hu : IsOpen u)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {x : E} {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    HasFDerivAt (T f u t₀) (fderivT f u t₀ α) (x, α) := by
  apply (HasFDerivAt.sub _ hasFDerivAt_snd).add _
  · exact ContinuousLinearMap.const ℝ (Icc tmin tmax) (M := E)
      |>.hasFDerivAt.comp (x, α) hasFDerivAt_fst
  · exact (hasFDerivAt_integralCMLM_curry0 hk hf hu t₀ hα).comp (𝕜 := ℝ) (x, α) hasFDerivAt_snd

/-- The derivative of `T` restricted to the second component is
`-id + fderivIntegralCurry0 f u t₀ α`. We will show that this is invertible under certain
conditions. -/
lemma fderivT_comp_inr {f : E → E} {u : Set E}
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)} :
    (fderivT f u t₀ α).comp (ContinuousLinearMap.inr ℝ E _) =
      -ContinuousLinearMap.id ℝ _ + fderivIntegralCurry0 f u t₀ α := by
  ext y
  simp [fderivT]

/-- The derivative of `T` restricted to the second component is invertible when the norm of
`fderivIntegralCurry0 f u t₀ α` is less than 1. This is the key condition for the implicit function
theorem to apply. -/
lemma isInvertible_fderivT_comp_inr {f : E → E} {u : Set E}
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hnorm : ‖fderivIntegralCurry0 f u t₀ α‖ < 1) :
    ((fderivT f u t₀ α) ∘L (ContinuousLinearMap.inr ℝ E _)).IsInvertible := by
  rw [fderivT_comp_inr t₀, neg_add_eq_sub, ← neg_sub]
  have hu := isUnit_one_sub_of_norm_lt_one hnorm
  exact ⟨(ContinuousLinearEquiv.ofUnit hu.unit).trans (.neg ℝ),
    ContinuousLinearMap.ext fun _ => rfl⟩

/-- The operator norm of `fderivIntegralCurry0 f u t₀ α` is less than 1 when the time interval is
sufficiently small relative to the derivative bound on `range α`. -/
lemma opNorm_fderivIntegralCurry0_lt_one {f : E → E} {u : Set E} {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f u)
    (hu : IsOpen u) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) {α : C(Icc tmin tmax, E)}
    (hα : range α ⊆ u) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ range α, ‖fderiv ℝ f x‖ ≤ C)
    (hsmall : |tmax - tmin| * C < 1) :
    ‖fderivIntegralCurry0 f u t₀ α‖ < 1 := by
  have hf₁ : ContDiffOn ℝ 1 f u := hf.of_le (by exact_mod_cast hk)
  rw [fderivIntegralCurry0, ← LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry,
    continuousMultilinearCurryFin0 ℝ C(Icc tmin tmax, E) C(Icc tmin tmax, E)
      |>.toLinearIsometry.norm_toContinuousLinearMap_comp]
  apply lt_of_le_of_lt _ hsmall
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun dα ↦ ?_
  refine opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have hf' : ContinuousOn (iteratedFDeriv ℝ 1 f) u := fun _ hx ↦
    hf₁.contDiffAt (hu.mem_nhds hx) |>.iteratedFDeriv_right (m := 0) le_rfl
      |>.continuousAt.continuousWithinAt
  rw [curryLeft_apply, integralCMLM_apply hf' hα, Fin.prod_univ_zero, mul_one, mul_comm]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * ‖dα‖) ?_).trans ?_
  · intro τ hτ
    apply (le_opNorm _ _).trans
    rw [norm_iteratedFDeriv_one, Fin.prod_univ_one]
    have hτ' : τ ∈ Icc tmin tmax := uIcc_subset_Icc t₀.2 t.2 (uIoc_subset_uIcc hτ)
    have hmem : compProj t₀ α τ ∈ range α := ⟨⟨τ, hτ'⟩, (compProj_of_mem hτ').symm⟩
    exact mul_le_mul (hbound _ hmem) (dα.norm_coe_le_norm _) (norm_nonneg _) hC
  · rw [mul_comm _ C, ← mul_assoc, mul_comm _ C]
    gcongr 1
    exact Icc.abs_sub_le t t₀

/-- For `f` that is `C^k` at `x₀` (`k ≥ 1`), there exist a neighbourhood `u` of `x₀` and `ε > 0`
such that for any time interval `[tmin, tmax]` of size less than `ε` and any continuous curve
`α : [tmin, tmax] → E` with `range α ⊆ u`, the operator norm
`‖fderivIntegralCurry0 f u t₀ α‖ < 1`. -/
lemma exists_nhds_eps_opNorm_fderivIntegralCurry0_lt_one {f : E → E} {x₀ : E} {k : ℕ}
    (hk : 1 ≤ k) (hf : ContDiffAt ℝ k f x₀) :
    ∃ u ∈ 𝓝 x₀, IsOpen u ∧ ∃ ε > 0, ContDiffOn ℝ k f u ∧
      ∀ (tmin tmax : ℝ) (t₀ : Icc tmin tmax) (α : C(Icc tmin tmax, E)),
        range α ⊆ u → |tmax - tmin| < ε →
          ‖fderivIntegralCurry0 f u t₀ α‖ < 1 := by
  -- Get a neighborhood where `f` is `C^k`
  obtain ⟨s, hs_nhds, hfs⟩ := hf.contDiffOn le_rfl nofun
  have hf₁ : ContDiffAt ℝ 1 f x₀ := hf.of_le (by exact_mod_cast hk)
  -- Use continuity to find a neighborhood where the derivative is bounded
  let C := ‖fderiv ℝ f x₀‖ + 1
  have hCpos : 0 < C := by positivity
  have hbound_ev : ∀ᶠ x in 𝓝 x₀, ‖fderiv ℝ f x‖ ≤ C :=
    hf₁.fderiv_right (m := 0) le_rfl |>.continuousAt.norm.eventually_le_const (by linarith)
  -- Combine conditions and extract an open neighborhood
  have h_combined := Filter.eventually_mem_set.mpr hs_nhds |>.and hbound_ev
  obtain ⟨u, hu_cond, hu_open, hx₀u⟩ := _root_.eventually_nhds_iff.mp h_combined
  have hu_nhds : u ∈ 𝓝 x₀ := hu_open.mem_nhds hx₀u
  have hfu : ContDiffOn ℝ k f u := hfs.mono fun x hx ↦ (hu_cond x hx).1
  -- Choose ε so that ε * C < 1
  set ε := 1 / (C + 1) with hε_def
  have hεpos : 0 < ε := by positivity
  refine ⟨u, hu_nhds, hu_open, ε, hεpos, hfu, ?_⟩
  intro tmin tmax t₀ α hαu hsmall
  have hbound' : ∀ x ∈ range α, ‖fderiv ℝ f x‖ ≤ C := fun x hx ↦ (hu_cond x (hαu hx)).2
  apply opNorm_fderivIntegralCurry0_lt_one hk hfu hu_open t₀ hαu hCpos.le hbound'
  -- TODO: add usable version of `mul_lt_one` for reals
  calc
    _ < ε * C := mul_lt_mul_of_pos_right hsmall hCpos
    _ = C / (C + 1) := by rw [hε_def]; ring
    _ < 1 := (div_lt_one (by positivity : 0 < C + 1)).mpr (lt_add_one C)

/-! ## Connect to the existence of integral curves -/

/-- When `f` is `C^k` at `x₀` (`k ≥ 1`), there exist a neighbourhood `u` of `x₀`, `ε > 0`, and a
continuous map `α : C(Icc (t₀ - ε) (t₀ + ε), E)` such that `f` is `C^k` on `u`, the range of `α` is
in `u`, `T f u t₀ (x₀, α) = 0`, and `‖fderivIntegralCurry0 f u t₀ α‖ < 1`.

Note that `T = 0` implies `α t₀ = x₀` since the integral from `t₀` to `t₀` vanishes. -/
lemma exists_integralCurve_opNorm_fderivIntegralCurry0_lt_one {f : E → E} {x₀ : E} {k : ℕ}
    (hk : 1 ≤ k) (hf : ContDiffAt ℝ k f x₀) (t₀ : ℝ) :
    ∃ u ∈ 𝓝 x₀, IsOpen u ∧ ContDiffOn ℝ k f u ∧ ∃ (ε : ℝ) (hε : 0 < ε),
      ∃ α : C(Icc (t₀ - ε) (t₀ + ε), E),
        range α ⊆ u ∧
        T f u ⟨t₀, by simp [le_of_lt hε]⟩ (x₀, α) = 0 ∧
        ‖fderivIntegralCurry0 f u ⟨t₀, by simp [le_of_lt hε]⟩ α‖ < 1 := by
  obtain ⟨u, hu_nhds, hu_open, ε₀, hε₀pos, hfu, hfderiv_bound⟩ :=
    exists_nhds_eps_opNorm_fderivIntegralCurry0_lt_one hk hf
  -- Get an integral curve with range in `u`
  obtain ⟨ε₁, hε₁pos, α₁, hα₁_range, hT₁_zero⟩ :=
    exists_integralCurve_T_eq_zero hk hf t₀ hu_nhds hfu.continuousOn
  -- Restrict to `ε = min ε₁ (ε₀/4)` so that `2ε < ε₀`
  let ε := min (ε₀ / 4) ε₁
  have hεpos : 0 < ε := lt_min (by linarith) hε₁pos
  have hε_le : ε ≤ ε₀ / 4 := min_le_left _ _
  have hε_le_ε₁ : ε ≤ ε₁ := min_le_right _ _
  let α := restrictIcc α₁ (by linarith : t₀ - ε₁ ≤ t₀ - ε) (by linarith : t₀ + ε ≤ t₀ + ε₁)
  have hα_range : range α ⊆ u := (range_restrictIcc_subset α₁ _ _).trans hα₁_range
  have hT_zero : T f u ⟨t₀, by simp [le_of_lt hεpos]⟩ (x₀, α) = 0 :=
    T_restrictIcc_eq_zero hfu.continuousOn hα₁_range hT₁_zero (by linarith) (by linarith)
      (by simp [le_of_lt hεpos]) (by simp [le_of_lt hεpos])
  have hα_norm : ‖fderivIntegralCurry0 f u ⟨t₀, by simp [le_of_lt hεpos]⟩ α‖ < 1 := by
    apply hfderiv_bound _ _ ⟨t₀, by simp [le_of_lt hεpos]⟩ α hα_range
    rw [add_sub_sub_cancel, ← two_mul, abs_of_pos (by positivity)]
    linarith
  exact ⟨u, hu_nhds, hu_open, hfu, ε, hεpos, α, hα_range, hT_zero, hα_norm⟩

/-- When `f` is `C^k` at `x₀` (`k ≥ 1`), the implicit function theorem provides a local flow:
there exist `ε > 0`, `a > 0`, and a function `lf : E → C(Icc (t₀ - ε) (t₀ + ε), E)` such that
for `x` near `x₀`:
- `lf x` is an integral curve of `f` on `Icc (t₀ - ε) (t₀ + ε)`
- `lf x` passes through `x` at time `t₀`
Furthermore, `lf` is `C^k` at `x₀`.

This is the key result connecting the ODE theory to the implicit function theorem. -/
lemma exists_localFlow {f : E → E} {x₀ : E} {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiffAt ℝ k f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (hε : 0 < ε) (lf : E → C(Icc (t₀ - ε) (t₀ + ε), E)),
        (∀ᶠ x in 𝓝 x₀,
          (∀ t (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)),
            HasDerivWithinAt (compProj ⟨t₀, by simp [le_of_lt hε]⟩ (lf x))
              (f ((lf x) ⟨t, ht⟩)) (Icc (t₀ - ε) (t₀ + ε)) t) ∧
          (lf x) ⟨t₀, by simp [le_of_lt hε]⟩ = x) ∧
        ContDiffAt ℝ k lf x₀ := by
  obtain ⟨u, _, hu_open, hf_diff, ε, hεpos, α₀, hα₀_range, hT_zero, hnorm⟩ :=
    exists_integralCurve_opNorm_fderivIntegralCurry0_lt_one hk hf t₀
  let t₀' : Icc (t₀ - ε) (t₀ + ε) := ⟨t₀, by simp [le_of_lt hεpos]⟩
  have hcont : ContDiffAt ℝ k (T f u t₀') (x₀, α₀) := contDiffAt_T hu_open t₀' k hf_diff hα₀_range
  have hne : ((k : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  have hif₂ : (fderiv ℝ (T f u t₀') (x₀, α₀) ∘L .inr ℝ E _).IsInvertible := by
    rw [(hasFDerivAt_T hk hf_diff hu_open t₀' hα₀_range).fderiv]
    exact isInvertible_fderivT_comp_inr t₀' hnorm
  refine ⟨ε, hεpos, hcont.implicitFunction hne hif₂, ?_,
    hcont.contDiffAt_implicitFunction hne hif₂⟩
  have hrange_near : ∀ᶠ x in 𝓝 x₀, range (hcont.implicitFunction hne hif₂ x) ⊆ u := by
    apply (hcont.contDiffAt_implicitFunction hne hif₂).continuousAt.eventually
      <| ContinuousMap.eventually_range_subset hu_open _
    rw [hcont.implicitFunction_apply_self hne hif₂]
    exact hα₀_range
  filter_upwards [hcont.eventually_apply_implicitFunction hne hif₂, hrange_near] with x hT_eq hrange
  constructor
  · intro t ht
    exact hasDerivWithinAt_of_T_eq_zero hf_diff.continuousOn hrange (by rw [hT_eq, hT_zero]) ht
  · exact eq_of_T_eq_zero hf_diff.continuousOn hrange (by rw [hT_eq, hT_zero])

end

end SmoothFlow
