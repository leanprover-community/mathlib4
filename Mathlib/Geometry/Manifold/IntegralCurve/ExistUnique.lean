/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Existence and uniqueness of integral curves

## Main results

* `exists_isIntegralCurveAt_of_contMDiffAt_boundaryless`: Existence of local integral curves for a
$C^1$ vector field. This follows from the existence theorem for solutions to ODEs
(`exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt`).
* `isIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`: Uniqueness of local integral curves for a
$C^1$ vector field. This follows from the uniqueness theorem for solutions to ODEs
(`ODE_solution_unique_of_mem_set_Ioo`). This requires the manifold to be Hausdorff (`T2Space`).

## Implementation notes

For the existence and uniqueness theorems, we assume that the image of the integral curve lies in
the interior of the manifold. The case where the integral curve may lie on the boundary of the
manifold requires special treatment, and we leave it as a TODO.

We state simpler versions of the theorem for boundaryless manifolds as corollaries.

## TODO

* The case where the integral curve may venture to the boundary of the manifold. See Theorem 9.34,
Lee. May require submanifolds.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field, local existence, uniqueness
-/


open scoped Manifold Topology

open Function Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} (t₀ : ℝ) {x₀ : M}

/-- Let $f : \mathbb{R} \to E$, $x_t = \phi^{-1} (f(t))$, and $v : TM_{x_t}$. If
$f' = (\phi_{x_0} \circ \phi_{x_t}^{-1})' v$, then
$(\phi_{x_t} \circ \phi_{x_0}^{-1} \circ f)' = v$. -/
lemma hasDerivAt_extChartAt_comp_extChartAt_comp_of_hasDerivAt_tangentCoordChange
    {x₀ : M} {f : ℝ → E} {t : ℝ} {v : TangentSpace I ((extChartAt I x₀).symm (f t))}
    (hmem : f t ∈ interior (extChartAt I x₀).target)
    (hf : let xₜ : M := (extChartAt I x₀).symm (f t)
      HasDerivAt f (tangentCoordChange I xₜ x₀ xₜ v) t) :
    let xₜ : M := (extChartAt I x₀).symm (f t)
    HasDerivAt (((extChartAt I xₜ) ∘ (extChartAt I x₀).symm) ∘ f) v t := by
  dsimp only
  let xₜ : M := (extChartAt I x₀).symm (f t)
  have hmem' := interior_subset hmem
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hmem' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  -- express `v` as `D⁻¹ D v`, where `D` is a change of coordinates, so we can use
  -- `HasFDerivAt.comp_hasDerivAt`
  rw [← tangentCoordChange_self (I := I) (v := v) hft2,
    ← tangentCoordChange_comp ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ hf
  apply HasFDerivWithinAt.hasFDerivAt (s := range I)
  · nth_rw 2 [← (extChartAt I x₀).right_inv hmem']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  · rw [mem_nhds_iff]
    exact ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..), isOpen_interior, hmem⟩

/-- Let `f : ℝ → E` and `v` be a tangent vector field on `M`. This lemma gives what `f'(t)` needs to
be in the model space in order for $(\phi_{x_0}^{-1} ∘ f)'(t) = v(\phi_{x_0}^{-1}(f(t))$ to hold
on the manifold. -/
lemma hasMFDerivAt_extChartAt_comp_of_hasDerivAt {v : (x : M) → TangentSpace I x} {x₀ : M}
    {f : ℝ → E} {t : ℝ} (hmem : f t ∈ interior (extChartAt I x₀).target)
    (hf : HasDerivAt f (((extChartAt I.tangent (⟨x₀, v x₀⟩ : TangentBundle I M)) ∘
      (fun x ↦ ⟨x, v x⟩) ∘ (extChartAt I x₀).symm) (f t)).2 t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I ((extChartAt I x₀).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt I x₀).symm (f t)))) := by
  let xₜ : M := (extChartAt I x₀).symm (f t)
  change HasDerivAt f (x := t) <| tangentCoordChange I xₜ x₀ xₜ (v xₜ) at hf
  -- express the derivative of the integral curve in the local chart
  have hmem' := interior_subset hmem
  refine ⟨continuousAt_extChartAt_symm'' hmem' |>.comp (x := t) hf.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  show HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  exact hasDerivAt_extChartAt_comp_extChartAt_comp_of_hasDerivAt_tangentCoordChange hmem hf

/-- Existence of local flows for a $C^1$ vector field at interior points of a $C^1$ manifold. -/
theorem exists_mem_nhds_isIntegralCurveOn_Ioo_of_contMDiffAt [CompleteSpace E]
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    ∃ u ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∃ γ : M × ℝ → M, ∀ x ∈ u, γ ⟨x, t₀⟩ = x ∧
      IsIntegralCurveOn (γ ⟨x, ·⟩) v (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ContinuousOn γ (u ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  -- express the differentiability of the vector field `v` in the local chart
  replace hv := contMDiffAt_iff.mp hv |>.2.contDiffAt (range_mem_nhds_isInteriorPoint hx)
  -- use Picard-Lindelöf theorem to extract a flow in the local chart
  have ⟨f, hf⟩ := hv.snd.exists_eventually_eq_hasDerivAt_continuousAt t₀
  clear hv
  simp only [Filter.eventually_and] at hf
  have ⟨hf1, hf2, hf3⟩ := hf
  have hf3' := hf3
  rw [nhds_prod_eq, Filter.eventually_prod_iff_exists_mem] at hf3'
  replace ⟨u0, hu0, s0, hs0, hf3'⟩ := hf3'
  -- `f ⟨x, t⟩` stays within `interior (extChartAt I x₀).target` if `⟨x, t⟩` is close to `⟨x₀, t₀⟩`
  have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ 𝓝 ⟨extChartAt I x₀ x₀, t₀⟩ := by
    apply hf3.self_of_nhds.preimage_mem_nhds
    apply isOpen_interior.mem_nhds
    rwa [hf1.self_of_nhds, ← I.isInteriorPoint_iff]
  rw [← eventually_mem_nhds_iff] at hnhds
  have hfmem : ∀ᶠ zt in 𝓝 ⟨extChartAt I x₀ x₀, t₀⟩, f zt ∈ interior (extChartAt I x₀).target :=
    hnhds.mono fun _ h ↦ mem_preimage.mp <| mem_of_mem_nhds h
  -- obtain a neighbourhood `u ×ˢ s` in which all of the above conditions hold
  replace hf := hf1.and <| hf2.and hfmem
  clear hf1 hf2 hf3
  rw [nhds_prod_eq] at hf
  replace ⟨u, hu, s, hs, hf⟩ := Filter.eventually_prod_iff_exists_mem.mp hf
  -- construct witnesses
  let U := (extChartAt I x₀) ⁻¹' (u0 ∩ u) ∩ (extChartAt I x₀).source
  have ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp <| Filter.inter_mem hs0 hs
  rw [Real.ball_eq_Ioo] at hεs
  let γ (xt : M × ℝ) := (extChartAt I x₀).symm <| f ⟨extChartAt I x₀ xt.1, xt.2⟩
  -- collect useful formulas
  have hmap : MapsTo (extChartAt I x₀) U (u0 ∩ u) := by
    intro x ⟨hx1, hx2⟩
    rwa [← mem_preimage]
  have ht₀ {x} (hx : x ∈ U) {t} (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :=
    hf _ (hmap hx).2 _ (hεs ht).2 |>.1
  have hderiv {x} (hx : x ∈ U) {t} (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :=
    hf _ (hmap hx).2 _ (hεs ht).2 |>.2.1
  have hmem {x} (hx : x ∈ U) {t} (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      f (extChartAt I x₀ x, t) ∈ interior (extChartAt I x₀).target :=
    hf _ (hmap hx).2 _ (hεs ht).2 |>.2.2
  have hmem' {x} (hx : x ∈ U) {t} (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      f (extChartAt I x₀ x, t) ∈ (extChartAt I x₀).target :=
    mem_of_mem_of_subset (hmem hx ht) interior_subset
  -- main proof
  refine ⟨U, ?_, ε, hε, γ, fun x hx ↦
    ⟨?_, fun t ht ↦ hasMFDerivAt_extChartAt_comp_of_hasDerivAt (hmem hx ht) (hderiv hx ht), ?_⟩⟩
  · apply Filter.inter_mem _ (extChartAt_source_mem_nhds _)
    exact continuousAt_extChartAt _ |>.preimage_mem_nhds <| Filter.inter_mem hu0 hu
  · symm
    have : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by
      rw [← Real.ball_eq_Ioo]
      exact Metric.mem_ball_self hε
    rw [PartialEquiv.eq_symm_apply _ hx.2 (hmem' hx this)]
    symm
    rw [ht₀ hx this]
  · apply ContinuousOn.comp' (continuousOn_extChartAt_symm x₀)
    · intro ⟨x', t'⟩ ⟨hx', ht'⟩
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.comp₂ _
        (ContinuousAt.comp (continuousAt_extChartAt' hx'.2) continuousAt_fst) continuousAt_snd
      simp only [comp_apply]
      exact hf3' _ (mem_preimage.mp <| (preimage_inter ▸ hx'.1).1) _ (hεs ht').1
    · intro ⟨x', t'⟩ ⟨hx', ht'⟩
      exact hmem' hx' ht'

/-- Existence of local integral curves for a $C^1$ vector field at interior points of a $C^1$
manifold. -/
theorem exists_isIntegralCurveAt_of_contMDiffAt [CompleteSpace E]
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ := by
  have ⟨u, hu, ε, hε, γ, h⟩ := exists_mem_nhds_isIntegralCurveOn_Ioo_of_contMDiffAt t₀ hv hx
  refine ⟨fun t ↦ γ ⟨x₀, t⟩, h _ (mem_of_mem_nhds hu) |>.1, ?_⟩
  rw [isIntegralCurveAt_iff]
  exact ⟨Ioo (t₀ - ε) (t₀ + ε), Ioo_mem_nhds (by linarith) (by linarith),
    h _ (mem_of_mem_nhds hu) |>.2.1⟩

/-- Existence of local integral curves for a $C^1$ vector field on a $C^1$ manifold without
boundary. -/
lemma exists_isIntegralCurveAt_of_contMDiffAt_boundaryless
    [CompleteSpace E] [BoundarylessManifold I M]
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ :=
  exists_isIntegralCurveAt_of_contMDiffAt t₀ hv BoundarylessManifold.isInteriorPoint

variable {t₀}

/-- Local integral curves are unique.

If a $C^1$ vector field `v` admits two local integral curves `γ γ' : ℝ → M` at `t₀` with
`γ t₀ = γ' t₀`, then `γ` and `γ'` agree on some open interval containing `t₀`. -/
theorem isIntegralCurveAt_eventuallyEq_of_contMDiffAt (hγt₀ : I.IsInteriorPoint (γ t₀))
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsIntegralCurveAt γ v t₀) (hγ' : IsIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    γ =ᶠ[𝓝 t₀] γ' := by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'
  -- extract a set `s` on which `v'` is Lipschitz
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  obtain ⟨K, s, hs, hlip⟩ : ∃ K, ∃ s ∈ 𝓝 _, LipschitzOnWith K v' s :=
    (hv.contDiffAt (range_mem_nhds_isInteriorPoint hγt₀)).snd.exists_lipschitzOnWith
  have hlip (t : ℝ) : LipschitzOnWith K ((fun _ ↦ v') t) ((fun _ ↦ s) t) := hlip
  -- internal lemmas to reduce code duplication
  have hsrc {g} (hg : IsIntegralCurveAt g v t₀) :
    ∀ᶠ t in 𝓝 t₀, g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝 t := eventually_mem_nhds_iff.mpr <|
      continuousAt_def.mp hg.continuousAt _ <| extChartAt_source_mem_nhds (g t₀)
  have hmem {g : ℝ → M} {t} (ht : g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝 t) :
    g t ∈ (extChartAt I (g t₀)).source := mem_preimage.mp <| mem_of_mem_nhds ht
  have hdrv {g} (hg : IsIntegralCurveAt g v t₀) (h' : γ t₀ = g t₀) : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt ((extChartAt I (g t₀)) ∘ g) ((fun _ ↦ v') t (((extChartAt I (g t₀)) ∘ g) t)) t ∧
      ((extChartAt I (g t₀)) ∘ g) t ∈ (fun _ ↦ s) t := by
    apply Filter.Eventually.and
    · apply (hsrc hg |>.and hg.eventually_hasDerivAt).mono
      rintro t ⟨ht1, ht2⟩
      rw [hv', h']
      apply ht2.congr_deriv
      congr <;>
      rw [Function.comp_apply, PartialEquiv.left_inv _ (hmem ht1)]
    · apply ((continuousAt_extChartAt (g t₀)).comp hg.continuousAt).preimage_mem_nhds
      rw [Function.comp_apply, ← h']
      exact hs
  have heq {g} (hg : IsIntegralCurveAt g v t₀) :
    g =ᶠ[𝓝 t₀] (extChartAt I (g t₀)).symm ∘ ↑(extChartAt I (g t₀)) ∘ g := by
    apply (hsrc hg).mono
    intros t ht
    rw [Function.comp_apply, Function.comp_apply, PartialEquiv.left_inv _ (hmem ht)]
  -- main proof
  suffices (extChartAt I (γ t₀)) ∘ γ =ᶠ[𝓝 t₀] (extChartAt I (γ' t₀)) ∘ γ' from
    (heq hγ).trans <| (this.fun_comp (extChartAt I (γ t₀)).symm).trans (h ▸ (heq hγ').symm)
  exact ODE_solution_unique_of_eventually (.of_forall hlip)
    (hdrv hγ rfl) (hdrv hγ' h) (by rw [Function.comp_apply, Function.comp_apply, h])

theorem isIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless [BoundarylessManifold I M]
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsIntegralCurveAt γ v t₀) (hγ' : IsIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    γ =ᶠ[𝓝 t₀] γ' :=
  isIntegralCurveAt_eventuallyEq_of_contMDiffAt BoundarylessManifold.isInteriorPoint hv hγ hγ' h

variable [T2Space M] {a b : ℝ}

/-- Integral curves are unique on open intervals.

If a $C^1$ vector field `v` admits two integral curves `γ γ' : ℝ → M` on some open interval
`Ioo a b`, and `γ t₀ = γ' t₀` for some `t ∈ Ioo a b`, then `γ` and `γ'` agree on `Ioo a b`. -/
theorem isIntegralCurveOn_Ioo_eqOn_of_contMDiff (ht₀ : t₀ ∈ Ioo a b)
    (hγt : ∀ t ∈ Ioo a b, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurveOn γ v (Ioo a b)) (hγ' : IsIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) := by
  set s := {t | γ t = γ' t} ∩ Ioo a b with hs
  -- since `Ioo a b` is connected, we get `s = Ioo a b` by showing that `s` is clopen in `Ioo a b`
  -- in the subtype topology (`s` is also non-empty by assumption)
  -- here we use a slightly weaker alternative theorem
  suffices hsub : Ioo a b ⊆ s from fun t ht ↦ mem_setOf.mp ((subset_def ▸ hsub) t ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨h, ht₀⟩⟩⟩
  · -- is this really the most convenient way to pass to subtype topology?
    -- TODO: shorten this when better API around subtype topology exists
    rw [hs, inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_setOf_eq]
    intros t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact hγ.continuousAt ht
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact hγ'.continuousAt ht
  · rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have hmem := Ioo_mem_nhds ht₁.2.1 ht₁.2.2
    have heq : γ =ᶠ[𝓝 t₁] γ' := isIntegralCurveAt_eventuallyEq_of_contMDiffAt
      (hγt _ ht₁.2) hv.contMDiffAt (hγ.isIntegralCurveAt hmem) (hγ'.isIntegralCurveAt hmem) ht₁.1
    apply (heq.and hmem).mono
    exact fun _ ht ↦ ht

theorem isIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (ht₀ : t₀ ∈ Ioo a b)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurveOn γ v (Ioo a b)) (hγ' : IsIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) :=
  isIntegralCurveOn_Ioo_eqOn_of_contMDiff
    ht₀ (fun _ _ ↦ BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

/-- Global integral curves are unique.

If a continuously differentiable vector field `v` admits two global integral curves
`γ γ' : ℝ → M`, and `γ t₀ = γ' t₀` for some `t₀`, then `γ` and `γ'` are equal. -/
theorem isIntegralCurve_eq_of_contMDiff (hγt : ∀ t, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurve γ v) (hγ' : IsIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' := by
  ext t
  obtain ⟨T, ht₀, ht⟩ : ∃ T, t ∈ Ioo (-T) T ∧ t₀ ∈ Ioo (-T) T := by
    obtain ⟨T, hT₁, hT₂⟩ := exists_abs_lt t
    obtain ⟨hT₂, hT₃⟩ := abs_lt.mp hT₂
    obtain ⟨S, hS₁, hS₂⟩ := exists_abs_lt t₀
    obtain ⟨hS₂, hS₃⟩ := abs_lt.mp hS₂
    exact ⟨T + S, by constructor <;> constructor <;> linarith⟩
  exact isIntegralCurveOn_Ioo_eqOn_of_contMDiff ht (fun t _ ↦ hγt t) hv
    ((hγ.isIntegralCurveOn _).mono (subset_univ _))
    ((hγ'.isIntegralCurveOn _).mono (subset_univ _)) h ht₀

theorem isIntegralCurve_Ioo_eq_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurve γ v) (hγ' : IsIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' :=
  isIntegralCurve_eq_of_contMDiff (fun _ ↦ BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

/-- For a global integral curve `γ`, if it crosses itself at `a b : ℝ`, then it is periodic with
period `a - b`. -/
lemma IsIntegralCurve.periodic_of_eq [BoundarylessManifold I M]
    (hγ : IsIntegralCurve γ v)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (heq : γ a = γ b) : Periodic γ (a - b) := by
  intro t
  apply congrFun <|
    isIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := b) hv (hγ.comp_add _) hγ _
  rw [comp_apply, add_sub_cancel, heq]

/-- A global integral curve is injective xor periodic with positive period. -/
lemma IsIntegralCurve.periodic_xor_injective [BoundarylessManifold I M]
    (hγ : IsIntegralCurve γ v)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    Xor' (∃ T > 0, Periodic γ T) (Injective γ) := by
  rw [xor_iff_iff_not]
  refine ⟨fun ⟨T, hT, hf⟩ ↦ hf.not_injective (ne_of_gt hT), ?_⟩
  intro h
  rw [Injective] at h
  push_neg at h
  obtain ⟨a, b, heq, hne⟩ := h
  refine ⟨|a - b|, ?_, ?_⟩
  · rw [gt_iff_lt, abs_pos, sub_ne_zero]
    exact hne
  · by_cases hab : a - b < 0
    · rw [abs_of_neg hab, neg_sub]
      exact hγ.periodic_of_eq hv heq.symm
    · rw [not_lt] at hab
      rw [abs_of_nonneg hab]
      exact hγ.periodic_of_eq hv heq
