/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# The open mapping theorem for holomorphic functions

This file proves the open mapping theorem for holomorphic functions, namely that an analytic
function on a preconnected set of the complex plane is either constant or open. The main step is to
show a local version of the theorem that states that if `f` is analytic at a point `z₀`, then either
it is constant in a neighborhood of `z₀` or it maps any neighborhood of `z₀` to a neighborhood of
its image `f z₀`. The results extend in higher dimension to `g : E → ℂ`.

The proof of the local version on `ℂ` goes through two main steps: first, assuming that the function
is not constant around `z₀`, use the isolated zero principle to show that `‖f z‖` is bounded below
on a small `sphere z₀ r` around `z₀`, and then use the maximum principle applied to the auxiliary
function `(fun z ↦ ‖f z - v‖)` to show that any `v` close enough to `f z₀` is in `f '' ball z₀ r`.
That second step is implemented in `DiffContOnCl.ball_subset_image_closedBall`.

## Main results

* `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` is the local version of the open mapping
  theorem around a point;
* `AnalyticOnNhd.is_constant_or_isOpen` is the open mapping theorem on a connected open set.
-/


open Set Filter Metric Complex

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {f : ℂ → ℂ} {g : E → ℂ}
  {z₀ : ℂ} {ε r : ℝ}

/-- If the modulus of a holomorphic function `f` is bounded below by `ε` on a circle, then its range
contains a disk of radius `ε / 2`. -/
theorem DiffContOnCl.ball_subset_image_closedBall (h : DiffContOnCl ℂ f (ball z₀ r)) (hr : 0 < r)
    (hf : ∀ z ∈ sphere z₀ r, ε ≤ ‖f z - f z₀‖) (hz₀ : ∃ᶠ z in 𝓝 z₀, f z ≠ f z₀) :
    ball (f z₀) (ε / 2) ⊆ f '' closedBall z₀ r := by
  /- This is a direct application of the maximum principle. Pick `v` close to `f z₀`, and look at
    the function `fun z ↦ ‖f z - v‖`: it is bounded below on the circle, and takes a small value
    at `z₀` so it is not constant on the disk, which implies that its infimum is equal to `0` and
    hence that `v` is in the range of `f`. -/
  rintro v hv
  have h1 : DiffContOnCl ℂ (fun z => f z - v) (ball z₀ r) := h.sub_const v
  have h2 : ContinuousOn (fun z => ‖f z - v‖) (closedBall z₀ r) :=
    continuous_norm.comp_continuousOn (closure_ball z₀ hr.ne.symm ▸ h1.continuousOn)
  have h3 : AnalyticOnNhd ℂ f (ball z₀ r) := h.differentiableOn.analyticOnNhd isOpen_ball
  have h4 : ∀ z ∈ sphere z₀ r, ε / 2 ≤ ‖f z - v‖ := fun z hz => by
    linarith [hf z hz, show ‖v - f z₀‖ < ε / 2 from mem_ball.mp hv,
      norm_sub_sub_norm_sub_le_norm_sub (f z) v (f z₀)]
  have h5 : ‖f z₀ - v‖ < ε / 2 := by simpa [← dist_eq_norm, dist_comm] using mem_ball.mp hv
  obtain ⟨z, hz1, hz2⟩ : ∃ z ∈ ball z₀ r, IsLocalMin (fun z => ‖f z - v‖) z :=
    exists_isLocalMin_mem_ball h2 (mem_closedBall_self hr.le) fun z hz => h5.trans_le (h4 z hz)
  refine ⟨z, ball_subset_closedBall hz1, sub_eq_zero.mp ?_⟩
  have h6 := h1.differentiableOn.eventually_differentiableAt (isOpen_ball.mem_nhds hz1)
  refine (eventually_eq_or_eq_zero_of_isLocalMin_norm h6 hz2).resolve_left fun key => ?_
  have h7 : ∀ᶠ w in 𝓝 z, f w = f z := by filter_upwards [key] with h; field_simp
  replace h7 : ∃ᶠ w in 𝓝[≠] z, f w = f z := (h7.filter_mono nhdsWithin_le_nhds).frequently
  have h8 : IsPreconnected (ball z₀ r) := (convex_ball z₀ r).isPreconnected
  have h9 := h3.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const h8 hz1 h7
  have h10 : f z = f z₀ := (h9 (mem_ball_self hr)).symm
  exact not_eventually.mpr hz₀ (mem_of_superset (ball_mem_nhds z₀ hr) (h10 ▸ h9))

/-- A function `f : ℂ → ℂ` which is analytic at a point `z₀` is either constant in a neighborhood
of `z₀`, or behaves locally like an open function (in the sense that the image of every neighborhood
of `z₀` is a neighborhood of `f z₀`, as in `isOpenMap_iff_nhds_le`). For a function `f : E → ℂ`
the same result holds, see `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`. -/
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux (hf : AnalyticAt ℂ f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = f z₀) ∨ 𝓝 (f z₀) ≤ map f (𝓝 z₀) := by
  /- The function `f` is analytic in a neighborhood of `z₀`; by the isolated zeros principle, if `f`
    is not constant in a neighborhood of `z₀`, then it is nonzero, and therefore bounded below, on
    every small enough circle around `z₀` and then `DiffContOnCl.ball_subset_image_closedBall`
    provides an explicit ball centered at `f z₀` contained in the range of `f`. -/
  refine or_iff_not_imp_left.mpr fun h => ?_
  refine (nhds_basis_ball.le_basis_iff (nhds_basis_closedBall.map f)).mpr fun R hR => ?_
  have h1 := (hf.eventually_eq_or_eventually_ne analyticAt_const).resolve_left h
  have h2 : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ f z := (isOpen_analyticAt ℂ f).eventually_mem hf
  obtain ⟨ρ, hρ, h3, h4⟩ :
    ∃ ρ > 0, AnalyticOnNhd ℂ f (closedBall z₀ ρ) ∧ ∀ z ∈ closedBall z₀ ρ, z ≠ z₀ → f z ≠ f z₀ := by
    simpa only [setOf_and, subset_inter_iff] using
      nhds_basis_closedBall.mem_iff.mp (h2.and (eventually_nhdsWithin_iff.mp h1))
  replace h3 : DiffContOnCl ℂ f (ball z₀ ρ) :=
    ⟨h3.differentiableOn.mono ball_subset_closedBall,
      (closure_ball z₀ hρ.lt.ne.symm).symm ▸ h3.continuousOn⟩
  let r := ρ ⊓ R
  have hr : 0 < r := lt_inf_iff.mpr ⟨hρ, hR⟩
  have h5 : closedBall z₀ r ⊆ closedBall z₀ ρ := closedBall_subset_closedBall inf_le_left
  have h6 : DiffContOnCl ℂ f (ball z₀ r) := h3.mono (ball_subset_ball inf_le_left)
  have h7 : ∀ z ∈ sphere z₀ r, f z ≠ f z₀ := fun z hz =>
    h4 z (h5 (sphere_subset_closedBall hz)) (ne_of_mem_sphere hz hr.ne.symm)
  have h8 : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have h9 : ContinuousOn (fun x => ‖f x - f z₀‖) (sphere z₀ r) := continuous_norm.comp_continuousOn
    ((h6.sub_const (f z₀)).continuousOn_ball.mono sphere_subset_closedBall)
  obtain ⟨x, hx, hfx⟩ := (isCompact_sphere z₀ r).exists_isMinOn h8 h9
  refine ⟨‖f x - f z₀‖ / 2, half_pos (norm_sub_pos_iff.mpr (h7 x hx)), ?_⟩
  exact (h6.ball_subset_image_closedBall hr (fun z hz => hfx hz) (not_eventually.mp h)).trans
    (image_subset f (closedBall_subset_closedBall inf_le_right))

/-- The *open mapping theorem* for holomorphic functions, local version: is a function `g : E → ℂ`
is analytic at a point `z₀`, then either it is constant in a neighborhood of `z₀`, or it maps every
neighborhood of `z₀` to a neighborhood of `z₀`. For the particular case of a holomorphic function on
`ℂ`, see `AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`. -/
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds {z₀ : E} (hg : AnalyticAt ℂ g z₀) :
    (∀ᶠ z in 𝓝 z₀, g z = g z₀) ∨ 𝓝 (g z₀) ≤ map g (𝓝 z₀) := by
  /- The idea of the proof is to use the one-dimensional version applied to the restriction of `g`
    to lines going through `z₀` (indexed by `sphere (0 : E) 1`). If the restriction is eventually
    constant along each of these lines, then the identity theorem implies that `g` is constant on
    any ball centered at `z₀` on which it is analytic, and in particular `g` is eventually constant.
    If on the other hand there is one line along which `g` is not eventually constant, then the
    one-dimensional version of the open mapping theorem can be used to conclude. -/
  let ray : E → ℂ → E := fun z t => z₀ + t • z
  let gray : E → ℂ → ℂ := fun z => g ∘ ray z
  obtain ⟨r, hr, hgr⟩ := isOpen_iff.mp (isOpen_analyticAt ℂ g) z₀ hg
  have h1 : ∀ z ∈ sphere (0 : E) 1, AnalyticOnNhd ℂ (gray z) (ball 0 r) := by
    refine fun z hz t ht => AnalyticAt.comp ?_ ?_
    · exact hgr (by simpa [ray, norm_smul, mem_sphere_zero_iff_norm.mp hz] using ht)
    · exact analyticAt_const.add
        ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) z).analyticAt t)
  by_cases h : ∀ z ∈ sphere (0 : E) 1, ∀ᶠ t in 𝓝 0, gray z t = gray z 0
  · left
    -- If g is eventually constant along every direction, then it is eventually constant
    refine eventually_of_mem (ball_mem_nhds z₀ hr) fun z hz => ?_
    refine (eq_or_ne z z₀).casesOn (congr_arg g) fun h' => ?_
    replace h' : ‖z - z₀‖ ≠ 0 := by simpa only [Ne, norm_eq_zero, sub_eq_zero]
    let w : E := ‖z - z₀‖⁻¹ • (z - z₀)
    have h3 : ∀ t ∈ ball (0 : ℂ) r, gray w t = g z₀ := by
      have e1 : IsPreconnected (ball (0 : ℂ) r) := (convex_ball 0 r).isPreconnected
      have e2 : w ∈ sphere (0 : E) 1 := by simp [w, norm_smul, inv_mul_cancel₀ h']
      specialize h1 w e2
      apply h1.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const e1 (mem_ball_self hr)
      simpa [ray, gray] using h w e2
    have h4 : ‖z - z₀‖ < r := by simpa [dist_eq_norm] using mem_ball.mp hz
    replace h4 : ↑‖z - z₀‖ ∈ ball (0 : ℂ) r := by simpa
    simpa only [ray, gray, w, smul_smul, mul_inv_cancel₀ h', one_smul, add_sub_cancel,
      Function.comp_apply, coe_smul] using h3 (↑‖z - z₀‖) h4
  · right
    -- Otherwise, it is open along at least one direction and that implies the result
    push_neg at h
    obtain ⟨z, hz, hrz⟩ := h
    specialize h1 z hz 0 (mem_ball_self hr)
    have h7 := h1.eventually_constant_or_nhds_le_map_nhds_aux.resolve_left hrz
    rw [show gray z 0 = g z₀ by simp [gray, ray], ← map_compose] at h7
    refine h7.trans (map_mono ?_)
    have h10 : Continuous fun t : ℂ => z₀ + t • z :=
      continuous_const.add (continuous_id'.smul continuous_const)
    simpa using h10.tendsto 0

/-- The *open mapping theorem* for holomorphic functions, global version: if a function `g : E → ℂ`
is analytic on a connected set `U`, then either it is constant on `U`, or it is open on `U` (in the
sense that it maps any open set contained in `U` to an open set in `ℂ`). -/
theorem AnalyticOnNhd.is_constant_or_isOpen (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) :
    (∃ w, ∀ z ∈ U, g z = w) ∨ ∀ s ⊆ U, IsOpen s → IsOpen (g '' s) := by
  by_cases h : ∃ z₀ ∈ U, ∀ᶠ z in 𝓝 z₀, g z = g z₀
  · obtain ⟨z₀, hz₀, h⟩ := h
    exact Or.inl ⟨g z₀, hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz₀ h⟩
  · push_neg at h
    refine Or.inr fun s hs1 hs2 => isOpen_iff_mem_nhds.mpr ?_
    rintro z ⟨w, hw1, rfl⟩
    exact (hg w (hs1 hw1)).eventually_constant_or_nhds_le_map_nhds.resolve_left (h w (hs1 hw1))
        (image_mem_map (hs2.mem_nhds hw1))
