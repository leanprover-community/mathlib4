/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `Complex.norm_deriv_le_div_of_mapsTo_ball`. Let `f : ℂ → E` be a complex analytic function
  on an open disk with center `c` and a positive radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`.

* `Complex.dist_le_div_mul_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c` and radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`.

* `Complex.norm_deriv_le_one_of_mapsTo_ball`. If `f : ℂ → E` is complex analytic
  on an open disk with center `c` and a positive radius `R₁`,
  and it sends this disk to a closed ball with center `f c` and radius the same radius,
  then the norm of the derivative of `f` at the center of this disk is at most `1`.

* `Complex.dist_le_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c`.
  If `f` sends this ball to a closed ball with center `f c` and the same radius,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.

* `Complex.norm_le_norm_of_mapsTo_ball`:
  Let `f : E → F` be a complex analytic on an open ball with center at the origin.
  If `f` sends this ball to the closed ball with center `0` of the same radius and `f 0 = 0`,
  then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`.

## Implementation notes

Traditionally, the Schwarz lemma is formulated for maps `f : ℂ → ℂ`.
We generalize all versions of the lemma to the case of maps to any normed space.
For the versions that don't use `deriv` or `dslope`,
we state it for maps between any two normed spaces.

## TODO

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/

open Metric Set Function Filter TopologicalSpace

open scoped Topology ComplexConjugate

namespace Complex

/-- An auxiliary lemma for `Complex.norm_dslope_le_div_of_mapsTo_ball`. -/
theorem schwarz_aux {f : ℂ → ℂ} {c z : ℂ} {R₁ R₂ : ℝ} (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    ‖dslope f c z‖ ≤ R₂ / R₁ := by
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  suffices ∀ᶠ r in 𝓝[<] R₁, ‖dslope f c z‖ ≤ R₂ / r by
    refine ge_of_tendsto ?_ this
    exact (tendsto_const_nhds.div tendsto_id hR₁.ne').mono_left nhdsWithin_le_nhds
  rw [mem_ball] at hz
  filter_upwards [Ioo_mem_nhdsLT hz] with r hr
  have hr₀ : 0 < r := dist_nonneg.trans_lt hr.1
  replace hd : DiffContOnCl ℂ (dslope f c) (ball c r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hr₀.ne']
    exact ((differentiableOn_dslope <| ball_mem_nhds _ hR₁).mpr hd).mono
      (closedBall_subset_ball hr.2)
  refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ ?_
  · rw [frontier_ball c hr₀.ne']
    intro z hz
    have hz' : z ≠ c := ne_of_mem_sphere hz hr₀.ne'
    rw [dslope_of_ne _ hz', slope_def_module, norm_smul, norm_inv, mem_sphere_iff_norm.1 hz, ←
      div_eq_inv_mul, div_le_div_iff_of_pos_right hr₀, ← mem_closedBall_iff_norm]
    exact h_maps <| mem_ball.2 <| by rw [mem_sphere.1 hz]; exact hr.2
  · rw [closure_ball c hr₀.ne', mem_closedBall]
    exact hr.1.le

public section

section DimOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {R R₁ R₂ : ℝ} {f : ℂ → E}
  {c z z₀ : ℂ}

/-- Two cases of the **Schwarz Lemma** (derivative and distance), merged together.

If `f : ℂ → E` is a complex analytic function on an open ball `ball c R₁`
hat sends it to a closed ball `closedBall (f c) R₂`, then the norm of `dslope f c z`,
which is defined as `(z - c)⁻¹ • (f z - f c)` for `z ≠ c` and as `deriv f c` for `z = c`,
is not greater than the ratio `R₂ / R₁`.
-/
theorem norm_dslope_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    ‖dslope f c z‖ ≤ R₂ / R₁ := by
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  have hR₂ : 0 ≤ R₂ := nonempty_closedBall.mp ⟨f z, h_maps hz⟩
  rcases eq_or_ne (dslope f c z) 0 with hc | hc
  · rw [hc, norm_zero]; exact div_nonneg hR₂ hR₁.le
  rcases exists_dual_vector ℂ _ hc with ⟨g, hg, hgf⟩
  have hg' : ‖g‖₊ = 1 := NNReal.eq hg
  calc
    ‖dslope f c z‖ = ‖dslope (g ∘ f) c z‖ := by
      rw [g.dslope_comp, hgf, RCLike.norm_ofReal, abs_norm]
      exact fun _ => hd.differentiableAt (ball_mem_nhds _ hR₁)
    _ ≤ R₂ / R₁ := by
      refine schwarz_aux (g.differentiable.comp_differentiableOn hd) (MapsTo.comp ?_ h_maps) hz
      simpa only [hg', NNReal.coe_one, one_mul] using g.lipschitz.mapsTo_closedBall (f c) R₂

/-- Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_mapsTo_ball`,
if `‖dslope f c z₀‖ = R₂ / R₁` holds at a point in the ball
then the map `f` is affine with slope `dslope f c z₀`.

Note that this lemma requires the codomain to be a strictly convex space.
Indeed, for `E = ℂ × ℂ` there is a counterexample:
the map `f := fun z ↦ (z, z ^ 2)` sends `ball 0 1` to `closedBall 0 1`,
`‖dslope f 0 0‖ = ‖deriv f 0‖ = ‖(1, 0)‖ = 1`, but the map is not an affine map.
-/
theorem affine_of_mapsTo_ball_of_norm_dslope_eq_div [StrictConvexSpace ℝ E]
    (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (h_z₀ : z₀ ∈ ball c R₁) (h_eq : ‖dslope f c z₀‖ = R₂ / R₁) :
    Set.EqOn f (fun z => f c + (z - c) • dslope f c z₀) (ball c R₁) := by
  set e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  set g := dslope (e ∘ f) c
  rintro z hz
  have h_R₁ : 0 < R₁ := nonempty_ball.mp ⟨_, h_z₀⟩
  have hg' : g = e ∘ dslope f c := by
    ext w
    simp only [g]
    rw [e.dslope_comp, Function.comp_apply]
    rintro rfl
    exact hd.differentiableAt <| ball_mem_nhds _ h_R₁
  have g_le_div : ∀ z ∈ ball c R₁, ‖g z‖ ≤ R₂ / R₁ := fun z hz =>
    norm_dslope_le_div_of_mapsTo_ball (e.differentiable.comp_differentiableOn hd)
      (fun w hw ↦ by simpa [e] using h_maps hw) hz
  have g_max : IsMaxOn (norm ∘ g) (ball c R₁) z₀ :=
    isMaxOn_iff.mpr fun z hz => by simpa [h_eq, hg', e] using g_le_div z hz
  have g_diff : DifferentiableOn ℂ g (ball c R₁) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self h_R₁))).mpr
      (e.differentiable.comp_differentiableOn hd)
  have heq : ‖dslope f c z‖ = ‖dslope f c z₀‖ := by
    simpa [hg', e] using norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball c R₁).isPreconnected
      isOpen_ball g_diff h_z₀ g_max hz
  have heq_add : ‖dslope f c z + dslope f c z₀‖ = ‖dslope f c z₀ + dslope f c z₀‖ := by
    simpa [hg', e, ← UniformSpace.Completion.coe_add]
      using norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball c R₁).isPreconnected
        isOpen_ball (g_diff.add_const (g z₀)) h_z₀ g_max.norm_add_self hz
  have : dslope f c z = dslope f c z₀ := eq_of_norm_eq_of_norm_add_eq heq <| by
    simp only [heq, SameRay.rfl.norm_add, heq_add]
  simp [← this]

@[deprecated (since := "2026-01-03")]
alias affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div :=
  affine_of_mapsTo_ball_of_norm_dslope_eq_div

/-- Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_mapsTo_ball`,
if there exists a point `z₀` in the ball such that `‖dslope f c z₀‖ = R₂ / R₁`,
then the map `f` is affine with the absolute value of the slope equal to `R₂ / R₁`.

This is an existence version of `affine_of_mapsTo_ball_of_norm_dslope_eq_div` above.

TODO: once the deprecated alias `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div` is gone,
rename this theorem to `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div`.
-/
theorem affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
    [StrictConvexSpace ℝ E] (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (h_z₀ : ∃ z₀ ∈ ball c R₁, ‖dslope f c z₀‖ = R₂ / R₁) :
    ∃ C : E, ‖C‖ = R₂ / R₁ ∧ Set.EqOn f (fun z => f c + (z - c) • C) (ball c R₁) :=
  let ⟨z₀, h_z₀, h_eq⟩ := h_z₀
  ⟨dslope f c z₀, h_eq, affine_of_mapsTo_ball_of_norm_dslope_eq_div hd h_maps h_z₀ h_eq⟩

/-- The **Schwarz Lemma**: if `f : ℂ → E` is complex analytic
on an open disk with center `c` and a positive radius `R₁`,
and it sends this disk to a closed ball with center `f c` and radius `R₂`,
then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`. -/
theorem norm_deriv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖deriv f c‖ ≤ R₂ / R₁ := by
  simpa only [dslope_same] using norm_dslope_le_div_of_mapsTo_ball hd h_maps (mem_ball_self h₀)

/-- The **Schwarz Lemma**: if `f : ℂ → E` is complex analytic
on an open disk with center `c` and a positive radius `R₁`,
and it sends this disk to a closed ball with center `f c` and radius the same radius,
then the norm of the derivative of `f` at the center of this disk is at most `1`.
-/
theorem norm_deriv_le_one_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (h₀ : 0 < R) : ‖deriv f c‖ ≤ 1 :=
  (norm_deriv_le_div_of_mapsTo_ball hd h_maps h₀).trans_eq (div_self h₀.ne')

end DimOne

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {R R₁ R₂ : ℝ} {f : E → F} {c z : E}

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and radius `R₁`.
If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`.
-/
theorem dist_le_div_mul_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    dist (f z) (f c) ≤ R₂ / R₁ * dist z c := by
  rcases eq_or_ne z c with (rfl | hne)
  · simp only [dist_self, mul_zero, le_rfl]
  set g : ℂ → F := f ∘ AffineMap.lineMap c z
  have hmaps : MapsTo (AffineMap.lineMap c z) (ball (0 : ℂ) (R₁ / dist z c)) (ball c R₁) := by
    intro w hw
    simpa [lt_div_iff₀, hne, dist_comm c] using hw
  have hdg : DifferentiableOn ℂ g (ball 0 (R₁ / dist z c)) :=
    hd.comp (by rw [funext (AffineMap.lineMap_apply_module _ _)]; fun_prop) hmaps
  calc
    dist (f z) (f c) = dist (g 1) (g 0) := by simp [g]
    _ ≤ R₂ / (R₁ / dist z c) * dist (1 : ℂ) 0 := by
      simpa [dslope_of_ne, slope_def_module, dist_eq_norm_sub]
        using norm_dslope_le_div_of_mapsTo_ball hdg (by simpa [g] using h_maps.comp hmaps)
          (z := 1) (by simpa [lt_div_iff₀, hne])
    _ = _ := by simp [field]

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and positive radius `R₁`.
If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
then the norm of the Fréchet derivative of `f` at `c` is at most `R₂ / R₁`.
-/
theorem norm_fderiv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖fderiv ℂ f c‖ ≤ R₂ / R₁ := by
  have : 0 ≤ R₂ := nonempty_closedBall.mp <| h_maps.nonempty <| nonempty_ball.mpr h₀
  refine norm_fderiv_le_of_lip' _ (by positivity) ?_
  filter_upwards [ball_mem_nhds _ h₀] with z hz
  simpa [dist_eq_norm_sub] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c`.
If `f` sends this ball to a closed ball with center `f c` and the same radius,
then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.
-/
theorem dist_le_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hz : z ∈ ball c R) :
    dist (f z) (f c) ≤ dist z c := by
  simpa [(nonempty_ball.1 ⟨z, hz⟩).ne'] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

@[deprecated (since := "2026-01-03")]
alias dist_le_dist_of_mapsTo_ball_self := dist_le_dist_of_mapsTo_ball

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and a positive radius.
If `f` sends this ball to a closed ball with center `f c` and the same radius,
then the norm of the Fréchet derivative of `f` at `c` is at most one.
-/
theorem norm_fderiv_le_one_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hR : 0 < R) :
    ‖fderiv ℂ f c‖ ≤ 1 := by
  simpa [hR.ne'] using norm_fderiv_le_div_of_mapsTo_ball hd h_maps hR

/-- The **Schwarz Lemma**.
Let `f : E → F` be a complex analytic on an open ball with center at the origin.
If `f` sends this ball to the closed ball with center `0` of the same radius and `f 0 = 0`,
then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`. -/
theorem norm_le_norm_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball 0 R))
    (h_maps : MapsTo f (ball 0 R) (closedBall 0 R)) (h₀ : f 0 = 0) (hz : ‖z‖ < R) :
    ‖f z‖ ≤ ‖z‖ := by
  simpa [h₀] using dist_le_dist_of_mapsTo_ball hd (by rwa [h₀]) (mem_ball_zero_iff.mpr hz)

@[deprecated (since := "2026-01-03")]
alias norm_le_norm_of_mapsTo_ball_self := norm_le_norm_of_mapsTo_ball

end -- public section

end Complex
