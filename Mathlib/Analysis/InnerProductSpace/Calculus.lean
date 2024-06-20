/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.NormedSpace.HomeomorphBall

#align_import analysis.inner_product_space.calculus from "leanprover-community/mathlib"@"f9dd3204df14a0749cd456fac1e6849dfe7d2b88"

/-!
# Calculus in inner product spaces

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `NormedSpace ℝ E`
instance. Though we can deduce this structure from `InnerProductSpace 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[NormedSpace ℝ E]`.

We also prove that functions to a `EuclideanSpace` are (higher) differentiable if and only if
their components are. This follows from the corresponding fact for finite product of normed spaces,
and from the equivalence of norms in finite dimensions.

## TODO

The last part of the file should be generalized to `PiLp`.
-/

noncomputable section

open RCLike Real Filter

open scoped Classical Topology

section DerivInner

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

variable (𝕜) [NormedSpace ℝ E]

/-- Derivative of the inner product. -/
def fderivInnerCLM (p : E × E) : E × E →L[ℝ] 𝕜 :=
  isBoundedBilinearMap_inner.deriv p
#align fderiv_inner_clm fderivInnerCLM

@[simp]
theorem fderivInnerCLM_apply (p x : E × E) : fderivInnerCLM 𝕜 p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫ :=
  rfl
#align fderiv_inner_clm_apply fderivInnerCLM_apply

variable {𝕜} -- Porting note: Lean 3 magically switches back to `{𝕜}` here

theorem contDiff_inner {n} : ContDiff ℝ n fun p : E × E => ⟪p.1, p.2⟫ :=
  isBoundedBilinearMap_inner.contDiff
#align cont_diff_inner contDiff_inner

theorem contDiffAt_inner {p : E × E} {n} : ContDiffAt ℝ n (fun p : E × E => ⟪p.1, p.2⟫) p :=
  ContDiff.contDiffAt contDiff_inner
#align cont_diff_at_inner contDiffAt_inner

theorem differentiable_inner : Differentiable ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  isBoundedBilinearMap_inner.differentiableAt
#align differentiable_inner differentiable_inner

variable (𝕜)
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : G → E} {f' g' : G →L[ℝ] E}
  {s : Set G} {x : G} {n : ℕ∞}

theorem ContDiffWithinAt.inner (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x) :
    ContDiffWithinAt ℝ n (fun x => ⟪f x, g x⟫) s x :=
  contDiffAt_inner.comp_contDiffWithinAt x (hf.prod hg)
#align cont_diff_within_at.inner ContDiffWithinAt.inner

nonrec theorem ContDiffAt.inner (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => ⟪f x, g x⟫) x :=
  hf.inner 𝕜 hg
#align cont_diff_at.inner ContDiffAt.inner

theorem ContDiffOn.inner (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ n (fun x => ⟪f x, g x⟫) s := fun x hx => (hf x hx).inner 𝕜 (hg x hx)
#align cont_diff_on.inner ContDiffOn.inner

theorem ContDiff.inner (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun x => ⟪f x, g x⟫ :=
  contDiff_inner.comp (hf.prod hg)
#align cont_diff.inner ContDiff.inner

theorem HasFDerivWithinAt.inner (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') s
      x :=
  (isBoundedBilinearMap_inner.hasFDerivAt (f x, g x)).comp_hasFDerivWithinAt x (hf.prod hg)
#align has_fderiv_within_at.inner HasFDerivWithinAt.inner

theorem HasStrictFDerivAt.inner (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') x :=
  (isBoundedBilinearMap_inner.hasStrictFDerivAt (f x, g x)).comp x (hf.prod hg)
#align has_strict_fderiv_at.inner HasStrictFDerivAt.inner

theorem HasFDerivAt.inner (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') x :=
  (isBoundedBilinearMap_inner.hasFDerivAt (f x, g x)).comp x (hf.prod hg)
#align has_fderiv_at.inner HasFDerivAt.inner

theorem HasDerivWithinAt.inner {f g : ℝ → E} {f' g' : E} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) s x := by
  simpa using (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).hasDerivWithinAt
#align has_deriv_within_at.inner HasDerivWithinAt.inner

theorem HasDerivAt.inner {f g : ℝ → E} {f' g' : E} {x : ℝ} :
    HasDerivAt f f' x → HasDerivAt g g' x →
      HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x := by
  simpa only [← hasDerivWithinAt_univ] using HasDerivWithinAt.inner 𝕜
#align has_deriv_at.inner HasDerivAt.inner

theorem DifferentiableWithinAt.inner (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) : DifferentiableWithinAt ℝ (fun x => ⟪f x, g x⟫) s x :=
  ((differentiable_inner _).hasFDerivAt.comp_hasFDerivWithinAt x
      (hf.prod hg).hasFDerivWithinAt).differentiableWithinAt
#align differentiable_within_at.inner DifferentiableWithinAt.inner

theorem DifferentiableAt.inner (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun x => ⟪f x, g x⟫) x :=
  (differentiable_inner _).comp x (hf.prod hg)
#align differentiable_at.inner DifferentiableAt.inner

theorem DifferentiableOn.inner (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s) :
    DifferentiableOn ℝ (fun x => ⟪f x, g x⟫) s := fun x hx => (hf x hx).inner 𝕜 (hg x hx)
#align differentiable_on.inner DifferentiableOn.inner

theorem Differentiable.inner (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ fun x => ⟪f x, g x⟫ := fun x => (hf x).inner 𝕜 (hg x)
#align differentiable.inner Differentiable.inner

theorem fderiv_inner_apply (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (y : G) :
    fderiv ℝ (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫ + ⟪fderiv ℝ f x y, g x⟫ := by
  rw [(hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).fderiv]; rfl
#align fderiv_inner_apply fderiv_inner_apply

theorem deriv_inner_apply {f g : ℝ → E} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun t => ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
  (hf.hasDerivAt.inner 𝕜 hg.hasDerivAt).deriv
#align deriv_inner_apply deriv_inner_apply

theorem contDiff_norm_sq : ContDiff ℝ n fun x : E => ‖x‖ ^ 2 := by
  convert (reCLM : 𝕜 →L[ℝ] ℝ).contDiff.comp ((contDiff_id (E := E)).inner 𝕜 (contDiff_id (E := E)))
  exact (inner_self_eq_norm_sq _).symm
#align cont_diff_norm_sq contDiff_norm_sq

theorem ContDiff.norm_sq (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => ‖f x‖ ^ 2 :=
  (contDiff_norm_sq 𝕜).comp hf
#align cont_diff.norm_sq ContDiff.norm_sq

theorem ContDiffWithinAt.norm_sq (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun y => ‖f y‖ ^ 2) s x :=
  (contDiff_norm_sq 𝕜).contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.norm_sq ContDiffWithinAt.norm_sq

nonrec theorem ContDiffAt.norm_sq (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (‖f ·‖ ^ 2) x :=
  hf.norm_sq 𝕜
#align cont_diff_at.norm_sq ContDiffAt.norm_sq

theorem contDiffAt_norm {x : E} (hx : x ≠ 0) : ContDiffAt ℝ n norm x := by
  have : ‖id x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.2 hx).ne'
  simpa only [id, sqrt_sq, norm_nonneg] using (contDiffAt_id.norm_sq 𝕜).sqrt this
#align cont_diff_at_norm contDiffAt_norm

theorem ContDiffAt.norm (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) :
    ContDiffAt ℝ n (fun y => ‖f y‖) x :=
  (contDiffAt_norm 𝕜 h0).comp x hf
#align cont_diff_at.norm ContDiffAt.norm

theorem ContDiffAt.dist (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (hne : f x ≠ g x) :
    ContDiffAt ℝ n (fun y => dist (f y) (g y)) x := by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)
#align cont_diff_at.dist ContDiffAt.dist

theorem ContDiffWithinAt.norm (hf : ContDiffWithinAt ℝ n f s x) (h0 : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y => ‖f y‖) s x :=
  (contDiffAt_norm 𝕜 h0).comp_contDiffWithinAt x hf
#align cont_diff_within_at.norm ContDiffWithinAt.norm

theorem ContDiffWithinAt.dist (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (hne : f x ≠ g x) : ContDiffWithinAt ℝ n (fun y => dist (f y) (g y)) s x := by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)
#align cont_diff_within_at.dist ContDiffWithinAt.dist

theorem ContDiffOn.norm_sq (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun y => ‖f y‖ ^ 2) s :=
  fun x hx => (hf x hx).norm_sq 𝕜
#align cont_diff_on.norm_sq ContDiffOn.norm_sq

theorem ContDiffOn.norm (hf : ContDiffOn ℝ n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm 𝕜 (h0 x hx)
#align cont_diff_on.norm ContDiffOn.norm

theorem ContDiffOn.dist (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hne : ∀ x ∈ s, f x ≠ g x) : ContDiffOn ℝ n (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)
#align cont_diff_on.dist ContDiffOn.dist

theorem ContDiff.norm (hf : ContDiff ℝ n f) (h0 : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => ‖f y‖ :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.norm 𝕜 (h0 x)
#align cont_diff.norm ContDiff.norm

theorem ContDiff.dist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hne : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun y => dist (f y) (g y) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.dist 𝕜 hg.contDiffAt (hne x)
#align cont_diff.dist ContDiff.dist

-- Porting note: use `2 •` instead of `bit0`
theorem hasStrictFDerivAt_norm_sq (x : F) :
    HasStrictFDerivAt (fun x => ‖x‖ ^ 2) (2 • (innerSL ℝ x)) x := by
  simp only [sq, ← @inner_self_eq_norm_mul_norm ℝ]
  convert (hasStrictFDerivAt_id x).inner ℝ (hasStrictFDerivAt_id x)
  ext y
  simp [two_smul, real_inner_comm]
#align has_strict_fderiv_at_norm_sq hasStrictFDerivAt_norm_sqₓ

theorem HasFDerivAt.norm_sq {f : G → F} {f' : G →L[ℝ] F} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (‖f ·‖ ^ 2) (2 • (innerSL ℝ (f x)).comp f') x :=
  (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp x hf

theorem HasDerivAt.norm_sq {f : ℝ → F} {f' : F} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (‖f ·‖ ^ 2) (2 * Inner.inner (f x) f') x := by
  simpa using hf.hasFDerivAt.norm_sq.hasDerivAt

theorem HasFDerivWithinAt.norm_sq {f : G → F} {f' : G →L[ℝ] F} (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (‖f ·‖ ^ 2) (2 • (innerSL ℝ (f x)).comp f') s x :=
  (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp_hasFDerivWithinAt x hf

theorem HasDerivWithinAt.norm_sq {f : ℝ → F} {f' : F} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (‖f ·‖ ^ 2) (2 * Inner.inner (f x) f') s x := by
  simpa using hf.hasFDerivWithinAt.norm_sq.hasDerivWithinAt

theorem DifferentiableAt.norm_sq (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => ‖f y‖ ^ 2) x :=
  ((contDiffAt_id.norm_sq 𝕜).differentiableAt le_rfl).comp x hf
#align differentiable_at.norm_sq DifferentiableAt.norm_sq

theorem DifferentiableAt.norm (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => ‖f y‖) x :=
  ((contDiffAt_norm 𝕜 h0).differentiableAt le_rfl).comp x hf
#align differentiable_at.norm DifferentiableAt.norm

theorem DifferentiableAt.dist (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hne : f x ≠ g x) : DifferentiableAt ℝ (fun y => dist (f y) (g y)) x := by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)
#align differentiable_at.dist DifferentiableAt.dist

theorem Differentiable.norm_sq (hf : Differentiable ℝ f) : Differentiable ℝ fun y => ‖f y‖ ^ 2 :=
  fun x => (hf x).norm_sq 𝕜
#align differentiable.norm_sq Differentiable.norm_sq

theorem Differentiable.norm (hf : Differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun y => ‖f y‖ := fun x => (hf x).norm 𝕜 (h0 x)
#align differentiable.norm Differentiable.norm

theorem Differentiable.dist (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hne : ∀ x, f x ≠ g x) : Differentiable ℝ fun y => dist (f y) (g y) := fun x =>
  (hf x).dist 𝕜 (hg x) (hne x)
#align differentiable.dist Differentiable.dist

theorem DifferentiableWithinAt.norm_sq (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun y => ‖f y‖ ^ 2) s x :=
  ((contDiffAt_id.norm_sq 𝕜).differentiableAt le_rfl).comp_differentiableWithinAt x hf
#align differentiable_within_at.norm_sq DifferentiableWithinAt.norm_sq

theorem DifferentiableWithinAt.norm (hf : DifferentiableWithinAt ℝ f s x) (h0 : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun y => ‖f y‖) s x :=
  ((contDiffAt_id.norm 𝕜 h0).differentiableAt le_rfl).comp_differentiableWithinAt x hf
#align differentiable_within_at.norm DifferentiableWithinAt.norm

theorem DifferentiableWithinAt.dist (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) (hne : f x ≠ g x) :
    DifferentiableWithinAt ℝ (fun y => dist (f y) (g y)) s x := by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)
#align differentiable_within_at.dist DifferentiableWithinAt.dist

theorem DifferentiableOn.norm_sq (hf : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun y => ‖f y‖ ^ 2) s := fun x hx => (hf x hx).norm_sq 𝕜
#align differentiable_on.norm_sq DifferentiableOn.norm_sq

theorem DifferentiableOn.norm (hf : DifferentiableOn ℝ f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm 𝕜 (h0 x hx)
#align differentiable_on.norm DifferentiableOn.norm

theorem DifferentiableOn.dist (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
    (hne : ∀ x ∈ s, f x ≠ g x) : DifferentiableOn ℝ (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)
#align differentiable_on.dist DifferentiableOn.dist

end DerivInner

section PiLike

open ContinuousLinearMap

variable {𝕜 ι H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H] [Fintype ι]
  {f : H → EuclideanSpace 𝕜 ι} {f' : H →L[𝕜] EuclideanSpace 𝕜 ι} {t : Set H} {y : H}

theorem differentiableWithinAt_euclidean :
    DifferentiableWithinAt 𝕜 f t y ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiableWithinAt_iff, differentiableWithinAt_pi]
  rfl
#align differentiable_within_at_euclidean differentiableWithinAt_euclidean

theorem differentiableAt_euclidean :
    DifferentiableAt 𝕜 f y ↔ ∀ i, DifferentiableAt 𝕜 (fun x => f x i) y := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiableAt_iff, differentiableAt_pi]
  rfl
#align differentiable_at_euclidean differentiableAt_euclidean

theorem differentiableOn_euclidean :
    DifferentiableOn 𝕜 f t ↔ ∀ i, DifferentiableOn 𝕜 (fun x => f x i) t := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiableOn_iff, differentiableOn_pi]
  rfl
#align differentiable_on_euclidean differentiableOn_euclidean

theorem differentiable_euclidean : Differentiable 𝕜 f ↔ ∀ i, Differentiable 𝕜 fun x => f x i := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiable_iff, differentiable_pi]
  rfl
#align differentiable_euclidean differentiable_euclidean

theorem hasStrictFDerivAt_euclidean :
    HasStrictFDerivAt f f' y ↔
      ∀ i, HasStrictFDerivAt (fun x => f x i) (EuclideanSpace.proj i ∘L f') y := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_hasStrictFDerivAt_iff, hasStrictFDerivAt_pi']
  rfl
#align has_strict_fderiv_at_euclidean hasStrictFDerivAt_euclidean

theorem hasFDerivWithinAt_euclidean :
    HasFDerivWithinAt f f' t y ↔
      ∀ i, HasFDerivWithinAt (fun x => f x i) (EuclideanSpace.proj i ∘L f') t y := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_hasFDerivWithinAt_iff, hasFDerivWithinAt_pi']
  rfl
#align has_fderiv_within_at_euclidean hasFDerivWithinAt_euclidean

theorem contDiffWithinAt_euclidean {n : ℕ∞} :
    ContDiffWithinAt 𝕜 n f t y ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_contDiffWithinAt_iff, contDiffWithinAt_pi]
  rfl
#align cont_diff_within_at_euclidean contDiffWithinAt_euclidean

theorem contDiffAt_euclidean {n : ℕ∞} :
    ContDiffAt 𝕜 n f y ↔ ∀ i, ContDiffAt 𝕜 n (fun x => f x i) y := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_contDiffAt_iff, contDiffAt_pi]
  rfl
#align cont_diff_at_euclidean contDiffAt_euclidean

theorem contDiffOn_euclidean {n : ℕ∞} :
    ContDiffOn 𝕜 n f t ↔ ∀ i, ContDiffOn 𝕜 n (fun x => f x i) t := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_contDiffOn_iff, contDiffOn_pi]
  rfl
#align cont_diff_on_euclidean contDiffOn_euclidean

theorem contDiff_euclidean {n : ℕ∞} : ContDiff 𝕜 n f ↔ ∀ i, ContDiff 𝕜 n fun x => f x i := by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_contDiff_iff, contDiff_pi]
  rfl
#align cont_diff_euclidean contDiff_euclidean

end PiLike

section DiffeomorphUnitBall

open Metric hiding mem_nhds_iff

variable {n : ℕ∞} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem PartialHomeomorph.contDiff_univUnitBall : ContDiff ℝ n (univUnitBall : E → E) := by
  suffices ContDiff ℝ n fun x : E => (√(1 + ‖x‖ ^ 2 : ℝ))⁻¹ from this.smul contDiff_id
  have h : ∀ x : E, (0 : ℝ) < (1 : ℝ) + ‖x‖ ^ 2 := fun x => by positivity
  refine ContDiff.inv ?_ fun x => Real.sqrt_ne_zero'.mpr (h x)
  exact (contDiff_const.add <| contDiff_norm_sq ℝ).sqrt fun x => (h x).ne'

theorem PartialHomeomorph.contDiffOn_univUnitBall_symm :
    ContDiffOn ℝ n univUnitBall.symm (ball (0 : E) 1) := fun y hy ↦ by
  apply ContDiffAt.contDiffWithinAt
  suffices ContDiffAt ℝ n (fun y : E => (√(1 - ‖y‖ ^ 2 : ℝ))⁻¹) y from this.smul contDiffAt_id
  have h : (0 : ℝ) < (1 : ℝ) - ‖(y : E)‖ ^ 2 := by
    rwa [mem_ball_zero_iff, ← _root_.abs_one, ← abs_norm, ← sq_lt_sq, one_pow, ← sub_pos] at hy
  refine ContDiffAt.inv ?_ (Real.sqrt_ne_zero'.mpr h)
  refine (contDiffAt_sqrt h.ne').comp y ?_
  exact contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt

theorem Homeomorph.contDiff_unitBall : ContDiff ℝ n fun x : E => (unitBall x : E) :=
  PartialHomeomorph.contDiff_univUnitBall
#align cont_diff_homeomorph_unit_ball Homeomorph.contDiff_unitBall

@[deprecated PartialHomeomorph.contDiffOn_univUnitBall_symm (since := "2023-07-26")]
theorem Homeomorph.contDiffOn_unitBall_symm {f : E → E}
    (h : ∀ (y) (hy : y ∈ ball (0 : E) 1), f y = Homeomorph.unitBall.symm ⟨y, hy⟩) :
    ContDiffOn ℝ n f <| ball 0 1 :=
  PartialHomeomorph.contDiffOn_univUnitBall_symm.congr h
#align cont_diff_on_homeomorph_unit_ball_symm Homeomorph.contDiffOn_unitBall_symm

namespace PartialHomeomorph

variable {c : E} {r : ℝ}

theorem contDiff_unitBallBall (hr : 0 < r) : ContDiff ℝ n (unitBallBall c r hr) :=
  (contDiff_id.const_smul _).add contDiff_const

theorem contDiff_unitBallBall_symm (hr : 0 < r) : ContDiff ℝ n (unitBallBall c r hr).symm :=
  (contDiff_id.sub contDiff_const).const_smul _

theorem contDiff_univBall : ContDiff ℝ n (univBall c r) := by
  unfold univBall; split_ifs with h
  · exact (contDiff_unitBallBall h).comp contDiff_univUnitBall
  · exact contDiff_id.add contDiff_const

theorem contDiffOn_univBall_symm :
    ContDiffOn ℝ n (univBall c r).symm (ball c r) := by
  unfold univBall; split_ifs with h
  · refine contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm h).contDiffOn ?_
    rw [← unitBallBall_source c r h, ← unitBallBall_target c r h]
    apply PartialHomeomorph.symm_mapsTo
  · exact contDiffOn_id.sub contDiffOn_const

end PartialHomeomorph

end DiffeomorphUnitBall
