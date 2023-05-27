/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.Ray

/-!
# Scale a vector to a given norm

For a nonnegative real number `r` and a vector `x` in a real (semi)normed space, we define
`scaleToNorm r x` to be the vector `(r / ‖x‖) • x`.

If `‖x‖ ≠ 0`, then this vector has norm `r` and belongs to the same ray as `x`.
If `‖x‖ = 0`, then this is the zero vector.

## Implementation notes

Since most facts are true only for nonnegative `r`, we choose to require this argument to be a
bundled nonnegative real number `NNReal` a.k.a. `ℝ≥0`.
-/

open Set Function Metric Topology NNReal Filter

variable
  {E : Type _} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {r : ℝ≥0}

/-- Scale a vector to a prescribed norm.

If `‖x‖ ≠ 0`, then this vector has norm `r` and belongs to the same ray as `x`.
If `‖x‖ = 0`, then this is the zero vector. -/
noncomputable def scaleToNorm (r : ℝ≥0) (x : E) : E := (↑r / ‖x‖) • x

/-!
### `scaleToNorm` and zeros
-/

lemma scaleToNorm_zero_left_apply (x : E) : scaleToNorm 0 x = 0 := by
  simp [scaleToNorm]

@[simp] lemma scaleToNorm_zero_left : (scaleToNorm 0 : E → E) = 0 :=
  funext scaleToNorm_zero_left_apply

lemma scaleToNorm_of_norm_zero (r : ℝ≥0) {x : E} (hx : ‖x‖ = 0) : scaleToNorm r x = 0 := by
  simp [scaleToNorm, hx]

@[simp] lemma scaleToNorm_zero_right (r : ℝ≥0) : scaleToNorm r (0 : E) = 0 :=
  scaleToNorm_of_norm_zero r norm_zero

/-!
### Norm of `scaleToNorm r x`

In this section we show that `‖scaleToNorm r x‖ ≤ r` for all `r`, `x` (see `norm_scaleToNorm_le`),
and in most cases this inequality becomes an equality (see `norm_scaleToNorm_eq'` and
`norm_scaleToNorm_eq`).
-/

lemma norm_scaleToNorm_eq' (r : ℝ≥0) {x : E} (hx : ‖x‖ ≠ 0) :
    ‖scaleToNorm r x‖ = r := by
  rw [scaleToNorm, norm_smul, norm_div, norm_norm, Real.norm_of_nonneg r.coe_nonneg,
    div_mul_cancel _ hx]

lemma norm_scaleToNorm_eq (r : ℝ≥0) {x : F} (hx : x ≠ 0) :
    ‖scaleToNorm r x‖ = r :=
  norm_scaleToNorm_eq' r (norm_ne_zero_iff.2 hx)

lemma scaleToNorm_mem_sphere' (r : ℝ≥0) {x : E} (hx : ‖x‖ ≠ 0) :
    scaleToNorm r x ∈ sphere (0 : E) r :=
  mem_sphere_zero_iff_norm.2 <| norm_scaleToNorm_eq' r hx

lemma scaleToNorm_mem_sphere (r : ℝ≥0) {x : F} (hx : x ≠ 0) :
    scaleToNorm r x ∈ sphere (0 : F) r :=
  mem_sphere_zero_iff_norm.2 <| norm_scaleToNorm_eq r hx

lemma norm_scaleToNorm_le (r : ℝ≥0) (x : E) : ‖scaleToNorm r x‖ ≤ r := by
  by_cases h : ‖x‖ = 0
  · rw [scaleToNorm_of_norm_zero r h, norm_zero]
    exact r.2
  · exact (norm_scaleToNorm_eq' r h).le

/-!
### `scaleToNorm` and `SameRay`

In this section we show that `scaleToNorm r x` and `x` belong to the same ray.

TODO: prove `SameRay ℝ x y → SameRay ℝ (scaleToNorm r x) y`. What are the right `≠ 0` assumptions?
-/

lemma SameRay.scaleToNorm_self (r : ℝ≥0) (x : E) : SameRay ℝ (scaleToNorm r x) x :=
  sameRay_nonneg_smul_left _ (by positivity)

lemma SameRay.self_scaleToNorm (r : ℝ≥0) (x : E) : SameRay ℝ x (scaleToNorm r x) :=
  .symm <| .scaleToNorm_self _ _

/-!
### Fixed points and composition of `scaleToNorm`s
-/

lemma scaleToNorm_eq_self' (hr : r ≠ 0) {x : E} (hx : ‖x‖ = r) :
    scaleToNorm r x = x := by
  rw [scaleToNorm, hx, div_self (NNReal.coe_ne_zero.2 hr), one_smul]

lemma scaleToNorm_eq_self (r : ℝ≥0) {x : F} (hx : ‖x‖ = r) :
    scaleToNorm r x = x := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp_all
  · exact scaleToNorm_eq_self' hr hx

lemma scaleToNorm_smul (r : ℝ≥0) {c : ℝ} (hc : 0 < c) (x : E) :
    scaleToNorm r (c • x) = scaleToNorm r x := by
  rw [scaleToNorm, scaleToNorm, norm_smul, smul_smul, div_mul, Real.norm_eq_abs,
    abs_of_pos hc, mul_div_cancel_left _ hc.ne']

lemma scaleToNorm_scaleToNorm (r₁ : ℝ≥0) {r₂ : ℝ≥0} (hr₂ : r₂ ≠ 0) (x : E) :
    scaleToNorm r₁ (scaleToNorm r₂ x) = scaleToNorm r₁ x := by
  cases' (norm_nonneg x).eq_or_gt with hx hx
  · simp [scaleToNorm, hx] 
  · apply scaleToNorm_smul
    exact div_pos (NNReal.coe_pos.2 hr₂.bot_lt) hx

/-!
### Image and range

In this section we show that `scaleToNorm r` sends `{0}ᶜ` to the sphere of radius `r` and the whole
space to the union of this sphere and the origin. The results are formulated using `Set.image` and
`Set.range`.
-/

lemma image_scaleToNorm_norm_ne_zero (hr : r ≠ 0) :
    scaleToNorm r '' {x : E | ‖x‖ ≠ 0} = sphere 0 r := by
  apply Subset.antisymm
  · exact image_subset_iff.2 (fun x ↦ scaleToNorm_mem_sphere' r)
  · refine fun x hx ↦ ⟨x, ?_, scaleToNorm_eq_self' hr (mem_sphere_zero_iff_norm.1 hx)⟩
    simp [mem_sphere_zero_iff_norm.1 hx, hr]

lemma image_scaleToNorm_compl_zero' (hr : r ≠ 0) :
    scaleToNorm r '' ({0}ᶜ : Set F) = sphere 0 r := by
  simp [← image_scaleToNorm_norm_ne_zero hr, Set.compl_def]

lemma image_scaleToNorm_compl_zero [Nontrivial F] (r : ℝ≥0) :
    scaleToNorm r '' ({0}ᶜ : Set F) = sphere 0 r := by
  rcases eq_or_ne r 0 with rfl | hr
  · have : Set.Nonempty ({0}ᶜ : Set F) := exists_ne _
    simp [this]
  · exact image_scaleToNorm_compl_zero' hr

lemma range_scaleToNorm' (hr : r ≠ 0) :
    range (scaleToNorm r) = insert 0 (sphere (0 : E) r) := by
  refine (range_subset_iff.2 <| fun x ↦ ?_).antisymm (insert_subset.2 ⟨?_, fun x hx ↦ ?_⟩)
  · cases' eq_or_ne (‖x‖) 0 with hx hx
    · rw [scaleToNorm_of_norm_zero _ hx]
      exact mem_insert _ _
    · simp only [← image_scaleToNorm_norm_ne_zero hr]
      exact mem_insert_of_mem _ (mem_image_of_mem _ hx)
  · exact ⟨0, scaleToNorm_zero_right _⟩
  · exact ⟨x, scaleToNorm_eq_self' hr (mem_sphere_zero_iff_norm.1 hx)⟩

lemma range_scaleToNorm (r : ℝ≥0) :
    range (scaleToNorm r) = insert 0 (sphere (0 : F) r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [Pi.zero_def]
  · exact range_scaleToNorm' hr

/-!
### Continuity of `scaleToNorm`

In this section we show that `scaleToNorm r x` is continuous in `r` everywhere and is continuous in
`x` away from zero. We also prove that `scaleToNorm (f a) (g a)` is continuous everywhere provided
that both `f` and `g` are continuous and `g a = 0` implies `f a = 0` for all `a`.
-/

lemma continuous_scaleToNorm_left (x : E) : Continuous (fun r ↦ scaleToNorm r x) :=
  (continuous_subtype_val.div_const _).smul continuous_const

lemma continuousOn_scaleToNorm₂' :
    ContinuousOn (fun p : ℝ≥0 × E ↦ scaleToNorm p.1 p.2) { p | ‖p.2‖ ≠ 0 } :=
  ((continuous_subtype_val.comp_continuousOn continuousOn_fst).div
    continuousOn_snd.norm <| fun _ ↦ id).smul continuousOn_snd

lemma continuousOn_scaleToNorm₂ :
    ContinuousOn (fun p : ℝ≥0 × F ↦ scaleToNorm p.1 p.2) { p | p.2 ≠ 0 } := by
  convert ← continuousOn_scaleToNorm₂' (E := F)
  exact norm_eq_zero

lemma continuousOn_scaleToNorm_right' (r : ℝ≥0) :
    ContinuousOn (scaleToNorm r) {x : E | ‖x‖ ≠ 0} :=
  continuousOn_scaleToNorm₂'.comp (continuousOn_const.prod continuousOn_id) fun _ ↦ id

lemma continuousOn_scaleToNorm_right (r : ℝ≥0) :
    ContinuousOn (scaleToNorm r) ({0}ᶜ : Set F) :=
  continuousOn_scaleToNorm₂.comp (continuousOn_const.prod continuousOn_id) fun _ ↦ id

variable {α X : Type _} [TopologicalSpace X]

protected lemma Filter.Tendsto.scaleToNorm' {l : Filter α} {f : α → ℝ≥0} {r : ℝ≥0}
    (hf : Tendsto f l (𝓝 r)) {g : α → E} {x : E} (hg : Tendsto g l (𝓝 x)) (h₀ : ‖x‖ = 0 → r = 0) :
    Tendsto (fun a ↦ scaleToNorm (f a) (g a)) l (𝓝 (scaleToNorm r x)) := by
  cases eq_or_ne (‖x‖) 0 with
  | inl hx =>
    obtain rfl := h₀ hx
    rw [scaleToNorm_of_norm_zero _ hx]
    exact squeeze_zero_norm (fun _ ↦ norm_scaleToNorm_le _ _) (NNReal.tendsto_coe.2 hf)
  | inr hx =>
    refine (continuousOn_scaleToNorm₂' (r, x) hx).tendsto.comp <|
      tendsto_nhdsWithin_iff.2 ⟨hf.prod_mk_nhds hg, ?_⟩
    exact hg.norm.eventually (isOpen_ne.mem_nhds hx)

protected lemma Filter.Tendsto.scaleToNorm {l : Filter α} {f : α → ℝ≥0} {r : ℝ≥0}
    (hf : Tendsto f l (𝓝 r)) {g : α → F} {x : F} (hg : Tendsto g l (𝓝 x)) (h₀ : x = 0 → r = 0) :
    Tendsto (fun a ↦ scaleToNorm (f a) (g a)) l (𝓝 (scaleToNorm r x)) :=
  hf.scaleToNorm' hg <| by simpa only [norm_eq_zero] using h₀

protected lemma Continuous.scaleToNorm' {f : X → ℝ≥0} {g : X → E} (hf : Continuous f)
    (hg : Continuous g) (h₀ : ∀ x, ‖g x‖ = 0 → f x = 0) :
    Continuous fun x ↦ scaleToNorm (f x) (g x) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.scaleToNorm' hg.continuousAt (h₀ _)

protected lemma Continuous.scaleToNorm {f : X → ℝ≥0} {g : X → F} (hf : Continuous f)
    (hg : Continuous g) (h₀ : ∀ x, g x = 0 → f x = 0) :
    Continuous fun x ↦ scaleToNorm (f x) (g x) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.scaleToNorm hg.continuousAt (h₀ _)
