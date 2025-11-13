/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Smooth bump functions on a smooth manifold

In this file we define `SmoothBumpFunction I c` to be a bundled smooth "bump" function centered at
`c`. It is a structure that consists of two real numbers `0 < rIn < rOut` with small enough `rOut`.
We define a coercion to function for this type, and for `f : SmoothBumpFunction I c`, the function
`⇑f` written in the extended chart at `c` has the following properties:

* `f x = 1` in the closed ball of radius `f.rIn` centered at `c`;
* `f x = 0` outside of the ball of radius `f.rOut` centered at `c`;
* `0 ≤ f x ≤ 1` for all `x`.

The actual statements involve (pre)images under `extChartAt I f` and are given as lemmas in the
`SmoothBumpFunction` namespace.

## Tags

manifold, smooth bump function
-/

universe uE uF uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M]

open Function Filter Module Set Metric

open scoped Topology Manifold ContDiff

noncomputable section

/-!
### Smooth bump function

In this section we define a structure for a bundled smooth bump function and prove its properties.
-/

variable (I) in
/-- Given a smooth manifold modelled on a finite-dimensional space `E`,
`f : SmoothBumpFunction I M` is a smooth function on `M` such that in the extended chart `e` at
`f.c`:

* `f x = 1` in the closed ball of radius `f.rIn` centered at `f.c`;
* `f x = 0` outside of the ball of radius `f.rOut` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The structure contains data required to construct a function with these properties. The function is
available as `⇑f` or `f x`. Formal statements of the properties listed above involve some
(pre)images under `extChartAt I f.c` and are given as lemmas in the `SmoothBumpFunction`
namespace. -/
structure SmoothBumpFunction (c : M) extends ContDiffBump (extChartAt I c c) where
  closedBall_subset : closedBall (extChartAt I c c) rOut ∩ range I ⊆ (extChartAt I c).target

namespace SmoothBumpFunction

section FiniteDimensional

variable [FiniteDimensional ℝ E]

variable {c : M} (f : SmoothBumpFunction I c) {x : M}

/-- The function defined by `f : SmoothBumpFunction c`. Use automatic coercion to function
instead. -/
@[coe] def toFun : M → ℝ :=
  indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)

instance : CoeFun (SmoothBumpFunction I c) fun _ => M → ℝ :=
  ⟨toFun⟩

theorem coe_def : ⇑f = indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c) :=
  rfl

end FiniteDimensional

variable {c : M} (f : SmoothBumpFunction I c) {x : M}

theorem rOut_pos : 0 < f.rOut :=
  f.toContDiffBump.rOut_pos

theorem ball_subset : ball (extChartAt I c c) f.rOut ∩ range I ⊆ (extChartAt I c).target :=
  Subset.trans (inter_subset_inter_left _ ball_subset_closedBall) f.closedBall_subset

theorem ball_inter_range_eq_ball_inter_target :
    ball (extChartAt I c c) f.rOut ∩ range I =
      ball (extChartAt I c c) f.rOut ∩ (extChartAt I c).target :=
  (subset_inter inter_subset_left f.ball_subset).antisymm <| inter_subset_inter_right _ <|
    extChartAt_target_subset_range _

section FiniteDimensional

variable [FiniteDimensional ℝ E]

theorem eqOn_source : EqOn f (f.toContDiffBump ∘ extChartAt I c) (chartAt H c).source :=
  eqOn_indicator

theorem eventuallyEq_of_mem_source (hx : x ∈ (chartAt H c).source) :
    f =ᶠ[𝓝 x] f.toContDiffBump ∘ extChartAt I c :=
  f.eqOn_source.eventuallyEq_of_mem <| (chartAt H c).open_source.mem_nhds hx

theorem one_of_dist_le (hs : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) ≤ f.rIn) : f x = 1 := by
  simp only [f.eqOn_source hs, (· ∘ ·), f.one_of_mem_closedBall hd]

theorem support_eq_inter_preimage :
    support f = (chartAt H c).source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) f.rOut := by
  rw [coe_def, support_indicator, support_comp_eq_preimage, ← extChartAt_source I,
    ← (extChartAt I c).symm_image_target_inter_eq', ← (extChartAt I c).symm_image_target_inter_eq',
    f.support_eq]

theorem isOpen_support : IsOpen (support f) := by
  rw [support_eq_inter_preimage]
  exact isOpen_extChartAt_preimage c isOpen_ball

theorem support_eq_symm_image :
    support f = (extChartAt I c).symm '' (ball (extChartAt I c c) f.rOut ∩ range I) := by
  rw [f.support_eq_inter_preimage, ← extChartAt_source I,
    ← (extChartAt I c).symm_image_target_inter_eq', inter_comm,
    ball_inter_range_eq_ball_inter_target]

theorem support_subset_source : support f ⊆ (chartAt H c).source := by
  rw [f.support_eq_inter_preimage, ← extChartAt_source I]; exact inter_subset_left

theorem image_eq_inter_preimage_of_subset_support {s : Set M} (hs : s ⊆ support f) :
    extChartAt I c '' s =
      closedBall (extChartAt I c c) f.rOut ∩ range I ∩ (extChartAt I c).symm ⁻¹' s := by
  rw [support_eq_inter_preimage, subset_inter_iff, ← extChartAt_source I, ← image_subset_iff] at hs
  obtain ⟨hse, hsf⟩ := hs
  apply Subset.antisymm
  · refine subset_inter (subset_inter (hsf.trans ball_subset_closedBall) ?_) ?_
    · rintro _ ⟨x, -, rfl⟩; exact mem_range_self _
    · rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
      exact inter_subset_right
  · refine Subset.trans (inter_subset_inter_left _ f.closedBall_subset) ?_
    rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]

theorem mem_Icc : f x ∈ Icc (0 : ℝ) 1 := by
  have : f x = 0 ∨ f x = _ := indicator_eq_zero_or_self _ _ _
  rcases this with h | h <;> rw [h]
  exacts [left_mem_Icc.2 zero_le_one, ⟨f.nonneg, f.le_one⟩]

theorem nonneg : 0 ≤ f x :=
  f.mem_Icc.1

theorem le_one : f x ≤ 1 :=
  f.mem_Icc.2

theorem eventuallyEq_one_of_dist_lt (hs : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < f.rIn) : f =ᶠ[𝓝 x] 1 := by
  filter_upwards [IsOpen.mem_nhds (isOpen_extChartAt_preimage c isOpen_ball) ⟨hs, hd⟩]
  rintro z ⟨hzs, hzd⟩
  exact f.one_of_dist_le hzs <| le_of_lt hzd

theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_dist_lt (mem_chart_source _ _) <| by rw [dist_self]; exact f.rIn_pos

@[simp]
theorem eq_one : f c = 1 :=
  f.eventuallyEq_one.eq_of_nhds

theorem support_mem_nhds : support f ∈ 𝓝 c :=
  f.eventuallyEq_one.mono fun x hx => by rw [hx]; exact one_ne_zero

theorem tsupport_mem_nhds : tsupport f ∈ 𝓝 c :=
  mem_of_superset f.support_mem_nhds subset_closure

theorem c_mem_support : c ∈ support f :=
  mem_of_mem_nhds f.support_mem_nhds

theorem nonempty_support : (support f).Nonempty :=
  ⟨c, f.c_mem_support⟩

theorem isCompact_symm_image_closedBall :
    IsCompact ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I)) :=
  ((isCompact_closedBall _ _).inter_right I.isClosed_range).image_of_continuousOn <|
    (continuousOn_extChartAt_symm _).mono f.closedBall_subset

end FiniteDimensional

/-- Given a smooth bump function `f : SmoothBumpFunction I c`, the closed ball of radius `f.R` is
known to include the support of `f`. These closed balls (in the model normed space `E`) intersected
with `Set.range I` form a basis of `𝓝[range I] (extChartAt I c c)`. -/
theorem nhdsWithin_range_basis :
    (𝓝[range I] extChartAt I c c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      closedBall (extChartAt I c c) f.rOut ∩ range I := by
  refine ((nhdsWithin_hasBasis nhds_basis_closedBall _).restrict_subset
    (extChartAt_target_mem_nhdsWithin _)).to_hasBasis' ?_ ?_
  · rintro R ⟨hR0, hsub⟩
    exact ⟨⟨⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩, hsub⟩, trivial, Subset.rfl⟩
  · exact fun f _ => inter_mem (mem_nhdsWithin_of_mem_nhds <| closedBall_mem_nhds _ f.rOut_pos)
      self_mem_nhdsWithin

variable [FiniteDimensional ℝ E]

theorem isClosed_image_of_isClosed {s : Set M} (hsc : IsClosed s) (hs : s ⊆ support f) :
    IsClosed (extChartAt I c '' s) := by
  rw [f.image_eq_inter_preimage_of_subset_support hs]
  refine ContinuousOn.preimage_isClosed_of_isClosed
    ((continuousOn_extChartAt_symm _).mono f.closedBall_subset) ?_ hsc
  exact IsClosed.inter isClosed_closedBall I.isClosed_range

/-- If `f` is a smooth bump function and `s` closed subset of the support of `f` (i.e., of the open
ball of radius `f.rOut`), then there exists `0 < r < f.rOut` such that `s` is a subset of the open
ball of radius `r`. Formally, `s ⊆ e.source ∩ e ⁻¹' (ball (e c) r)`, where `e = extChartAt I c`. -/
theorem exists_r_pos_lt_subset_ball {s : Set M} (hsc : IsClosed s) (hs : s ⊆ support f) :
    ∃ r ∈ Ioo 0 f.rOut,
      s ⊆ (chartAt H c).source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) r := by
  set e := extChartAt I c
  have : IsClosed (e '' s) := f.isClosed_image_of_isClosed hsc hs
  rw [support_eq_inter_preimage, subset_inter_iff, ← image_subset_iff] at hs
  rcases exists_pos_lt_subset_ball f.rOut_pos this hs.2 with ⟨r, hrR, hr⟩
  exact ⟨r, hrR, subset_inter hs.1 (image_subset_iff.1 hr)⟩

/-- Replace `rIn` with another value in the interval `(0, f.rOut)`. -/
@[simps rOut rIn]
def updateRIn (r : ℝ) (hr : r ∈ Ioo 0 f.rOut) : SmoothBumpFunction I c :=
  ⟨⟨r, f.rOut, hr.1, hr.2⟩, f.closedBall_subset⟩

@[simp]
theorem support_updateRIn {r : ℝ} (hr : r ∈ Ioo 0 f.rOut) :
    support (f.updateRIn r hr) = support f := by
  simp only [support_eq_inter_preimage, updateRIn_rOut]

instance : Nonempty (SmoothBumpFunction I c) := nhdsWithin_range_basis.nonempty

variable [T2Space M]

theorem isClosed_symm_image_closedBall :
    IsClosed ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I)) :=
  f.isCompact_symm_image_closedBall.isClosed

theorem tsupport_subset_symm_image_closedBall :
    tsupport f ⊆ (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) := by
  rw [tsupport, support_eq_symm_image]
  exact closure_minimal (image_mono <| inter_subset_inter_left _ ball_subset_closedBall)
    f.isClosed_symm_image_closedBall

theorem tsupport_subset_extChartAt_source : tsupport f ⊆ (extChartAt I c).source :=
  calc
    tsupport f ⊆ (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) :=
      f.tsupport_subset_symm_image_closedBall
    _ ⊆ (extChartAt I c).symm '' (extChartAt I c).target := image_mono f.closedBall_subset
    _ = (extChartAt I c).source := (extChartAt I c).symm_image_target_eq_source

theorem tsupport_subset_chartAt_source : tsupport f ⊆ (chartAt H c).source := by
  simpa only [extChartAt_source] using f.tsupport_subset_extChartAt_source

protected theorem hasCompactSupport : HasCompactSupport f :=
  f.isCompact_symm_image_closedBall.of_isClosed_subset isClosed_closure
    f.tsupport_subset_symm_image_closedBall

variable (c) in
/-- The closures of supports of smooth bump functions centered at `c` form a basis of `𝓝 c`.
In other words, each of these closures is a neighborhood of `c` and each neighborhood of `c`
includes `tsupport f` for some `f : SmoothBumpFunction I c`. -/
theorem nhds_basis_tsupport :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f => tsupport f := by
  have :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c]
    exact nhdsWithin_range_basis.map _
  exact this.to_hasBasis' (fun f _ => ⟨f, trivial, f.tsupport_subset_symm_image_closedBall⟩)
    fun f _ => f.tsupport_mem_nhds

/-- Given `s ∈ 𝓝 c`, the supports of smooth bump functions `f : SmoothBumpFunction I c` such that
`tsupport f ⊆ s` form a basis of `𝓝 c`.  In other words, each of these supports is a
neighborhood of `c` and each neighborhood of `c` includes `support f` for some
`f : SmoothBumpFunction I c` such that `tsupport f ⊆ s`. -/
theorem nhds_basis_support {s : Set M} (hs : s ∈ 𝓝 c) :
    (𝓝 c).HasBasis (fun f : SmoothBumpFunction I c => tsupport f ⊆ s) fun f => support f :=
  ((nhds_basis_tsupport c).restrict_subset hs).to_hasBasis'
    (fun f hf => ⟨f, hf.2, subset_closure⟩) fun f _ => f.support_mem_nhds

variable [IsManifold I ∞ M]

/-- A smooth bump function is infinitely smooth. -/
protected theorem contMDiff : ContMDiff I 𝓘(ℝ) ∞ f := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have : x ∈ (chartAt H c).source := f.tsupport_subset_chartAt_source hx
  refine ContMDiffAt.congr_of_eventuallyEq ?_ <| f.eqOn_source.eventuallyEq_of_mem <|
    (chartAt H c).open_source.mem_nhds this
  exact f.contDiffAt.contMDiffAt.comp _ (contMDiffAt_extChartAt' this)

protected theorem contMDiffAt {x} : ContMDiffAt I 𝓘(ℝ) ∞ f x :=
  f.contMDiff.contMDiffAt

protected theorem continuous : Continuous f :=
  f.contMDiff.continuous

/-- If `f : SmoothBumpFunction I c` is a smooth bump function and `g : M → G` is a function smooth
on the source of the chart at `c`, then `f • g` is smooth on the whole manifold. -/
theorem contMDiff_smul {G} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : M → G}
    (hg : ContMDiffOn I 𝓘(ℝ, G) ∞ g (chartAt H c).source) :
    ContMDiff I 𝓘(ℝ, G) ∞ fun x => f x • g x := by
  refine contMDiff_of_tsupport fun x hx => ?_
  -- Porting note: was a more readable `calc`
  -- calc
  --   x ∈ tsupport fun x => f x • g x := hx
  --   _ ⊆ tsupport f := tsupport_smul_subset_left _ _
  --   _ ⊆ (chart_at _ c).source := f.tsupport_subset_chartAt_source
  have : x ∈ (chartAt H c).source :=
    f.tsupport_subset_chartAt_source <| tsupport_smul_subset_left _ _ hx
  exact f.contMDiffAt.smul ((hg _ this).contMDiffAt <| (chartAt _ _).open_source.mem_nhds this)

end SmoothBumpFunction
