/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

#align_import geometry.manifold.bump_function from "leanprover-community/mathlib"@"b018406ad2f2a73223a3a9e198ccae61e6f05318"

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

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M]

open Function Filter FiniteDimensional Set Metric

open scoped Topology Manifold Classical Filter

noncomputable section

/-!
### Smooth bump function

In this section we define a structure for a bundled smooth bump function and prove its properties.
-/

/-- Given a smooth manifold modelled on a finite dimensional space `E`,
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
#align smooth_bump_function SmoothBumpFunction

namespace SmoothBumpFunction

variable {c : M} (f : SmoothBumpFunction I c) {x : M} {I}

/-- The function defined by `f : SmoothBumpFunction c`. Use automatic coercion to function
instead. -/
@[coe] def toFun : M → ℝ :=
  indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)
#align smooth_bump_function.to_fun SmoothBumpFunction.toFun

instance : CoeFun (SmoothBumpFunction I c) fun _ => M → ℝ :=
  ⟨toFun⟩

theorem coe_def : ⇑f = indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c) :=
  rfl
#align smooth_bump_function.coe_def SmoothBumpFunction.coe_def

theorem rOut_pos : 0 < f.rOut :=
  f.toContDiffBump.rOut_pos
set_option linter.uppercaseLean3 false in
#align smooth_bump_function.R_pos SmoothBumpFunction.rOut_pos

theorem ball_subset : ball (extChartAt I c c) f.rOut ∩ range I ⊆ (extChartAt I c).target :=
  Subset.trans (inter_subset_inter_left _ ball_subset_closedBall) f.closedBall_subset
#align smooth_bump_function.ball_subset SmoothBumpFunction.ball_subset

theorem ball_inter_range_eq_ball_inter_target :
    ball (extChartAt I c c) f.rOut ∩ range I =
      ball (extChartAt I c c) f.rOut ∩ (extChartAt I c).target :=
  (subset_inter inter_subset_left f.ball_subset).antisymm <| inter_subset_inter_right _ <|
    extChartAt_target_subset_range _ _

theorem eqOn_source : EqOn f (f.toContDiffBump ∘ extChartAt I c) (chartAt H c).source :=
  eqOn_indicator
#align smooth_bump_function.eq_on_source SmoothBumpFunction.eqOn_source

theorem eventuallyEq_of_mem_source (hx : x ∈ (chartAt H c).source) :
    f =ᶠ[𝓝 x] f.toContDiffBump ∘ extChartAt I c :=
  f.eqOn_source.eventuallyEq_of_mem <| (chartAt H c).open_source.mem_nhds hx
#align smooth_bump_function.eventually_eq_of_mem_source SmoothBumpFunction.eventuallyEq_of_mem_source

theorem one_of_dist_le (hs : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) ≤ f.rIn) : f x = 1 := by
  simp only [f.eqOn_source hs, (· ∘ ·), f.one_of_mem_closedBall hd]
#align smooth_bump_function.one_of_dist_le SmoothBumpFunction.one_of_dist_le

theorem support_eq_inter_preimage :
    support f = (chartAt H c).source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) f.rOut := by
  rw [coe_def, support_indicator, support_comp_eq_preimage, ← extChartAt_source I,
    ← (extChartAt I c).symm_image_target_inter_eq', ← (extChartAt I c).symm_image_target_inter_eq',
    f.support_eq]
#align smooth_bump_function.support_eq_inter_preimage SmoothBumpFunction.support_eq_inter_preimage

theorem isOpen_support : IsOpen (support f) := by
  rw [support_eq_inter_preimage]
  exact isOpen_extChartAt_preimage I c isOpen_ball
#align smooth_bump_function.is_open_support SmoothBumpFunction.isOpen_support

theorem support_eq_symm_image :
    support f = (extChartAt I c).symm '' (ball (extChartAt I c c) f.rOut ∩ range I) := by
  rw [f.support_eq_inter_preimage, ← extChartAt_source I,
    ← (extChartAt I c).symm_image_target_inter_eq', inter_comm,
    ball_inter_range_eq_ball_inter_target]
#align smooth_bump_function.support_eq_symm_image SmoothBumpFunction.support_eq_symm_image

theorem support_subset_source : support f ⊆ (chartAt H c).source := by
  rw [f.support_eq_inter_preimage, ← extChartAt_source I]; exact inter_subset_left
#align smooth_bump_function.support_subset_source SmoothBumpFunction.support_subset_source

theorem image_eq_inter_preimage_of_subset_support {s : Set M} (hs : s ⊆ support f) :
    extChartAt I c '' s =
      closedBall (extChartAt I c c) f.rOut ∩ range I ∩ (extChartAt I c).symm ⁻¹' s := by
  rw [support_eq_inter_preimage, subset_inter_iff, ← extChartAt_source I, ← image_subset_iff] at hs
  cases' hs with hse hsf
  apply Subset.antisymm
  · refine subset_inter (subset_inter (hsf.trans ball_subset_closedBall) ?_) ?_
    · rintro _ ⟨x, -, rfl⟩; exact mem_range_self _
    · rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
      exact inter_subset_right
  · refine Subset.trans (inter_subset_inter_left _ f.closedBall_subset) ?_
    rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
#align smooth_bump_function.image_eq_inter_preimage_of_subset_support SmoothBumpFunction.image_eq_inter_preimage_of_subset_support

theorem mem_Icc : f x ∈ Icc (0 : ℝ) 1 := by
  have : f x = 0 ∨ f x = _ := indicator_eq_zero_or_self _ _ _
  cases' this with h h <;> rw [h]
  exacts [left_mem_Icc.2 zero_le_one, ⟨f.nonneg, f.le_one⟩]
#align smooth_bump_function.mem_Icc SmoothBumpFunction.mem_Icc

theorem nonneg : 0 ≤ f x :=
  f.mem_Icc.1
#align smooth_bump_function.nonneg SmoothBumpFunction.nonneg

theorem le_one : f x ≤ 1 :=
  f.mem_Icc.2
#align smooth_bump_function.le_one SmoothBumpFunction.le_one

theorem eventuallyEq_one_of_dist_lt (hs : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < f.rIn) : f =ᶠ[𝓝 x] 1 := by
  filter_upwards [IsOpen.mem_nhds (isOpen_extChartAt_preimage I c isOpen_ball) ⟨hs, hd⟩]
  rintro z ⟨hzs, hzd⟩
  exact f.one_of_dist_le hzs <| le_of_lt hzd
#align smooth_bump_function.eventually_eq_one_of_dist_lt SmoothBumpFunction.eventuallyEq_one_of_dist_lt

theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_dist_lt (mem_chart_source _ _) <| by rw [dist_self]; exact f.rIn_pos
#align smooth_bump_function.eventually_eq_one SmoothBumpFunction.eventuallyEq_one

@[simp]
theorem eq_one : f c = 1 :=
  f.eventuallyEq_one.eq_of_nhds
#align smooth_bump_function.eq_one SmoothBumpFunction.eq_one

theorem support_mem_nhds : support f ∈ 𝓝 c :=
  f.eventuallyEq_one.mono fun x hx => by rw [hx]; exact one_ne_zero
#align smooth_bump_function.support_mem_nhds SmoothBumpFunction.support_mem_nhds

theorem tsupport_mem_nhds : tsupport f ∈ 𝓝 c :=
  mem_of_superset f.support_mem_nhds subset_closure
#align smooth_bump_function.tsupport_mem_nhds SmoothBumpFunction.tsupport_mem_nhds

theorem c_mem_support : c ∈ support f :=
  mem_of_mem_nhds f.support_mem_nhds
#align smooth_bump_function.c_mem_support SmoothBumpFunction.c_mem_support

theorem nonempty_support : (support f).Nonempty :=
  ⟨c, f.c_mem_support⟩
#align smooth_bump_function.nonempty_support SmoothBumpFunction.nonempty_support

theorem isCompact_symm_image_closedBall :
    IsCompact ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I)) :=
  ((isCompact_closedBall _ _).inter_right I.isClosed_range).image_of_continuousOn <|
    (continuousOn_extChartAt_symm _ _).mono f.closedBall_subset
#align smooth_bump_function.is_compact_symm_image_closed_ball SmoothBumpFunction.isCompact_symm_image_closedBall

/-- Given a smooth bump function `f : SmoothBumpFunction I c`, the closed ball of radius `f.R` is
known to include the support of `f`. These closed balls (in the model normed space `E`) intersected
with `Set.range I` form a basis of `𝓝[range I] (extChartAt I c c)`. -/
theorem nhdsWithin_range_basis :
    (𝓝[range I] extChartAt I c c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      closedBall (extChartAt I c c) f.rOut ∩ range I := by
  refine ((nhdsWithin_hasBasis nhds_basis_closedBall _).restrict_subset
    (extChartAt_target_mem_nhdsWithin _ _)).to_hasBasis' ?_ ?_
  · rintro R ⟨hR0, hsub⟩
    exact ⟨⟨⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩, hsub⟩, trivial, Subset.rfl⟩
  · exact fun f _ => inter_mem (mem_nhdsWithin_of_mem_nhds <| closedBall_mem_nhds _ f.rOut_pos)
      self_mem_nhdsWithin
#align smooth_bump_function.nhds_within_range_basis SmoothBumpFunction.nhdsWithin_range_basis

theorem isClosed_image_of_isClosed {s : Set M} (hsc : IsClosed s) (hs : s ⊆ support f) :
    IsClosed (extChartAt I c '' s) := by
  rw [f.image_eq_inter_preimage_of_subset_support hs]
  refine ContinuousOn.preimage_isClosed_of_isClosed
    ((continuousOn_extChartAt_symm _ _).mono f.closedBall_subset) ?_ hsc
  exact IsClosed.inter isClosed_ball I.isClosed_range
#align smooth_bump_function.is_closed_image_of_is_closed SmoothBumpFunction.isClosed_image_of_isClosed

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
#align smooth_bump_function.exists_r_pos_lt_subset_ball SmoothBumpFunction.exists_r_pos_lt_subset_ball

/-- Replace `rIn` with another value in the interval `(0, f.rOut)`. -/
@[simps rOut rIn]
def updateRIn (r : ℝ) (hr : r ∈ Ioo 0 f.rOut) : SmoothBumpFunction I c :=
  ⟨⟨r, f.rOut, hr.1, hr.2⟩, f.closedBall_subset⟩
#align smooth_bump_function.update_r SmoothBumpFunction.updateRIn
set_option linter.uppercaseLean3 false in
#align smooth_bump_function.update_r_R SmoothBumpFunction.updateRIn_rOut
#align smooth_bump_function.update_r_r SmoothBumpFunction.updateRIn_rIn

@[simp]
theorem support_updateRIn {r : ℝ} (hr : r ∈ Ioo 0 f.rOut) :
    support (f.updateRIn r hr) = support f := by
  simp only [support_eq_inter_preimage, updateRIn_rOut]
#align smooth_bump_function.support_update_r SmoothBumpFunction.support_updateRIn

-- Porting note: was an `Inhabited` instance
instance : Nonempty (SmoothBumpFunction I c) := nhdsWithin_range_basis.nonempty

variable [T2Space M]

theorem isClosed_symm_image_closedBall :
    IsClosed ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I)) :=
  f.isCompact_symm_image_closedBall.isClosed
#align smooth_bump_function.is_closed_symm_image_closed_ball SmoothBumpFunction.isClosed_symm_image_closedBall

theorem tsupport_subset_symm_image_closedBall :
    tsupport f ⊆ (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) := by
  rw [tsupport, support_eq_symm_image]
  exact closure_minimal (image_subset _ <| inter_subset_inter_left _ ball_subset_closedBall)
    f.isClosed_symm_image_closedBall
#align smooth_bump_function.tsupport_subset_symm_image_closed_ball SmoothBumpFunction.tsupport_subset_symm_image_closedBall

theorem tsupport_subset_extChartAt_source : tsupport f ⊆ (extChartAt I c).source :=
  calc
    tsupport f ⊆ (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) :=
      f.tsupport_subset_symm_image_closedBall
    _ ⊆ (extChartAt I c).symm '' (extChartAt I c).target := image_subset _ f.closedBall_subset
    _ = (extChartAt I c).source := (extChartAt I c).symm_image_target_eq_source
#align smooth_bump_function.tsupport_subset_ext_chart_at_source SmoothBumpFunction.tsupport_subset_extChartAt_source

theorem tsupport_subset_chartAt_source : tsupport f ⊆ (chartAt H c).source := by
  simpa only [extChartAt_source] using f.tsupport_subset_extChartAt_source
#align smooth_bump_function.tsupport_subset_chart_at_source SmoothBumpFunction.tsupport_subset_chartAt_source

protected theorem hasCompactSupport : HasCompactSupport f :=
  f.isCompact_symm_image_closedBall.of_isClosed_subset isClosed_closure
    f.tsupport_subset_symm_image_closedBall
#align smooth_bump_function.has_compact_support SmoothBumpFunction.hasCompactSupport

variable (I c)

/-- The closures of supports of smooth bump functions centered at `c` form a basis of `𝓝 c`.
In other words, each of these closures is a neighborhood of `c` and each neighborhood of `c`
includes `tsupport f` for some `f : SmoothBumpFunction I c`. -/
theorem nhds_basis_tsupport :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f => tsupport f := by
  have :
    (𝓝 c).HasBasis (fun _ : SmoothBumpFunction I c => True) fun f =>
      (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.rOut ∩ range I) := by
    rw [← map_extChartAt_symm_nhdsWithin_range I c]
    exact nhdsWithin_range_basis.map _
  exact this.to_hasBasis' (fun f _ => ⟨f, trivial, f.tsupport_subset_symm_image_closedBall⟩)
    fun f _ => f.tsupport_mem_nhds
#align smooth_bump_function.nhds_basis_tsupport SmoothBumpFunction.nhds_basis_tsupport

variable {c}

/-- Given `s ∈ 𝓝 c`, the supports of smooth bump functions `f : SmoothBumpFunction I c` such that
`tsupport f ⊆ s` form a basis of `𝓝 c`.  In other words, each of these supports is a
neighborhood of `c` and each neighborhood of `c` includes `support f` for some
`f : SmoothBumpFunction I c` such that `tsupport f ⊆ s`. -/
theorem nhds_basis_support {s : Set M} (hs : s ∈ 𝓝 c) :
    (𝓝 c).HasBasis (fun f : SmoothBumpFunction I c => tsupport f ⊆ s) fun f => support f :=
  ((nhds_basis_tsupport I c).restrict_subset hs).to_hasBasis'
    (fun f hf => ⟨f, hf.2, subset_closure⟩) fun f _ => f.support_mem_nhds
#align smooth_bump_function.nhds_basis_support SmoothBumpFunction.nhds_basis_support

variable [SmoothManifoldWithCorners I M] {I}

/-- A smooth bump function is infinitely smooth. -/
protected theorem smooth : Smooth I 𝓘(ℝ) f := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have : x ∈ (chartAt H c).source := f.tsupport_subset_chartAt_source hx
  refine ContMDiffAt.congr_of_eventuallyEq ?_ <| f.eqOn_source.eventuallyEq_of_mem <|
    (chartAt H c).open_source.mem_nhds this
  exact f.contDiffAt.contMDiffAt.comp _ (contMDiffAt_extChartAt' this)
#align smooth_bump_function.smooth SmoothBumpFunction.smooth

protected theorem smoothAt {x} : SmoothAt I 𝓘(ℝ) f x :=
  f.smooth.smoothAt
#align smooth_bump_function.smooth_at SmoothBumpFunction.smoothAt

protected theorem continuous : Continuous f :=
  f.smooth.continuous
#align smooth_bump_function.continuous SmoothBumpFunction.continuous

/-- If `f : SmoothBumpFunction I c` is a smooth bump function and `g : M → G` is a function smooth
on the source of the chart at `c`, then `f • g` is smooth on the whole manifold. -/
theorem smooth_smul {G} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : M → G}
    (hg : SmoothOn I 𝓘(ℝ, G) g (chartAt H c).source) : Smooth I 𝓘(ℝ, G) fun x => f x • g x := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have : x ∈ (chartAt H c).source :=
  -- Porting note: was a more readable `calc`
  -- calc
  --   x ∈ tsupport fun x => f x • g x := hx
  --   _ ⊆ tsupport f := tsupport_smul_subset_left _ _
  --   _ ⊆ (chart_at _ c).source := f.tsupport_subset_chartAt_source
    f.tsupport_subset_chartAt_source <| tsupport_smul_subset_left _ _ hx
  exact f.smoothAt.smul ((hg _ this).contMDiffAt <| (chartAt _ _).open_source.mem_nhds this)
#align smooth_bump_function.smooth_smul SmoothBumpFunction.smooth_smul

end SmoothBumpFunction
