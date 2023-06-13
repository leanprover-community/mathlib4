/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.conditional_expectation.ae_measurable
! leanprover-community/mathlib commit d8bbb04e2d2a44596798a9207ceefc0fb236e41e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-! # Functions a.e. measurable with respect to a sub-σ-algebra

A function `f` verifies `ae_strongly_measurable' m f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `ae_strongly_measurable`, but the
`measurable_space` structures used for the measurability statement and for the measure are
different.

We define `Lp_meas F 𝕜 m p μ`, the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-strongly
measurable function.

## Main statements

We define an `isometry_equiv` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of `Lp_meas`.

`Lp.induction_strongly_measurable` (see also `mem_ℒp.induction_strongly_measurable`):
To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.

-/


open TopologicalSpace Filter

open scoped ENNReal MeasureTheory

namespace MeasureTheory

/-- A function `f` verifies `ae_strongly_measurable' m f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `ae_strongly_measurable`, but the
`measurable_space` structures used for the measurability statement and for the measure are
different. -/
def AeStronglyMeasurable' {α β} [TopologicalSpace β] (m : MeasurableSpace α)
    {m0 : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g : α → β, strongly_measurable[m] g ∧ f =ᵐ[μ] g
#align measure_theory.ae_strongly_measurable' MeasureTheory.AeStronglyMeasurable'

namespace AeStronglyMeasurable'

variable {α β 𝕜 : Type _} {m m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
  {f g : α → β}

theorem congr (hf : AeStronglyMeasurable' m f μ) (hfg : f =ᵐ[μ] g) : AeStronglyMeasurable' m g μ :=
  by obtain ⟨f', hf'_meas, hff'⟩ := hf; exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩
#align measure_theory.ae_strongly_measurable'.congr MeasureTheory.AeStronglyMeasurable'.congr

theorem add [Add β] [ContinuousAdd β] (hf : AeStronglyMeasurable' m f μ)
    (hg : AeStronglyMeasurable' m g μ) : AeStronglyMeasurable' m (f + g) μ := by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  rcases hg with ⟨g', h_g'_meas, hgg'⟩
  exact ⟨f' + g', h_f'_meas.add h_g'_meas, hff'.add hgg'⟩
#align measure_theory.ae_strongly_measurable'.add MeasureTheory.AeStronglyMeasurable'.add

theorem neg [AddGroup β] [TopologicalAddGroup β] {f : α → β} (hfm : AeStronglyMeasurable' m f μ) :
    AeStronglyMeasurable' m (-f) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine' ⟨-f', hf'_meas.neg, hf_ae.mono fun x hx => _⟩
  simp_rw [Pi.neg_apply]
  rw [hx]
#align measure_theory.ae_strongly_measurable'.neg MeasureTheory.AeStronglyMeasurable'.neg

theorem sub [AddGroup β] [TopologicalAddGroup β] {f g : α → β} (hfm : AeStronglyMeasurable' m f μ)
    (hgm : AeStronglyMeasurable' m g μ) : AeStronglyMeasurable' m (f - g) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  rcases hgm with ⟨g', hg'_meas, hg_ae⟩
  refine' ⟨f' - g', hf'_meas.sub hg'_meas, hf_ae.mp (hg_ae.mono fun x hx1 hx2 => _)⟩
  simp_rw [Pi.sub_apply]
  rw [hx1, hx2]
#align measure_theory.ae_strongly_measurable'.sub MeasureTheory.AeStronglyMeasurable'.sub

theorem const_smul [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (c : 𝕜) (hf : AeStronglyMeasurable' m f μ) :
    AeStronglyMeasurable' m (c • f) μ := by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  refine' ⟨c • f', h_f'_meas.const_smul c, _⟩
  exact eventually_eq.fun_comp hff' fun x => c • x
#align measure_theory.ae_strongly_measurable'.const_smul MeasureTheory.AeStronglyMeasurable'.const_smul

theorem const_inner {𝕜 β} [IsROrC 𝕜] [NormedAddCommGroup β] [InnerProductSpace 𝕜 β] {f : α → β}
    (hfm : AeStronglyMeasurable' m f μ) (c : β) :
    AeStronglyMeasurable' m (fun x => (inner c (f x) : 𝕜)) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine'
    ⟨fun x => (inner c (f' x) : 𝕜), (@strongly_measurable_const _ _ m _ _).inner hf'_meas,
      hf_ae.mono fun x hx => _⟩
  dsimp only
  rw [hx]
#align measure_theory.ae_strongly_measurable'.const_inner MeasureTheory.AeStronglyMeasurable'.const_inner

/-- An `m`-strongly measurable function almost everywhere equal to `f`. -/
noncomputable def mk (f : α → β) (hfm : AeStronglyMeasurable' m f μ) : α → β :=
  hfm.some
#align measure_theory.ae_strongly_measurable'.mk MeasureTheory.AeStronglyMeasurable'.mk

theorem stronglyMeasurable_mk {f : α → β} (hfm : AeStronglyMeasurable' m f μ) :
    strongly_measurable[m] (hfm.mk f) :=
  hfm.choose_spec.1
#align measure_theory.ae_strongly_measurable'.strongly_measurable_mk MeasureTheory.AeStronglyMeasurable'.stronglyMeasurable_mk

theorem ae_eq_mk {f : α → β} (hfm : AeStronglyMeasurable' m f μ) : f =ᵐ[μ] hfm.mk f :=
  hfm.choose_spec.2
#align measure_theory.ae_strongly_measurable'.ae_eq_mk MeasureTheory.AeStronglyMeasurable'.ae_eq_mk

theorem continuous_comp {γ} [TopologicalSpace γ] {f : α → β} {g : β → γ} (hg : Continuous g)
    (hf : AeStronglyMeasurable' m f μ) : AeStronglyMeasurable' m (g ∘ f) μ :=
  ⟨fun x => g (hf.mk _ x),
    @Continuous.comp_stronglyMeasurable _ _ _ m _ _ _ _ hg hf.stronglyMeasurable_mk,
    hf.ae_eq_mk.mono fun x hx => by rw [Function.comp_apply, hx]⟩
#align measure_theory.ae_strongly_measurable'.continuous_comp MeasureTheory.AeStronglyMeasurable'.continuous_comp

end AeStronglyMeasurable'

theorem aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim {α β} {m m0 m0' : MeasurableSpace α}
    [TopologicalSpace β] (hm0 : m0 ≤ m0') {μ : Measure α} {f : α → β}
    (hf : AeStronglyMeasurable' m f (μ.trim hm0)) : AeStronglyMeasurable' m f μ := by
  obtain ⟨g, hg_meas, hfg⟩ := hf; exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩
#align measure_theory.ae_strongly_measurable'_of_ae_strongly_measurable'_trim MeasureTheory.aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim

theorem StronglyMeasurable.aeStronglyMeasurable' {α β} {m m0 : MeasurableSpace α}
    [TopologicalSpace β] {μ : Measure α} {f : α → β} (hf : strongly_measurable[m] f) :
    AeStronglyMeasurable' m f μ :=
  ⟨f, hf, ae_eq_refl _⟩
#align measure_theory.strongly_measurable.ae_strongly_measurable' MeasureTheory.StronglyMeasurable.aeStronglyMeasurable'

theorem ae_eq_trim_iff_of_aeStronglyMeasurable' {α β} [TopologicalSpace β] [MetrizableSpace β]
    {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β} (hm : m ≤ m0)
    (hfm : AeStronglyMeasurable' m f μ) (hgm : AeStronglyMeasurable' m g μ) :
    hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (ae_eq_trim_iff hm hfm.stronglyMeasurable_mk hgm.stronglyMeasurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h =>
      hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩
#align measure_theory.ae_eq_trim_iff_of_ae_strongly_measurable' MeasureTheory.ae_eq_trim_iff_of_aeStronglyMeasurable'

theorem AEStronglyMeasurable.comp_ae_measurable' {α β γ : Type _} [TopologicalSpace β]
    {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {f : α → β} {μ : Measure γ} {g : γ → α}
    (hf : AEStronglyMeasurable f (μ.map g)) (hg : AEMeasurable g μ) :
    AeStronglyMeasurable' (mα.comap g) (f ∘ g) μ :=
  ⟨hf.mk f ∘ g, hf.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl),
    ae_eq_comp hg hf.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.comp_ae_measurable' MeasureTheory.AEStronglyMeasurable.comp_ae_measurable'

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable. -/
theorem AeStronglyMeasurable'.aeStronglyMeasurable'_of_measurableSpace_le_on {α E}
    {m m₂ m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace E] [Zero E] (hm : m ≤ m0)
    {s : Set α} {f : α → E} (hs_m : measurable_set[m] s)
    (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t))
    (hf : AeStronglyMeasurable' m f μ) (hf_zero : f =ᵐ[μ.restrict (sᶜ)] 0) :
    AeStronglyMeasurable' m₂ f μ := by
  let f' := hf.mk f
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f := by
    refine'
      Filter.EventuallyEq.trans _ (indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero)
    filter_upwards [hf.ae_eq_mk] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs, hx]
    · simp [hxs]
  suffices : strongly_measurable[m₂] (s.indicator (hf.mk f))
  exact ae_strongly_measurable'.congr this.ae_strongly_measurable' h_ind_eq
  have hf_ind : strongly_measurable[m] (s.indicator (hf.mk f)) :=
    hf.strongly_measurable_mk.indicator hs_m
  exact
    hf_ind.strongly_measurable_of_measurable_space_le_on hs_m hs fun x hxs =>
      Set.indicator_of_not_mem hxs _
#align measure_theory.ae_strongly_measurable'.ae_strongly_measurable'_of_measurable_space_le_on MeasureTheory.AeStronglyMeasurable'.aeStronglyMeasurable'_of_measurableSpace_le_on

variable {α E' F F' 𝕜 : Type _} {p : ℝ≥0∞} [IsROrC 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- E' for an inner product space on which we compute integrals
  [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace ℝ E']
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']

section LpMeas

/-! ## The subset `Lp_meas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable (F)

/-- `Lp_meas_subgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    AddSubgroup (Lp F p μ) where
  carrier := {f : Lp F p μ | AeStronglyMeasurable' m f μ}
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' f g hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  neg_mem' f hf := AeStronglyMeasurable'.congr hf.neg (Lp.coeFn_neg f).symm
#align measure_theory.Lp_meas_subgroup MeasureTheory.lpMeasSubgroup

variable (𝕜)

/-- `Lp_meas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeas (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    Submodule 𝕜 (Lp F p μ) where
  carrier := {f : Lp F p μ | AeStronglyMeasurable' m f μ}
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' f g hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.const_smul c).congr (Lp.coeFn_smul c f).symm
#align measure_theory.Lp_meas MeasureTheory.lpMeas

variable {F 𝕜}

variable ()

theorem mem_lpMeasSubgroup_iff_aeStronglyMeasurable' {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f ∈ lpMeasSubgroup F m p μ ↔ AeStronglyMeasurable' m f μ := by
  rw [← AddSubgroup.mem_carrier, Lp_meas_subgroup, Set.mem_setOf_eq]
#align measure_theory.mem_Lp_meas_subgroup_iff_ae_strongly_measurable' MeasureTheory.mem_lpMeasSubgroup_iff_aeStronglyMeasurable'

theorem mem_lpMeas_iff_aeStronglyMeasurable' {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f ∈ lpMeas F 𝕜 m p μ ↔ AeStronglyMeasurable' m f μ := by
  rw [← SetLike.mem_coe, ← Submodule.mem_carrier, Lp_meas, Set.mem_setOf_eq]
#align measure_theory.mem_Lp_meas_iff_ae_strongly_measurable' MeasureTheory.mem_lpMeas_iff_aeStronglyMeasurable'

theorem lpMeas.aeStronglyMeasurable' {m m0 : MeasurableSpace α} {μ : Measure α}
    (f : lpMeas F 𝕜 m p μ) : AeStronglyMeasurable' m f μ :=
  mem_lpMeas_iff_aeStronglyMeasurable'.mp f.Mem
#align measure_theory.Lp_meas.ae_strongly_measurable' MeasureTheory.lpMeas.aeStronglyMeasurable'

theorem mem_lpMeas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : Lp F p μ) :
    f ∈ lpMeas F 𝕜 m0 p μ :=
  mem_lpMeas_iff_aeStronglyMeasurable'.mpr (Lp.aestronglyMeasurable f)
#align measure_theory.mem_Lp_meas_self MeasureTheory.mem_lpMeas_self

theorem lpMeasSubgroup_coe {m m0 : MeasurableSpace α} {μ : Measure α} {f : lpMeasSubgroup F m p μ} :
    ⇑f = (f : Lp F p μ) :=
  coeFn_coeBase f
#align measure_theory.Lp_meas_subgroup_coe MeasureTheory.lpMeasSubgroup_coe

theorem lpMeas_coe {m m0 : MeasurableSpace α} {μ : Measure α} {f : lpMeas F 𝕜 m p μ} :
    ⇑f = (f : Lp F p μ) :=
  coeFn_coeBase f
#align measure_theory.Lp_meas_coe MeasureTheory.lpMeas_coe

theorem mem_lpMeas_indicatorConstLp {m m0 : MeasurableSpace α} (hm : m ≤ m0) {μ : Measure α}
    {s : Set α} (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {c : F} :
    indicatorConstLp p (hm s hs) hμs c ∈ lpMeas F 𝕜 m p μ :=
  ⟨s.indicator fun x : α => c, (@stronglyMeasurable_const _ _ m _ _).indicator hs,
    indicatorConstLp_coeFn⟩
#align measure_theory.mem_Lp_meas_indicator_const_Lp MeasureTheory.mem_lpMeas_indicatorConstLp

section CompleteSubspace

/-! ## The subspace `Lp_meas` is complete.

We define an `isometry_equiv` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas_subgroup` (and `Lp_meas`). -/


variable {ι : Type _} {m m0 : MeasurableSpace α} {μ : Measure α}

/-- If `f` belongs to `Lp_meas_subgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
theorem memℒp_trim_of_mem_lpMeasSubgroup (hm : m ≤ m0) (f : Lp F p μ)
    (hf_meas : f ∈ lpMeasSubgroup F m p μ) :
    Memℒp (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp hf_meas).some p (μ.trim hm) := by
  have hf : ae_strongly_measurable' m f μ :=
    mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp hf_meas
  let g := hf.some
  obtain ⟨hg, hfg⟩ := hf.some_spec
  change mem_ℒp g p (μ.trim hm)
  refine' ⟨hg.ae_strongly_measurable, _⟩
  have h_snorm_fg : snorm g p (μ.trim hm) = snorm f p μ := by rw [snorm_trim hm hg];
    exact snorm_congr_ae hfg.symm
  rw [h_snorm_fg]
  exact Lp.snorm_lt_top f
#align measure_theory.mem_ℒp_trim_of_mem_Lp_meas_subgroup MeasureTheory.memℒp_trim_of_mem_lpMeasSubgroup

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`Lp_meas_subgroup F m p μ`. -/
theorem mem_lpMeasSubgroup_toLp_of_trim (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    (memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f ∈ lpMeasSubgroup F m p μ := by
  let hf_mem_ℒp := mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)
  rw [mem_Lp_meas_subgroup_iff_ae_strongly_measurable']
  refine' ae_strongly_measurable'.congr _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm
  refine' ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm _
  exact Lp.ae_strongly_measurable f
#align measure_theory.mem_Lp_meas_subgroup_to_Lp_of_trim MeasureTheory.mem_lpMeasSubgroup_toLp_of_trim

variable (F p μ)

/-- Map from `Lp_meas_subgroup` to `Lp F p (μ.trim hm)`. -/
noncomputable def lpMeasSubgroupToLpTrim (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    Lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.Mem).some
    (memℒp_trim_of_mem_lpMeasSubgroup hm f f.Mem)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim MeasureTheory.lpMeasSubgroupToLpTrim

variable (𝕜)

/-- Map from `Lp_meas` to `Lp F p (μ.trim hm)`. -/
noncomputable def lpMeasToLpTrim (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : Lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_lpMeas_iff_aeStronglyMeasurable'.mp f.Mem).some
    (memℒp_trim_of_mem_lpMeasSubgroup hm f f.Mem)
#align measure_theory.Lp_meas_to_Lp_trim MeasureTheory.lpMeasToLpTrim

variable {𝕜}

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas_subgroup`, inverse of
`Lp_meas_subgroup_to_Lp_trim`. -/
noncomputable def lpTrimToLpMeasSubgroup (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpMeasSubgroup F m p μ :=
  ⟨(memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩
#align measure_theory.Lp_trim_to_Lp_meas_subgroup MeasureTheory.lpTrimToLpMeasSubgroup

variable (𝕜)

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas`, inverse of `Lp_meas_to_Lp_trim`. -/
noncomputable def lpTrimToLpMeas (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ :=
  ⟨(memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩
#align measure_theory.Lp_trim_to_Lp_meas MeasureTheory.lpTrimToLpMeas

variable {F 𝕜 p μ}

theorem lpMeasSubgroupToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp (memℒp_trim_of_mem_lpMeasSubgroup hm (↑f) f.Mem))).trans
    (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.Mem).choose_spec.2.symm
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_ae_eq MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq

theorem lpTrimToLpMeasSubgroup_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f :=
  Memℒp.coeFn_toLp _
#align measure_theory.Lp_trim_to_Lp_meas_subgroup_ae_eq MeasureTheory.lpTrimToLpMeasSubgroup_ae_eq

theorem lpMeasToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp (memℒp_trim_of_mem_lpMeasSubgroup hm (↑f) f.Mem))).trans
    (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.Mem).choose_spec.2.symm
#align measure_theory.Lp_meas_to_Lp_trim_ae_eq MeasureTheory.lpMeasToLpTrim_ae_eq

theorem lpTrimToLpMeas_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f :=
  Memℒp.coeFn_toLp _
#align measure_theory.Lp_trim_to_Lp_meas_ae_eq MeasureTheory.lpTrimToLpMeas_ae_eq

/-- `Lp_trim_to_Lp_meas_subgroup` is a right inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem lpMeasSubgroupToLpTrim_right_inv (hm : m ≤ m0) :
    Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  refine'
    ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) (Lp.strongly_measurable _) _
  exact (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_right_inv MeasureTheory.lpMeasSubgroupToLpTrim_right_inv

/-- `Lp_trim_to_Lp_meas_subgroup` is a left inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem lpMeasSubgroupToLpTrim_left_inv (hm : m ≤ m0) :
    Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  ext1
  rw [← Lp_meas_subgroup_coe]
  exact (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _).trans (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_left_inv MeasureTheory.lpMeasSubgroupToLpTrim_left_inv

theorem lpMeasSubgroupToLpTrim_add (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f + g) =
      lpMeasSubgroupToLpTrim F p μ hm f + lpMeasSubgroupToLpTrim F p μ hm g := by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  refine' ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _
  · exact (Lp.strongly_measurable _).add (Lp.strongly_measurable _)
  refine' (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _
  refine'
    eventually_eq.trans _
      (eventually_eq.add (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm
        (Lp_meas_subgroup_to_Lp_trim_ae_eq hm g).symm)
  refine' (Lp.coe_fn_add _ _).trans _
  simp_rw [Lp_meas_subgroup_coe]
  exact eventually_of_forall fun x => by rfl
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_add MeasureTheory.lpMeasSubgroupToLpTrim_add

theorem lpMeasSubgroupToLpTrim_neg (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f := by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_neg _).symm
  refine' ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _
  · exact @strongly_measurable.neg _ _ _ m _ _ _ (Lp.strongly_measurable _)
  refine' (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _
  refine' eventually_eq.trans _ (eventually_eq.neg (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm)
  refine' (Lp.coe_fn_neg _).trans _
  simp_rw [Lp_meas_subgroup_coe]
  exact eventually_of_forall fun x => by rfl
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_neg MeasureTheory.lpMeasSubgroupToLpTrim_neg

theorem lpMeasSubgroupToLpTrim_sub (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f - g) =
      lpMeasSubgroupToLpTrim F p μ hm f - lpMeasSubgroupToLpTrim F p μ hm g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Lp_meas_subgroup_to_Lp_trim_add,
    Lp_meas_subgroup_to_Lp_trim_neg]
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_sub MeasureTheory.lpMeasSubgroupToLpTrim_sub

theorem lpMeasToLpTrim_smul (hm : m ≤ m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f := by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  refine' ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _
  · exact (Lp.strongly_measurable _).const_smul c
  refine' (Lp_meas_to_Lp_trim_ae_eq hm _).trans _
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (Lp_meas_to_Lp_trim_ae_eq hm f).mono fun x hx => _
  rw [Pi.smul_apply, Pi.smul_apply, hx]
  rfl
#align measure_theory.Lp_meas_to_Lp_trim_smul MeasureTheory.lpMeasToLpTrim_smul

/-- `Lp_meas_subgroup_to_Lp_trim` preserves the norm. -/
theorem lpMeasSubgroupToLpTrim_norm_map [hp : Fact (1 ≤ p)] (hm : m ≤ m0)
    (f : lpMeasSubgroup F m p μ) : ‖lpMeasSubgroupToLpTrim F p μ hm f‖ = ‖f‖ := by
  rw [Lp.norm_def, snorm_trim hm (Lp.strongly_measurable _),
    snorm_congr_ae (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _), Lp_meas_subgroup_coe, ← Lp.norm_def]
  congr
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_norm_map MeasureTheory.lpMeasSubgroupToLpTrim_norm_map

theorem isometry_lpMeasSubgroupToLpTrim [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    Isometry (lpMeasSubgroupToLpTrim F p μ hm) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, ← Lp_meas_subgroup_to_Lp_trim_sub, Lp_meas_subgroup_to_Lp_trim_norm_map,
      dist_eq_norm]
#align measure_theory.isometry_Lp_meas_subgroup_to_Lp_trim MeasureTheory.isometry_lpMeasSubgroupToLpTrim

variable (F p μ)

/-- `Lp_meas_subgroup` and `Lp F p (μ.trim hm)` are isometric. -/
noncomputable def lpMeasSubgroupToLpTrimIso [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    lpMeasSubgroup F m p μ ≃ᵢ Lp F p (μ.trim hm) where
  toFun := lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  isometry_toFun := isometry_lpMeasSubgroupToLpTrim hm
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_iso MeasureTheory.lpMeasSubgroupToLpTrimIso

variable (𝕜)

/-- `Lp_meas_subgroup` and `Lp_meas` are isometric. -/
noncomputable def lpMeasSubgroupToLpMeasIso [hp : Fact (1 ≤ p)] :
    lpMeasSubgroup F m p μ ≃ᵢ lpMeas F 𝕜 m p μ :=
  IsometryEquiv.refl (lpMeasSubgroup F m p μ)
#align measure_theory.Lp_meas_subgroup_to_Lp_meas_iso MeasureTheory.lpMeasSubgroupToLpMeasIso

/-- `Lp_meas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence. -/
noncomputable def lpMeasToLpTrimLie [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    lpMeas F 𝕜 m p μ ≃ₗᵢ[𝕜] Lp F p (μ.trim hm) where
  toFun := lpMeasToLpTrim F 𝕜 p μ hm
  invFun := lpTrimToLpMeas F 𝕜 p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  map_add' := lpMeasSubgroupToLpTrim_add hm
  map_smul' := lpMeasToLpTrim_smul hm
  norm_map' := lpMeasSubgroupToLpTrim_norm_map hm
#align measure_theory.Lp_meas_to_Lp_trim_lie MeasureTheory.lpMeasToLpTrimLie

variable {F 𝕜 p μ}

instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] :
    CompleteSpace (lpMeasSubgroup F m p μ) := by
  rw [(Lp_meas_subgroup_to_Lp_trim_iso F p μ hm.elim).completeSpace_iff]; infer_instance

-- For now just no-lint this; lean4's tree-based logging will make this easier to debug.
-- One possible change might be to generalize `𝕜` from `is_R_or_C` to `normed_field`, as this
-- result may well hold there.
@[nolint fails_quickly]
instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] :
    CompleteSpace (lpMeas F 𝕜 m p μ) := by
  rw [(Lp_meas_subgroup_to_Lp_meas_iso F 𝕜 p μ).symm.completeSpace_iff]; infer_instance

theorem isComplete_aeStronglyMeasurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsComplete {f : Lp F p μ | AeStronglyMeasurable' m f μ} := by
  rw [← completeSpace_coe_iff_isComplete]
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  change CompleteSpace (Lp_meas_subgroup F m p μ)
  infer_instance
#align measure_theory.is_complete_ae_strongly_measurable' MeasureTheory.isComplete_aeStronglyMeasurable'

theorem isClosed_aeStronglyMeasurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsClosed {f : Lp F p μ | AeStronglyMeasurable' m f μ} :=
  IsComplete.isClosed (isComplete_aeStronglyMeasurable' hm)
#align measure_theory.is_closed_ae_strongly_measurable' MeasureTheory.isClosed_aeStronglyMeasurable'

end CompleteSubspace

section StronglyMeasurable

variable {m m0 : MeasurableSpace α} {μ : Measure α}

/-- We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`. -/
theorem lpMeas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : ∃ g, FinStronglyMeasurable g (μ.trim hm) ∧ f =ᵐ[μ] g :=
  ⟨lpMeasSubgroupToLpTrim F p μ hm f, Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top,
    (lpMeasSubgroupToLpTrim_ae_eq hm f).symm⟩
#align measure_theory.Lp_meas.ae_fin_strongly_measurable' MeasureTheory.lpMeas.ae_fin_strongly_measurable'

/-- When applying the inverse of `Lp_meas_to_Lp_trim_lie` (which takes a function in the Lp space of
the sub-sigma algebra and returns its version in the larger Lp space) to an indicator of the
sub-sigma-algebra, we obtain an indicator in the Lp space of the larger sigma-algebra. -/
theorem lpMeasToLpTrimLie_symm_indicator [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] {hm : m ≤ m0}
    {s : Set α} {μ : Measure α} (hs : measurable_set[m] s) (hμs : μ.trim hm s ≠ ∞) (c : F) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (indicatorConstLp p hs hμs c) : Lp F p μ) =
      indicatorConstLp p (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).Ne c := by
  ext1
  rw [← Lp_meas_coe]
  change
    Lp_trim_to_Lp_meas F ℝ p μ hm (indicator_const_Lp p hs hμs c) =ᵐ[μ]
      (indicator_const_Lp p _ _ c : α → F)
  refine' (Lp_trim_to_Lp_meas_ae_eq hm _).trans _
  exact (ae_eq_of_ae_eq_trim indicator_const_Lp_coe_fn).trans indicator_const_Lp_coe_fn.symm
#align measure_theory.Lp_meas_to_Lp_trim_lie_symm_indicator MeasureTheory.lpMeasToLpTrimLie_symm_indicator

theorem lpMeasToLpTrimLie_symm_toLp [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] (hm : m ≤ m0)
    (f : α → F) (hf : Memℒp f p (μ.trim hm)) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (hf.toLp f) : Lp F p μ) =
      (memℒp_of_memℒp_trim hm hf).toLp f := by
  ext1
  rw [← Lp_meas_coe]
  refine' (Lp_trim_to_Lp_meas_ae_eq hm _).trans _
  exact (ae_eq_of_ae_eq_trim (mem_ℒp.coe_fn_to_Lp hf)).trans (mem_ℒp.coe_fn_to_Lp _).symm
#align measure_theory.Lp_meas_to_Lp_trim_lie_symm_to_Lp MeasureTheory.lpMeasToLpTrimLie_symm_toLp

end StronglyMeasurable

end LpMeas

section Induction

variable {m m0 : MeasurableSpace α} {μ : Measure α} [Fact (1 ≤ p)] [NormedSpace ℝ F]

/-- Auxiliary lemma for `Lp.induction_strongly_measurable`. -/
@[elab_as_elim]
theorem Lp.induction_strongly_measurable_aux (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
    (h_ind :
      ∀ (c : F) {s : Set α} (hs : measurable_set[m] s) (hμs : μ s < ∞),
        P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.Ne c))
    (h_add :
      ∀ ⦃f g⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            ∀ hfm : AeStronglyMeasurable' m f μ,
              ∀ hgm : AeStronglyMeasurable' m g μ,
                Disjoint (Function.support f) (Function.support g) →
                  P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f}) :
    ∀ f : Lp F p μ, AeStronglyMeasurable' m f μ → P f := by
  intro f hf
  let f' := (⟨f, hf⟩ : Lp_meas F ℝ m p μ)
  let g := Lp_meas_to_Lp_trim_lie F ℝ p μ hm f'
  have hfg : f' = (Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm g := by
    simp only [LinearIsometryEquiv.symm_apply_apply]
  change P ↑f'
  rw [hfg]
  refine'
    @Lp.induction α F m _ p (μ.trim hm) _ hp_ne_top
      (fun g => P ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm g)) _ _ _ g
  · intro b t ht hμt
    rw [Lp.simple_func.coe_indicator_const, Lp_meas_to_Lp_trim_lie_symm_indicator ht hμt.ne b]
    have hμt' : μ t < ∞ := (le_trim hm).trans_lt hμt
    specialize h_ind b ht hμt'
    rwa [Lp.simple_func.coe_indicator_const] at h_ind 
  · intro f g hf hg h_disj hfP hgP
    rw [LinearIsometryEquiv.map_add]
    push_cast
    have h_eq :
      ∀ (f : α → F) (hf : mem_ℒp f p (μ.trim hm)),
        ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm (mem_ℒp.to_Lp f hf) : Lp F p μ) =
          (mem_ℒp_of_mem_ℒp_trim hm hf).toLp f :=
      Lp_meas_to_Lp_trim_lie_symm_to_Lp hm
    rw [h_eq f hf] at hfP ⊢
    rw [h_eq g hg] at hgP ⊢
    exact
      h_add (mem_ℒp_of_mem_ℒp_trim hm hf) (mem_ℒp_of_mem_ℒp_trim hm hg)
        (ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm hf.ae_strongly_measurable)
        (ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm hg.ae_strongly_measurable)
        h_disj hfP hgP
  · change IsClosed ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm ⁻¹' {g : Lp_meas F ℝ m p μ | P ↑g})
    exact IsClosed.preimage (LinearIsometryEquiv.continuous _) h_closed
#align measure_theory.Lp.induction_strongly_measurable_aux MeasureTheory.Lp.induction_strongly_measurable_aux

/-- To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.
-/
@[elab_as_elim]
theorem Lp.induction_stronglyMeasurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
    (h_ind :
      ∀ (c : F) {s : Set α} (hs : measurable_set[m] s) (hμs : μ s < ∞),
        P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.Ne c))
    (h_add :
      ∀ ⦃f g⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            ∀ hfm : strongly_measurable[m] f,
              ∀ hgm : strongly_measurable[m] g,
                Disjoint (Function.support f) (Function.support g) →
                  P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f}) :
    ∀ f : Lp F p μ, AeStronglyMeasurable' m f μ → P f := by
  intro f hf
  suffices h_add_ae :
    ∀ ⦃f g⦄,
      ∀ hf : mem_ℒp f p μ,
        ∀ hg : mem_ℒp g p μ,
          ∀ hfm : ae_strongly_measurable' m f μ,
            ∀ hgm : ae_strongly_measurable' m g μ,
              Disjoint (Function.support f) (Function.support g) →
                P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g)
  exact Lp.induction_strongly_measurable_aux hm hp_ne_top P h_ind h_add_ae h_closed f hf
  intro f g hf hg hfm hgm h_disj hPf hPg
  let s_f : Set α := Function.support (hfm.mk f)
  have hs_f : measurable_set[m] s_f := hfm.strongly_measurable_mk.measurable_set_support
  have hs_f_eq : s_f =ᵐ[μ] Function.support f := hfm.ae_eq_mk.symm.support
  let s_g : Set α := Function.support (hgm.mk g)
  have hs_g : measurable_set[m] s_g := hgm.strongly_measurable_mk.measurable_set_support
  have hs_g_eq : s_g =ᵐ[μ] Function.support g := hgm.ae_eq_mk.symm.support
  have h_inter_empty : (s_f ∩ s_g : Set α) =ᵐ[μ] (∅ : Set α) := by
    refine' (hs_f_eq.inter hs_g_eq).trans _
    suffices Function.support f ∩ Function.support g = ∅ by rw [this]
    exact set.disjoint_iff_inter_eq_empty.mp h_disj
  let f' := (s_f \ s_g).indicator (hfm.mk f)
  have hff' : f =ᵐ[μ] f' := by
    have : s_f \ s_g =ᵐ[μ] s_f := by
      rw [← Set.diff_inter_self_eq_diff, Set.inter_comm]
      refine' ((ae_eq_refl s_f).diffₓ h_inter_empty).trans _
      rw [Set.diff_empty]
    refine' ((indicator_ae_eq_of_ae_eq_set this).trans _).symm
    rw [Set.indicator_support]
    exact hfm.ae_eq_mk.symm
  have hf'_meas : strongly_measurable[m] f' := hfm.strongly_measurable_mk.indicator (hs_f.diff hs_g)
  have hf'_Lp : mem_ℒp f' p μ := hf.ae_eq hff'
  let g' := (s_g \ s_f).indicator (hgm.mk g)
  have hgg' : g =ᵐ[μ] g' := by
    have : s_g \ s_f =ᵐ[μ] s_g := by
      rw [← Set.diff_inter_self_eq_diff]
      refine' ((ae_eq_refl s_g).diffₓ h_inter_empty).trans _
      rw [Set.diff_empty]
    refine' ((indicator_ae_eq_of_ae_eq_set this).trans _).symm
    rw [Set.indicator_support]
    exact hgm.ae_eq_mk.symm
  have hg'_meas : strongly_measurable[m] g' := hgm.strongly_measurable_mk.indicator (hs_g.diff hs_f)
  have hg'_Lp : mem_ℒp g' p μ := hg.ae_eq hgg'
  have h_disj : Disjoint (Function.support f') (Function.support g') :=
    haveI : Disjoint (s_f \ s_g) (s_g \ s_f) := disjoint_sdiff_sdiff
    this.mono Set.support_indicator_subset Set.support_indicator_subset
  rw [← mem_ℒp.to_Lp_congr hf'_Lp hf hff'.symm] at hPf ⊢
  rw [← mem_ℒp.to_Lp_congr hg'_Lp hg hgg'.symm] at hPg ⊢
  exact h_add hf'_Lp hg'_Lp hf'_meas hg'_meas h_disj hPf hPg
#align measure_theory.Lp.induction_strongly_measurable MeasureTheory.Lp.induction_stronglyMeasurable

/-- To prove something for an arbitrary `mem_ℒp` function a.e. strongly measurable with respect
to a sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in the `Lᵖ` space strongly measurable w.r.t. `m` for which the property
  holds is closed.
* the property is closed under the almost-everywhere equal relation.
-/
@[elab_as_elim]
theorem Memℒp.induction_stronglyMeasurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : (α → F) → Prop)
    (h_ind : ∀ (c : F) ⦃s⦄, measurable_set[m] s → μ s < ∞ → P (s.indicator fun _ => c))
    (h_add :
      ∀ ⦃f g : α → F⦄,
        Disjoint (Function.support f) (Function.support g) →
          Memℒp f p μ →
            Memℒp g p μ →
              strongly_measurable[m] f → strongly_measurable[m] g → P f → P g → P (f + g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f})
    (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → Memℒp f p μ → P f → P g) :
    ∀ ⦃f : α → F⦄ (hf : Memℒp f p μ) (hfm : AeStronglyMeasurable' m f μ), P f := by
  intro f hf hfm
  let f_Lp := hf.to_Lp f
  have hfm_Lp : ae_strongly_measurable' m f_Lp μ := hfm.congr hf.coe_fn_to_Lp.symm
  refine' h_ae hf.coe_fn_to_Lp (Lp.mem_ℒp _) _
  change P f_Lp
  refine' Lp.induction_strongly_measurable hm hp_ne_top (fun f => P ⇑f) _ _ h_closed f_Lp hfm_Lp
  · intro c s hs hμs
    rw [Lp.simple_func.coe_indicator_const]
    refine' h_ae indicator_const_Lp_coe_fn.symm _ (h_ind c hs hμs)
    exact mem_ℒp_indicator_const p (hm s hs) c (Or.inr hμs.ne)
  · intro f g hf_mem hg_mem hfm hgm h_disj hfP hgP
    have hfP' : P f := h_ae hf_mem.coe_fn_to_Lp (Lp.mem_ℒp _) hfP
    have hgP' : P g := h_ae hg_mem.coe_fn_to_Lp (Lp.mem_ℒp _) hgP
    specialize h_add h_disj hf_mem hg_mem hfm hgm hfP' hgP'
    refine' h_ae _ (hf_mem.add hg_mem) h_add
    exact (hf_mem.coe_fn_to_Lp.symm.add hg_mem.coe_fn_to_Lp.symm).trans (Lp.coe_fn_add _ _).symm
#align measure_theory.mem_ℒp.induction_strongly_measurable MeasureTheory.Memℒp.induction_stronglyMeasurable

end Induction

end MeasureTheory

