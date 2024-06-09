/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Order.Filter.IndicatorFunction
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

#align_import measure_theory.function.conditional_expectation.ae_measurable from "leanprover-community/mathlib"@"d8bbb04e2d2a44596798a9207ceefc0fb236e41e"

/-! # Functions a.e. measurable with respect to a sub-σ-algebra

A function `f` verifies `AEStronglyMeasurable' m f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `AEStronglyMeasurable`, but the
`MeasurableSpace` structures used for the measurability statement and for the measure are
different.

We define `lpMeas F 𝕜 m p μ`, the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-strongly
measurable function.

## Main statements

We define an `IsometryEquiv` between `lpMeasSubgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of `lpMeas`.

`Lp.induction_stronglyMeasurable` (see also `Memℒp.induction_stronglyMeasurable`):
To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.

-/

set_option linter.uppercaseLean3 false

open TopologicalSpace Filter

open scoped ENNReal MeasureTheory

namespace MeasureTheory

/-- A function `f` verifies `AEStronglyMeasurable' m f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `AEStronglyMeasurable`, but the
`MeasurableSpace` structures used for the measurability statement and for the measure are
different. -/
def AEStronglyMeasurable' {α β} [TopologicalSpace β] (m : MeasurableSpace α)
    {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g : α → β, StronglyMeasurable[m] g ∧ f =ᵐ[μ] g
#align measure_theory.ae_strongly_measurable' MeasureTheory.AEStronglyMeasurable'

namespace AEStronglyMeasurable'

variable {α β 𝕜 : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
  {f g : α → β}

theorem congr (hf : AEStronglyMeasurable' m f μ) (hfg : f =ᵐ[μ] g) :
    AEStronglyMeasurable' m g μ := by
  obtain ⟨f', hf'_meas, hff'⟩ := hf; exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩
#align measure_theory.ae_strongly_measurable'.congr MeasureTheory.AEStronglyMeasurable'.congr

theorem mono {m'} (hf : AEStronglyMeasurable' m f μ) (hm : m ≤ m') :
    AEStronglyMeasurable' m' f μ :=
  let ⟨f', hf'_meas, hff'⟩ := hf; ⟨f', hf'_meas.mono hm, hff'⟩

theorem add [Add β] [ContinuousAdd β] (hf : AEStronglyMeasurable' m f μ)
    (hg : AEStronglyMeasurable' m g μ) : AEStronglyMeasurable' m (f + g) μ := by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  rcases hg with ⟨g', h_g'_meas, hgg'⟩
  exact ⟨f' + g', h_f'_meas.add h_g'_meas, hff'.add hgg'⟩
#align measure_theory.ae_strongly_measurable'.add MeasureTheory.AEStronglyMeasurable'.add

theorem neg [AddGroup β] [TopologicalAddGroup β] {f : α → β} (hfm : AEStronglyMeasurable' m f μ) :
    AEStronglyMeasurable' m (-f) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine ⟨-f', hf'_meas.neg, hf_ae.mono fun x hx => ?_⟩
  simp_rw [Pi.neg_apply]
  rw [hx]
#align measure_theory.ae_strongly_measurable'.neg MeasureTheory.AEStronglyMeasurable'.neg

theorem sub [AddGroup β] [TopologicalAddGroup β] {f g : α → β} (hfm : AEStronglyMeasurable' m f μ)
    (hgm : AEStronglyMeasurable' m g μ) : AEStronglyMeasurable' m (f - g) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  rcases hgm with ⟨g', hg'_meas, hg_ae⟩
  refine ⟨f' - g', hf'_meas.sub hg'_meas, hf_ae.mp (hg_ae.mono fun x hx1 hx2 => ?_)⟩
  simp_rw [Pi.sub_apply]
  rw [hx1, hx2]
#align measure_theory.ae_strongly_measurable'.sub MeasureTheory.AEStronglyMeasurable'.sub

theorem const_smul [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (c : 𝕜) (hf : AEStronglyMeasurable' m f μ) :
    AEStronglyMeasurable' m (c • f) μ := by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  refine ⟨c • f', h_f'_meas.const_smul c, ?_⟩
  exact EventuallyEq.fun_comp hff' fun x => c • x
#align measure_theory.ae_strongly_measurable'.const_smul MeasureTheory.AEStronglyMeasurable'.const_smul

theorem const_inner {𝕜 β} [RCLike 𝕜] [NormedAddCommGroup β] [InnerProductSpace 𝕜 β] {f : α → β}
    (hfm : AEStronglyMeasurable' m f μ) (c : β) :
    AEStronglyMeasurable' m (fun x => (inner c (f x) : 𝕜)) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine
    ⟨fun x => (inner c (f' x) : 𝕜), (@stronglyMeasurable_const _ _ m _ c).inner hf'_meas,
      hf_ae.mono fun x hx => ?_⟩
  dsimp only
  rw [hx]
#align measure_theory.ae_strongly_measurable'.const_inner MeasureTheory.AEStronglyMeasurable'.const_inner

/-- An `m`-strongly measurable function almost everywhere equal to `f`. -/
noncomputable def mk (f : α → β) (hfm : AEStronglyMeasurable' m f μ) : α → β :=
  hfm.choose
#align measure_theory.ae_strongly_measurable'.mk MeasureTheory.AEStronglyMeasurable'.mk

theorem stronglyMeasurable_mk {f : α → β} (hfm : AEStronglyMeasurable' m f μ) :
    StronglyMeasurable[m] (hfm.mk f) :=
  hfm.choose_spec.1
#align measure_theory.ae_strongly_measurable'.stronglyMeasurable_mk MeasureTheory.AEStronglyMeasurable'.stronglyMeasurable_mk

theorem ae_eq_mk {f : α → β} (hfm : AEStronglyMeasurable' m f μ) : f =ᵐ[μ] hfm.mk f :=
  hfm.choose_spec.2
#align measure_theory.ae_strongly_measurable'.ae_eq_mk MeasureTheory.AEStronglyMeasurable'.ae_eq_mk

theorem continuous_comp {γ} [TopologicalSpace γ] {f : α → β} {g : β → γ} (hg : Continuous g)
    (hf : AEStronglyMeasurable' m f μ) : AEStronglyMeasurable' m (g ∘ f) μ :=
  ⟨fun x => g (hf.mk _ x),
    @Continuous.comp_stronglyMeasurable _ _ _ m _ _ _ _ hg hf.stronglyMeasurable_mk,
    hf.ae_eq_mk.mono fun x hx => by rw [Function.comp_apply, hx]⟩
#align measure_theory.ae_strongly_measurable'.continuous_comp MeasureTheory.AEStronglyMeasurable'.continuous_comp

end AEStronglyMeasurable'

theorem aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim {α β} {m m0 m0' : MeasurableSpace α}
    [TopologicalSpace β] (hm0 : m0 ≤ m0') {μ : Measure α} {f : α → β}
    (hf : AEStronglyMeasurable' m f (μ.trim hm0)) : AEStronglyMeasurable' m f μ := by
  obtain ⟨g, hg_meas, hfg⟩ := hf; exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩
#align measure_theory.ae_strongly_measurable'_of_ae_strongly_measurable'_trim MeasureTheory.aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim

theorem StronglyMeasurable.aeStronglyMeasurable' {α β} {m _ : MeasurableSpace α}
    [TopologicalSpace β] {μ : Measure α} {f : α → β} (hf : StronglyMeasurable[m] f) :
    AEStronglyMeasurable' m f μ :=
  ⟨f, hf, ae_eq_refl _⟩
#align measure_theory.strongly_measurable.ae_strongly_measurable' MeasureTheory.StronglyMeasurable.aeStronglyMeasurable'

theorem ae_eq_trim_iff_of_aeStronglyMeasurable' {α β} [TopologicalSpace β] [MetrizableSpace β]
    {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β} (hm : m ≤ m0)
    (hfm : AEStronglyMeasurable' m f μ) (hgm : AEStronglyMeasurable' m g μ) :
    hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (ae_eq_trim_iff hm hfm.stronglyMeasurable_mk hgm.stronglyMeasurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h =>
      hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩
#align measure_theory.ae_eq_trim_iff_of_ae_strongly_measurable' MeasureTheory.ae_eq_trim_iff_of_aeStronglyMeasurable'

theorem AEStronglyMeasurable.comp_ae_measurable' {α β γ : Type*} [TopologicalSpace β]
    {mα : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α → β} {μ : Measure γ} {g : γ → α}
    (hf : AEStronglyMeasurable f (μ.map g)) (hg : AEMeasurable g μ) :
    AEStronglyMeasurable' (mα.comap g) (f ∘ g) μ :=
  ⟨hf.mk f ∘ g, hf.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl),
    ae_eq_comp hg hf.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.comp_ae_measurable' MeasureTheory.AEStronglyMeasurable.comp_ae_measurable'

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable. -/
theorem AEStronglyMeasurable'.aeStronglyMeasurable'_of_measurableSpace_le_on {α E}
    {m m₂ m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace E] [Zero E] (hm : m ≤ m0)
    {s : Set α} {f : α → E} (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) → MeasurableSet[m₂] (s ∩ t))
    (hf : AEStronglyMeasurable' m f μ) (hf_zero : f =ᵐ[μ.restrict sᶜ] 0) :
    AEStronglyMeasurable' m₂ f μ := by
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f := by
    refine Filter.EventuallyEq.trans ?_ <|
      indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero
    filter_upwards [hf.ae_eq_mk] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs, hx]
    · simp [hxs]
  suffices StronglyMeasurable[m₂] (s.indicator (hf.mk f)) from
    AEStronglyMeasurable'.congr this.aeStronglyMeasurable' h_ind_eq
  have hf_ind : StronglyMeasurable[m] (s.indicator (hf.mk f)) :=
    hf.stronglyMeasurable_mk.indicator hs_m
  exact
    hf_ind.stronglyMeasurable_of_measurableSpace_le_on hs_m hs fun x hxs =>
      Set.indicator_of_not_mem hxs _
#align measure_theory.ae_strongly_measurable'.ae_strongly_measurable'_of_measurable_space_le_on MeasureTheory.AEStronglyMeasurable'.aeStronglyMeasurable'_of_measurableSpace_le_on

variable {α E' F F' 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
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

/-! ## The subset `lpMeas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable (F)

/-- `lpMeasSubgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    AddSubgroup (Lp F p μ) where
  carrier := {f : Lp F p μ | AEStronglyMeasurable' m f μ}
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  neg_mem' {f} hf := AEStronglyMeasurable'.congr hf.neg (Lp.coeFn_neg f).symm
#align measure_theory.Lp_meas_subgroup MeasureTheory.lpMeasSubgroup

variable (𝕜)

/-- `lpMeas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeas (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    Submodule 𝕜 (Lp F p μ) where
  carrier := {f : Lp F p μ | AEStronglyMeasurable' m f μ}
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.const_smul c).congr (Lp.coeFn_smul c f).symm
#align measure_theory.Lp_meas MeasureTheory.lpMeas

variable {F 𝕜}

theorem mem_lpMeasSubgroup_iff_aeStronglyMeasurable' {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f ∈ lpMeasSubgroup F m p μ ↔ AEStronglyMeasurable' m f μ := by
  rw [← AddSubgroup.mem_carrier, lpMeasSubgroup, Set.mem_setOf_eq]
#align measure_theory.mem_Lp_meas_subgroup_iff_ae_strongly_measurable' MeasureTheory.mem_lpMeasSubgroup_iff_aeStronglyMeasurable'

theorem mem_lpMeas_iff_aeStronglyMeasurable' {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f ∈ lpMeas F 𝕜 m p μ ↔ AEStronglyMeasurable' m f μ := by
  rw [← SetLike.mem_coe, ← Submodule.mem_carrier, lpMeas, Set.mem_setOf_eq]
#align measure_theory.mem_Lp_meas_iff_ae_strongly_measurable' MeasureTheory.mem_lpMeas_iff_aeStronglyMeasurable'

theorem lpMeas.aeStronglyMeasurable' {m _ : MeasurableSpace α} {μ : Measure α}
    (f : lpMeas F 𝕜 m p μ) : AEStronglyMeasurable' (β := F) m f μ :=
  mem_lpMeas_iff_aeStronglyMeasurable'.mp f.mem
#align measure_theory.Lp_meas.ae_strongly_measurable' MeasureTheory.lpMeas.aeStronglyMeasurable'

theorem mem_lpMeas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : Lp F p μ) :
    f ∈ lpMeas F 𝕜 m0 p μ :=
  mem_lpMeas_iff_aeStronglyMeasurable'.mpr (Lp.aestronglyMeasurable f)
#align measure_theory.mem_Lp_meas_self MeasureTheory.mem_lpMeas_self

theorem lpMeasSubgroup_coe {m _ : MeasurableSpace α} {μ : Measure α} {f : lpMeasSubgroup F m p μ} :
    (f : _ → _) = (f : Lp F p μ) :=
  rfl
#align measure_theory.Lp_meas_subgroup_coe MeasureTheory.lpMeasSubgroup_coe

theorem lpMeas_coe {m _ : MeasurableSpace α} {μ : Measure α} {f : lpMeas F 𝕜 m p μ} :
    (f : _ → _) = (f : Lp F p μ) :=
  rfl
#align measure_theory.Lp_meas_coe MeasureTheory.lpMeas_coe

theorem mem_lpMeas_indicatorConstLp {m m0 : MeasurableSpace α} (hm : m ≤ m0) {μ : Measure α}
    {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) {c : F} :
    indicatorConstLp p (hm s hs) hμs c ∈ lpMeas F 𝕜 m p μ :=
  ⟨s.indicator fun _ : α => c, (@stronglyMeasurable_const _ _ m _ _).indicator hs,
    indicatorConstLp_coeFn⟩
#align measure_theory.mem_Lp_meas_indicator_const_Lp MeasureTheory.mem_lpMeas_indicatorConstLp

section CompleteSubspace

/-! ## The subspace `lpMeas` is complete.

We define an `IsometryEquiv` between `lpMeasSubgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`lpMeasSubgroup` (and `lpMeas`). -/


variable {ι : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

/-- If `f` belongs to `lpMeasSubgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `AEMeasurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
theorem memℒp_trim_of_mem_lpMeasSubgroup (hm : m ≤ m0) (f : Lp F p μ)
    (hf_meas : f ∈ lpMeasSubgroup F m p μ) :
    Memℒp (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp hf_meas).choose p (μ.trim hm) := by
  have hf : AEStronglyMeasurable' m f μ :=
    mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp hf_meas
  let g := hf.choose
  obtain ⟨hg, hfg⟩ := hf.choose_spec
  change Memℒp g p (μ.trim hm)
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  have h_snorm_fg : snorm g p (μ.trim hm) = snorm f p μ := by
    rw [snorm_trim hm hg]
    exact snorm_congr_ae hfg.symm
  rw [h_snorm_fg]
  exact Lp.snorm_lt_top f
#align measure_theory.mem_ℒp_trim_of_mem_Lp_meas_subgroup MeasureTheory.memℒp_trim_of_mem_lpMeasSubgroup

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`lpMeasSubgroup F m p μ`. -/
theorem mem_lpMeasSubgroup_toLp_of_trim (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    (memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f ∈ lpMeasSubgroup F m p μ := by
  let hf_mem_ℒp := memℒp_of_memℒp_trim hm (Lp.memℒp f)
  rw [mem_lpMeasSubgroup_iff_aeStronglyMeasurable']
  refine AEStronglyMeasurable'.congr ?_ (Memℒp.coeFn_toLp hf_mem_ℒp).symm
  refine aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim hm ?_
  exact Lp.aestronglyMeasurable f
#align measure_theory.mem_Lp_meas_subgroup_to_Lp_of_trim MeasureTheory.mem_lpMeasSubgroup_toLp_of_trim

variable (F p μ)

/-- Map from `lpMeasSubgroup` to `Lp F p (μ.trim hm)`. -/
noncomputable def lpMeasSubgroupToLpTrim (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    Lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.mem).choose
    -- Porting note: had to replace `f` with `f.1` here.
    (memℒp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim MeasureTheory.lpMeasSubgroupToLpTrim

variable (𝕜)

/-- Map from `lpMeas` to `Lp F p (μ.trim hm)`. -/
noncomputable def lpMeasToLpTrim (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : Lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_lpMeas_iff_aeStronglyMeasurable'.mp f.mem).choose
    -- Porting note: had to replace `f` with `f.1` here.
    (memℒp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)
#align measure_theory.Lp_meas_to_Lp_trim MeasureTheory.lpMeasToLpTrim

variable {𝕜}

/-- Map from `Lp F p (μ.trim hm)` to `lpMeasSubgroup`, inverse of
`lpMeasSubgroupToLpTrim`. -/
noncomputable def lpTrimToLpMeasSubgroup (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpMeasSubgroup F m p μ :=
  ⟨(memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩
#align measure_theory.Lp_trim_to_Lp_meas_subgroup MeasureTheory.lpTrimToLpMeasSubgroup

variable (𝕜)

/-- Map from `Lp F p (μ.trim hm)` to `lpMeas`, inverse of `Lp_meas_to_Lp_trim`. -/
noncomputable def lpTrimToLpMeas (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ :=
  ⟨(memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩
#align measure_theory.Lp_trim_to_Lp_meas MeasureTheory.lpTrimToLpMeas

variable {F 𝕜 p μ}

theorem lpMeasSubgroupToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f :=
  -- Porting note: replaced `(↑f)` with `f.1` here.
  (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp (memℒp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.mem).choose_spec.2.symm
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_ae_eq MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq

theorem lpTrimToLpMeasSubgroup_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f :=
  -- Porting note: filled in the argument
  Memℒp.coeFn_toLp (memℒp_of_memℒp_trim hm (Lp.memℒp f))
#align measure_theory.Lp_trim_to_Lp_meas_subgroup_ae_eq MeasureTheory.lpTrimToLpMeasSubgroup_ae_eq

theorem lpMeasToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f :=
  -- Porting note: replaced `(↑f)` with `f.1` here.
  (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp (memℒp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.mem).choose_spec.2.symm
#align measure_theory.Lp_meas_to_Lp_trim_ae_eq MeasureTheory.lpMeasToLpTrim_ae_eq

theorem lpTrimToLpMeas_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f :=
  -- Porting note: filled in the argument
  Memℒp.coeFn_toLp (memℒp_of_memℒp_trim hm (Lp.memℒp f))
#align measure_theory.Lp_trim_to_Lp_meas_ae_eq MeasureTheory.lpTrimToLpMeas_ae_eq

/-- `lpTrimToLpMeasSubgroup` is a right inverse of `lpMeasSubgroupToLpTrim`. -/
theorem lpMeasSubgroupToLpTrim_right_inv (hm : m ≤ m0) :
    Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  refine
    ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) (Lp.stronglyMeasurable _) ?_
  exact (lpMeasSubgroupToLpTrim_ae_eq hm _).trans (lpTrimToLpMeasSubgroup_ae_eq hm _)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_right_inv MeasureTheory.lpMeasSubgroupToLpTrim_right_inv

/-- `lpTrimToLpMeasSubgroup` is a left inverse of `lpMeasSubgroupToLpTrim`. -/
theorem lpMeasSubgroupToLpTrim_left_inv (hm : m ≤ m0) :
    Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  ext1
  rw [← lpMeasSubgroup_coe]
  exact (lpTrimToLpMeasSubgroup_ae_eq hm _).trans (lpMeasSubgroupToLpTrim_ae_eq hm _)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_left_inv MeasureTheory.lpMeasSubgroupToLpTrim_left_inv

theorem lpMeasSubgroupToLpTrim_add (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f + g) =
      lpMeasSubgroupToLpTrim F p μ hm f + lpMeasSubgroupToLpTrim F p μ hm g := by
  ext1
  refine EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  refine ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) ?_ ?_
  · exact (Lp.stronglyMeasurable _).add (Lp.stronglyMeasurable _)
  refine (lpMeasSubgroupToLpTrim_ae_eq hm _).trans ?_
  refine
    EventuallyEq.trans ?_
      (EventuallyEq.add (lpMeasSubgroupToLpTrim_ae_eq hm f).symm
        (lpMeasSubgroupToLpTrim_ae_eq hm g).symm)
  refine (Lp.coeFn_add _ _).trans ?_
  simp_rw [lpMeasSubgroup_coe]
  filter_upwards with x using rfl
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_add MeasureTheory.lpMeasSubgroupToLpTrim_add

theorem lpMeasSubgroupToLpTrim_neg (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f := by
  ext1
  refine EventuallyEq.trans ?_ (Lp.coeFn_neg _).symm
  refine ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) ?_ ?_
  · exact @StronglyMeasurable.neg _ _ _ m _ _ _ (Lp.stronglyMeasurable _)
  refine (lpMeasSubgroupToLpTrim_ae_eq hm _).trans ?_
  refine EventuallyEq.trans ?_ (EventuallyEq.neg (lpMeasSubgroupToLpTrim_ae_eq hm f).symm)
  refine (Lp.coeFn_neg _).trans ?_
  simp_rw [lpMeasSubgroup_coe]
  exact eventually_of_forall fun x => by rfl
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_neg MeasureTheory.lpMeasSubgroupToLpTrim_neg

theorem lpMeasSubgroupToLpTrim_sub (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f - g) =
      lpMeasSubgroupToLpTrim F p μ hm f - lpMeasSubgroupToLpTrim F p μ hm g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, lpMeasSubgroupToLpTrim_add,
    lpMeasSubgroupToLpTrim_neg]
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_sub MeasureTheory.lpMeasSubgroupToLpTrim_sub

theorem lpMeasToLpTrim_smul (hm : m ≤ m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f := by
  ext1
  refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  refine ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) ?_ ?_
  · exact (Lp.stronglyMeasurable _).const_smul c
  refine (lpMeasToLpTrim_ae_eq hm _).trans ?_
  refine (Lp.coeFn_smul _ _).trans ?_
  refine (lpMeasToLpTrim_ae_eq hm f).mono fun x hx => ?_
  simp only [Pi.smul_apply, hx]
#align measure_theory.Lp_meas_to_Lp_trim_smul MeasureTheory.lpMeasToLpTrim_smul

/-- `lpMeasSubgroupToLpTrim` preserves the norm. -/
theorem lpMeasSubgroupToLpTrim_norm_map [hp : Fact (1 ≤ p)] (hm : m ≤ m0)
    (f : lpMeasSubgroup F m p μ) : ‖lpMeasSubgroupToLpTrim F p μ hm f‖ = ‖f‖ := by
  rw [Lp.norm_def, snorm_trim hm (Lp.stronglyMeasurable _),
    snorm_congr_ae (lpMeasSubgroupToLpTrim_ae_eq hm _), lpMeasSubgroup_coe, ← Lp.norm_def]
  congr
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_norm_map MeasureTheory.lpMeasSubgroupToLpTrim_norm_map

theorem isometry_lpMeasSubgroupToLpTrim [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    Isometry (lpMeasSubgroupToLpTrim F p μ hm) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, ← lpMeasSubgroupToLpTrim_sub, lpMeasSubgroupToLpTrim_norm_map,
      dist_eq_norm]
#align measure_theory.isometry_Lp_meas_subgroup_to_Lp_trim MeasureTheory.isometry_lpMeasSubgroupToLpTrim

variable (F p μ)

/-- `lpMeasSubgroup` and `Lp F p (μ.trim hm)` are isometric. -/
noncomputable def lpMeasSubgroupToLpTrimIso [Fact (1 ≤ p)] (hm : m ≤ m0) :
    lpMeasSubgroup F m p μ ≃ᵢ Lp F p (μ.trim hm) where
  toFun := lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  isometry_toFun := isometry_lpMeasSubgroupToLpTrim hm
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_iso MeasureTheory.lpMeasSubgroupToLpTrimIso

variable (𝕜)

/-- `lpMeasSubgroup` and `lpMeas` are isometric. -/
noncomputable def lpMeasSubgroupToLpMeasIso [Fact (1 ≤ p)] :
    lpMeasSubgroup F m p μ ≃ᵢ lpMeas F 𝕜 m p μ :=
  IsometryEquiv.refl (lpMeasSubgroup F m p μ)
#align measure_theory.Lp_meas_subgroup_to_Lp_meas_iso MeasureTheory.lpMeasSubgroupToLpMeasIso

/-- `lpMeas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence. -/
noncomputable def lpMeasToLpTrimLie [Fact (1 ≤ p)] (hm : m ≤ m0) :
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
  rw [(lpMeasSubgroupToLpTrimIso F p μ hm.elim).completeSpace_iff]; infer_instance

-- For now just no-lint this; lean4's tree-based logging will make this easier to debug.
-- One possible change might be to generalize `𝕜` from `RCLike` to `NormedField`, as this
-- result may well hold there.
-- Porting note: removed @[nolint fails_quickly]
instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] :
    CompleteSpace (lpMeas F 𝕜 m p μ) := by
  rw [(lpMeasSubgroupToLpMeasIso F 𝕜 p μ).symm.completeSpace_iff]; infer_instance

theorem isComplete_aeStronglyMeasurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsComplete {f : Lp F p μ | AEStronglyMeasurable' m f μ} := by
  rw [← completeSpace_coe_iff_isComplete]
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  change CompleteSpace (lpMeasSubgroup F m p μ)
  infer_instance
#align measure_theory.is_complete_ae_strongly_measurable' MeasureTheory.isComplete_aeStronglyMeasurable'

theorem isClosed_aeStronglyMeasurable' [Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsClosed {f : Lp F p μ | AEStronglyMeasurable' m f μ} :=
  IsComplete.isClosed (isComplete_aeStronglyMeasurable' hm)
#align measure_theory.is_closed_ae_strongly_measurable' MeasureTheory.isClosed_aeStronglyMeasurable'

end CompleteSubspace

section StronglyMeasurable

variable {m m0 : MeasurableSpace α} {μ : Measure α}

/-- We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`. -/
theorem lpMeas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) :
    -- Porting note: changed `f` to `f.1` in the next line. Not certain this is okay.
    ∃ g, FinStronglyMeasurable g (μ.trim hm) ∧ f.1 =ᵐ[μ] g :=
  ⟨lpMeasSubgroupToLpTrim F p μ hm f, Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top,
    (lpMeasSubgroupToLpTrim_ae_eq hm f).symm⟩
#align measure_theory.Lp_meas.ae_fin_strongly_measurable' MeasureTheory.lpMeas.ae_fin_strongly_measurable'

/-- When applying the inverse of `lpMeasToLpTrimLie` (which takes a function in the Lp space of
the sub-sigma algebra and returns its version in the larger Lp space) to an indicator of the
sub-sigma-algebra, we obtain an indicator in the Lp space of the larger sigma-algebra. -/
theorem lpMeasToLpTrimLie_symm_indicator [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] {hm : m ≤ m0}
    {s : Set α} {μ : Measure α} (hs : MeasurableSet[m] s) (hμs : μ.trim hm s ≠ ∞) (c : F) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (indicatorConstLp p hs hμs c) : Lp F p μ) =
      indicatorConstLp p (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).ne c := by
  ext1
  rw [← lpMeas_coe]
  change
    lpTrimToLpMeas F ℝ p μ hm (indicatorConstLp p hs hμs c) =ᵐ[μ]
      (indicatorConstLp p _ _ c : α → F)
  refine (lpTrimToLpMeas_ae_eq hm _).trans ?_
  exact (ae_eq_of_ae_eq_trim indicatorConstLp_coeFn).trans indicatorConstLp_coeFn.symm
#align measure_theory.Lp_meas_to_Lp_trim_lie_symm_indicator MeasureTheory.lpMeasToLpTrimLie_symm_indicator

theorem lpMeasToLpTrimLie_symm_toLp [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] (hm : m ≤ m0)
    (f : α → F) (hf : Memℒp f p (μ.trim hm)) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (hf.toLp f) : Lp F p μ) =
      (memℒp_of_memℒp_trim hm hf).toLp f := by
  ext1
  rw [← lpMeas_coe]
  refine (lpTrimToLpMeas_ae_eq hm _).trans ?_
  exact (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp hf)).trans (Memℒp.coeFn_toLp _).symm
#align measure_theory.Lp_meas_to_Lp_trim_lie_symm_to_Lp MeasureTheory.lpMeasToLpTrimLie_symm_toLp

end StronglyMeasurable

end LpMeas

section Induction

variable {m m0 : MeasurableSpace α} {μ : Measure α} [Fact (1 ≤ p)] [NormedSpace ℝ F]

/-- Auxiliary lemma for `Lp.induction_stronglyMeasurable`. -/
@[elab_as_elim]
theorem Lp.induction_stronglyMeasurable_aux (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
    (h_ind : ∀ (c : F) {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s < ∞),
      P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add : ∀ ⦃f g⦄, ∀ hf : Memℒp f p μ, ∀ hg : Memℒp g p μ, AEStronglyMeasurable' m f μ →
      AEStronglyMeasurable' m g μ → Disjoint (Function.support f) (Function.support g) →
        P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f}) :
    ∀ f : Lp F p μ, AEStronglyMeasurable' m f μ → P f := by
  intro f hf
  let f' := (⟨f, hf⟩ : lpMeas F ℝ m p μ)
  let g := lpMeasToLpTrimLie F ℝ p μ hm f'
  have hfg : f' = (lpMeasToLpTrimLie F ℝ p μ hm).symm g := by
    simp only [f', g, LinearIsometryEquiv.symm_apply_apply]
  change P ↑f'
  rw [hfg]
  refine
    @Lp.induction α F m _ p (μ.trim hm) _ hp_ne_top
      (fun g => P ((lpMeasToLpTrimLie F ℝ p μ hm).symm g)) ?_ ?_ ?_ g
  · intro b t ht hμt
    -- Porting note: needed to pass `m` to `Lp.simpleFunc.coe_indicatorConst` to avoid
    -- synthesized type class instance is not definitionally equal to expression inferred by typing
    -- rules, synthesized m0 inferred m
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m, lpMeasToLpTrimLie_symm_indicator ht hμt.ne b]
    have hμt' : μ t < ∞ := (le_trim hm).trans_lt hμt
    specialize h_ind b ht hμt'
    rwa [Lp.simpleFunc.coe_indicatorConst] at h_ind
  · intro f g hf hg h_disj hfP hgP
    rw [LinearIsometryEquiv.map_add]
    push_cast
    have h_eq :
      ∀ (f : α → F) (hf : Memℒp f p (μ.trim hm)),
        ((lpMeasToLpTrimLie F ℝ p μ hm).symm (Memℒp.toLp f hf) : Lp F p μ) =
          (memℒp_of_memℒp_trim hm hf).toLp f :=
      lpMeasToLpTrimLie_symm_toLp hm
    rw [h_eq f hf] at hfP ⊢
    rw [h_eq g hg] at hgP ⊢
    exact
      h_add (memℒp_of_memℒp_trim hm hf) (memℒp_of_memℒp_trim hm hg)
        (aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim hm hf.aestronglyMeasurable)
        (aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim hm hg.aestronglyMeasurable)
        h_disj hfP hgP
  · change IsClosed ((lpMeasToLpTrimLie F ℝ p μ hm).symm ⁻¹' {g : lpMeas F ℝ m p μ | P ↑g})
    exact IsClosed.preimage (LinearIsometryEquiv.continuous _) h_closed
#align measure_theory.Lp.induction_strongly_measurable_aux MeasureTheory.Lp.induction_stronglyMeasurable_aux

/-- To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.
-/
@[elab_as_elim]
theorem Lp.induction_stronglyMeasurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
    (h_ind : ∀ (c : F) {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s < ∞),
      P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add : ∀ ⦃f g⦄, ∀ hf : Memℒp f p μ, ∀ hg : Memℒp g p μ, StronglyMeasurable[m] f →
      StronglyMeasurable[m] g → Disjoint (Function.support f) (Function.support g) →
        P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f}) :
    ∀ f : Lp F p μ, AEStronglyMeasurable' m f μ → P f := by
  intro f hf
  suffices h_add_ae :
    ∀ ⦃f g⦄, ∀ hf : Memℒp f p μ, ∀ hg : Memℒp g p μ, AEStronglyMeasurable' m f μ →
      AEStronglyMeasurable' m g μ → Disjoint (Function.support f) (Function.support g) →
        P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g) from
  -- Porting note: `P` should be an explicit argument to `Lp.induction_stronglyMeasurable_aux`, but
  -- it isn't?
    Lp.induction_stronglyMeasurable_aux hm hp_ne_top h_ind h_add_ae h_closed f hf
  intro f g hf hg hfm hgm h_disj hPf hPg
  let s_f : Set α := Function.support (hfm.mk f)
  have hs_f : MeasurableSet[m] s_f := hfm.stronglyMeasurable_mk.measurableSet_support
  have hs_f_eq : s_f =ᵐ[μ] Function.support f := hfm.ae_eq_mk.symm.support
  let s_g : Set α := Function.support (hgm.mk g)
  have hs_g : MeasurableSet[m] s_g := hgm.stronglyMeasurable_mk.measurableSet_support
  have hs_g_eq : s_g =ᵐ[μ] Function.support g := hgm.ae_eq_mk.symm.support
  have h_inter_empty : (s_f ∩ s_g : Set α) =ᵐ[μ] (∅ : Set α) := by
    refine (hs_f_eq.inter hs_g_eq).trans ?_
    suffices Function.support f ∩ Function.support g = ∅ by rw [this]
    exact Set.disjoint_iff_inter_eq_empty.mp h_disj
  let f' := (s_f \ s_g).indicator (hfm.mk f)
  have hff' : f =ᵐ[μ] f' := by
    have : s_f \ s_g =ᵐ[μ] s_f := by
      rw [← Set.diff_inter_self_eq_diff, Set.inter_comm]
      refine ((ae_eq_refl s_f).diff h_inter_empty).trans ?_
      rw [Set.diff_empty]
    refine ((indicator_ae_eq_of_ae_eq_set this).trans ?_).symm
    rw [Set.indicator_support]
    exact hfm.ae_eq_mk.symm
  have hf'_meas : StronglyMeasurable[m] f' := hfm.stronglyMeasurable_mk.indicator (hs_f.diff hs_g)
  have hf'_Lp : Memℒp f' p μ := hf.ae_eq hff'
  let g' := (s_g \ s_f).indicator (hgm.mk g)
  have hgg' : g =ᵐ[μ] g' := by
    have : s_g \ s_f =ᵐ[μ] s_g := by
      rw [← Set.diff_inter_self_eq_diff]
      refine ((ae_eq_refl s_g).diff h_inter_empty).trans ?_
      rw [Set.diff_empty]
    refine ((indicator_ae_eq_of_ae_eq_set this).trans ?_).symm
    rw [Set.indicator_support]
    exact hgm.ae_eq_mk.symm
  have hg'_meas : StronglyMeasurable[m] g' := hgm.stronglyMeasurable_mk.indicator (hs_g.diff hs_f)
  have hg'_Lp : Memℒp g' p μ := hg.ae_eq hgg'
  have h_disj : Disjoint (Function.support f') (Function.support g') :=
    haveI : Disjoint (s_f \ s_g) (s_g \ s_f) := disjoint_sdiff_sdiff
    this.mono Set.support_indicator_subset Set.support_indicator_subset
  rw [← Memℒp.toLp_congr hf'_Lp hf hff'.symm] at hPf ⊢
  rw [← Memℒp.toLp_congr hg'_Lp hg hgg'.symm] at hPg ⊢
  exact h_add hf'_Lp hg'_Lp hf'_meas hg'_meas h_disj hPf hPg
#align measure_theory.Lp.induction_strongly_measurable MeasureTheory.Lp.induction_stronglyMeasurable

/-- To prove something for an arbitrary `Memℒp` function a.e. strongly measurable with respect
to a sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in the `Lᵖ` space strongly measurable w.r.t. `m` for which the property
  holds is closed.
* the property is closed under the almost-everywhere equal relation.
-/
@[elab_as_elim]
theorem Memℒp.induction_stronglyMeasurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : (α → F) → Prop)
    (h_ind : ∀ (c : F) ⦃s⦄, MeasurableSet[m] s → μ s < ∞ → P (s.indicator fun _ => c))
    (h_add : ∀ ⦃f g : α → F⦄, Disjoint (Function.support f) (Function.support g) →
      Memℒp f p μ → Memℒp g p μ → StronglyMeasurable[m] f → StronglyMeasurable[m] g →
        P f → P g → P (f + g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f})
    (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → Memℒp f p μ → P f → P g) :
    ∀ ⦃f : α → F⦄, Memℒp f p μ → AEStronglyMeasurable' m f μ → P f := by
  intro f hf hfm
  let f_Lp := hf.toLp f
  have hfm_Lp : AEStronglyMeasurable' m f_Lp μ := hfm.congr hf.coeFn_toLp.symm
  refine h_ae hf.coeFn_toLp (Lp.memℒp _) ?_
  change P f_Lp
  -- Porting note: `P` should be an explicit argument to `Lp.induction_stronglyMeasurable`, but
  -- it isn't?
  refine Lp.induction_stronglyMeasurable hm hp_ne_top (P := fun f => P f) ?_ ?_ h_closed f_Lp hfm_Lp
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    refine h_ae indicatorConstLp_coeFn.symm ?_ (h_ind c hs hμs)
    exact memℒp_indicator_const p (hm s hs) c (Or.inr hμs.ne)
  · intro f g hf_mem hg_mem hfm hgm h_disj hfP hgP
    have hfP' : P f := h_ae hf_mem.coeFn_toLp (Lp.memℒp _) hfP
    have hgP' : P g := h_ae hg_mem.coeFn_toLp (Lp.memℒp _) hgP
    specialize h_add h_disj hf_mem hg_mem hfm hgm hfP' hgP'
    refine h_ae ?_ (hf_mem.add hg_mem) h_add
    exact (hf_mem.coeFn_toLp.symm.add hg_mem.coeFn_toLp.symm).trans (Lp.coeFn_add _ _).symm
#align measure_theory.mem_ℒp.induction_strongly_measurable MeasureTheory.Memℒp.induction_stronglyMeasurable

end Induction

end MeasureTheory
