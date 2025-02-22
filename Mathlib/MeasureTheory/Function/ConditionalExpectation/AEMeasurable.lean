/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-! # Functions a.e. measurable with respect to a sub-σ-algebra

A function `f` verifies `AEStronglyMeasurable[m] f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `AEStronglyMeasurable`, but the
`MeasurableSpace` structures used for the measurability statement and for the measure are
different.

We define `lpMeas F 𝕜 m p μ`, the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-strongly
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


open TopologicalSpace Filter

open scoped ENNReal MeasureTheory

namespace MeasureTheory

/-- A function `f` verifies `AEStronglyMeasurable[m] f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `AEStronglyMeasurable`, but the
`MeasurableSpace` structures used for the measurability statement and for the measure are
different. -/
@[deprecated AEStronglyMeasurable (since := "2025-01-23")]
def AEStronglyMeasurable' {α β} [TopologicalSpace β] (m : MeasurableSpace α)
    {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop := AEStronglyMeasurable[m] f μ

set_option linter.deprecated false

namespace AEStronglyMeasurable'

variable {α β 𝕜 : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
  {f g : α → β}

@[deprecated AEStronglyMeasurable.congr (since := "2025-01-23")]
theorem congr (hf : AEStronglyMeasurable[m] f μ) (hfg : f =ᵐ[μ] g) :
    AEStronglyMeasurable[m] g μ := AEStronglyMeasurable.congr hf hfg

@[deprecated AEStronglyMeasurable.mono (since := "2025-01-23")]
theorem mono {m'} (hf : AEStronglyMeasurable[m] f μ) (hm : m ≤ m') :
    AEStronglyMeasurable' m' f μ := AEStronglyMeasurable.mono hm hf

@[deprecated AEStronglyMeasurable.add (since := "2025-01-23")]
theorem add [Add β] [ContinuousAdd β] (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f + g) μ :=
  AEStronglyMeasurable.add hf hg

@[deprecated AEStronglyMeasurable.neg (since := "2025-01-23")]
theorem neg [AddGroup β] [ContinuousNeg β] {f : α → β} (hfm : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (-f) μ :=
  AEStronglyMeasurable.neg hfm

@[deprecated AEStronglyMeasurable.sub (since := "2025-01-23")]
theorem sub [AddGroup β] [TopologicalAddGroup β] {f g : α → β} (hfm : AEStronglyMeasurable[m] f μ)
    (hgm : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f - g) μ :=
  AEStronglyMeasurable.sub hfm hgm

@[deprecated AEStronglyMeasurable.const_smul (since := "2025-01-23")]
theorem const_smul [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (c : 𝕜) (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (c • f) μ :=
  AEStronglyMeasurable.const_smul hf _

@[deprecated AEStronglyMeasurable.const_inner (since := "2025-01-23")]
theorem const_inner {𝕜 β} [RCLike 𝕜] [NormedAddCommGroup β] [InnerProductSpace 𝕜 β] {f : α → β}
    (hfm : AEStronglyMeasurable[m] f μ) (c : β) :
    AEStronglyMeasurable[m] (fun x => (inner c (f x) : 𝕜)) μ :=
  AEStronglyMeasurable.const_inner hfm

@[deprecated AEStronglyMeasurable.of_subsingleton_cod (since := "2025-01-23")]
theorem of_subsingleton [Subsingleton β] : AEStronglyMeasurable[m] f μ := .of_subsingleton_cod

@[deprecated AEStronglyMeasurable.of_subsingleton_dom (since := "2025-01-23")]
theorem of_subsingleton' [Subsingleton α] : AEStronglyMeasurable[m] f μ := .of_subsingleton_dom

/-- An `m`-strongly measurable function almost everywhere equal to `f`. -/
@[deprecated AEStronglyMeasurable.mk (since := "2025-01-23")]
noncomputable def mk (f : α → β) (hfm : AEStronglyMeasurable[m] f μ) : α → β :=
  AEStronglyMeasurable.mk f hfm

@[deprecated AEStronglyMeasurable.stronglyMeasurable_mk (since := "2025-01-23")]
theorem stronglyMeasurable_mk {f : α → β} (hfm : AEStronglyMeasurable[m] f μ) :
    StronglyMeasurable[m] (hfm.mk f) :=
  AEStronglyMeasurable.stronglyMeasurable_mk hfm

@[deprecated AEStronglyMeasurable.ae_eq_mk (since := "2025-01-23")]
theorem ae_eq_mk {f : α → β} (hfm : AEStronglyMeasurable[m] f μ) : f =ᵐ[μ] hfm.mk f :=
  AEStronglyMeasurable.ae_eq_mk hfm

@[deprecated Continuous.comp_aestronglyMeasurable (since := "2025-01-23")]
theorem continuous_comp {γ} [TopologicalSpace γ] {f : α → β} {g : β → γ} (hg : Continuous g)
    (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (g ∘ f) μ :=
  hg.comp_aestronglyMeasurable hf

end AEStronglyMeasurable'

@[deprecated AEStronglyMeasurable.of_trim (since := "2025-01-23")]
theorem aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim {α β} {m m0 m0' : MeasurableSpace α}
    [TopologicalSpace β] (hm0 : m0 ≤ m0') {μ : Measure α} {f : α → β}
    (hf : AEStronglyMeasurable[m] f (μ.trim hm0)) : AEStronglyMeasurable[m] f μ := .of_trim hm0 hf

@[deprecated StronglyMeasurable.aestronglyMeasurable (since := "2025-01-23")]
theorem StronglyMeasurable.aeStronglyMeasurable' {α β} {m _ : MeasurableSpace α}
    [TopologicalSpace β] {μ : Measure α} {f : α → β} (hf : StronglyMeasurable[m] f) :
    AEStronglyMeasurable[m] f μ := hf.aestronglyMeasurable

theorem ae_eq_trim_iff_of_aeStronglyMeasurable' {α β} [TopologicalSpace β] [MetrizableSpace β]
    {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β} (hm : m ≤ m0)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) :
    hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (hfm.stronglyMeasurable_mk.ae_eq_trim_iff hm  hgm.stronglyMeasurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h =>
      hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩

theorem AEStronglyMeasurable.comp_ae_measurable' {α β γ : Type*} [TopologicalSpace β]
    {mα : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α → β} {μ : Measure γ} {g : γ → α}
    (hf : AEStronglyMeasurable f (μ.map g)) (hg : AEMeasurable g μ) :
    AEStronglyMeasurable' (mα.comap g) (f ∘ g) μ :=
  ⟨hf.mk f ∘ g, hf.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl),
    ae_eq_comp hg hf.ae_eq_mk⟩

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable. -/
@[deprecated AEStronglyMeasurable.of_measurableSpace_le_on (since := "2025-01-23")]
theorem AEStronglyMeasurable'.aeStronglyMeasurable'_of_measurableSpace_le_on {α E}
    {m m₂ m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace E] [Zero E] (hm : m ≤ m0)
    {s : Set α} {f : α → E} (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) → MeasurableSet[m₂] (s ∩ t))
    (hf : AEStronglyMeasurable[m] f μ) (hf_zero : f =ᵐ[μ.restrict sᶜ] 0) :
    AEStronglyMeasurable' m₂ f μ :=
  .of_measurableSpace_le_on hm hs_m hs hf hf_zero

variable {α F 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section LpMeas

/-! ## The subset `lpMeas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable (F)

/-- `lpMeasSubgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    AddSubgroup (Lp F p μ) where
  carrier := {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  neg_mem' {f} hf := AEStronglyMeasurable.congr hf.neg (Lp.coeFn_neg f).symm

variable (𝕜)

/-- `lpMeas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeas (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    Submodule 𝕜 (Lp F p μ) where
  carrier := {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.const_smul c).congr (Lp.coeFn_smul c f).symm

variable {F 𝕜}

theorem mem_lpMeasSubgroup_iff_aeStronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f ∈ lpMeasSubgroup F m p μ ↔ AEStronglyMeasurable[m] f μ := by
  rw [← AddSubgroup.mem_carrier, lpMeasSubgroup, Set.mem_setOf_eq]

@[deprecated (since := "2025-01-24")]
alias mem_lpMeasSubgroup_iff_aeStronglyMeasurable' := mem_lpMeasSubgroup_iff_aeStronglyMeasurable

theorem mem_lpMeas_iff_aeStronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f ∈ lpMeas F 𝕜 m p μ ↔ AEStronglyMeasurable[m] f μ := by
  rw [← SetLike.mem_coe, ← Submodule.mem_carrier, lpMeas, Set.mem_setOf_eq]

@[deprecated (since := "2025-01-24")]
alias mem_lpMeas_iff_aeStronglyMeasurable' := mem_lpMeas_iff_aeStronglyMeasurable

theorem lpMeas.aeStronglyMeasurable {m _ : MeasurableSpace α} {μ : Measure α}
    (f : lpMeas F 𝕜 m p μ) : AEStronglyMeasurable[m] (f : α → F) μ :=
  mem_lpMeas_iff_aeStronglyMeasurable.mp f.mem

@[deprecated (since := "2025-01-24")]
alias lpMeas.aeStronglyMeasurable' := lpMeas.aeStronglyMeasurable

theorem mem_lpMeas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : Lp F p μ) :
    f ∈ lpMeas F 𝕜 m0 p μ :=
  mem_lpMeas_iff_aeStronglyMeasurable.mpr (Lp.aestronglyMeasurable f)

theorem lpMeasSubgroup_coe {m _ : MeasurableSpace α} {μ : Measure α} {f : lpMeasSubgroup F m p μ} :
    (f : _ → _) = (f : Lp F p μ) :=
  rfl

theorem lpMeas_coe {m _ : MeasurableSpace α} {μ : Measure α} {f : lpMeas F 𝕜 m p μ} :
    (f : _ → _) = (f : Lp F p μ) :=
  rfl

theorem mem_lpMeas_indicatorConstLp {m m0 : MeasurableSpace α} (hm : m ≤ m0) {μ : Measure α}
    {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) {c : F} :
    indicatorConstLp p (hm s hs) hμs c ∈ lpMeas F 𝕜 m p μ :=
  ⟨s.indicator fun _ : α => c, (@stronglyMeasurable_const _ _ m _ _).indicator hs,
    indicatorConstLp_coeFn⟩

section CompleteSubspace

/-! ## The subspace `lpMeas` is complete.

We define an `IsometryEquiv` between `lpMeasSubgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`lpMeasSubgroup` (and `lpMeas`). -/


variable {m m0 : MeasurableSpace α} {μ : Measure α}

/-- If `f` belongs to `lpMeasSubgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `AEMeasurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
theorem memℒp_trim_of_mem_lpMeasSubgroup (hm : m ≤ m0) (f : Lp F p μ)
    (hf_meas : f ∈ lpMeasSubgroup F m p μ) :
    Memℒp (mem_lpMeasSubgroup_iff_aeStronglyMeasurable.mp hf_meas).choose p (μ.trim hm) := by
  have hf : AEStronglyMeasurable[m] f μ :=
    mem_lpMeasSubgroup_iff_aeStronglyMeasurable.mp hf_meas
  let g := hf.choose
  obtain ⟨hg, hfg⟩ := hf.choose_spec
  change Memℒp g p (μ.trim hm)
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  have h_eLpNorm_fg : eLpNorm g p (μ.trim hm) = eLpNorm f p μ := by
    rw [eLpNorm_trim hm hg]
    exact eLpNorm_congr_ae hfg.symm
  rw [h_eLpNorm_fg]
  exact Lp.eLpNorm_lt_top f

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`lpMeasSubgroup F m p μ`. -/
theorem mem_lpMeasSubgroup_toLp_of_trim (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    (memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f ∈ lpMeasSubgroup F m p μ := by
  let hf_mem_ℒp := memℒp_of_memℒp_trim hm (Lp.memℒp f)
  rw [mem_lpMeasSubgroup_iff_aeStronglyMeasurable]
  refine AEStronglyMeasurable'.congr ?_ (Memℒp.coeFn_toLp hf_mem_ℒp).symm
  refine aeStronglyMeasurable'_of_aeStronglyMeasurable'_trim hm ?_
  exact Lp.aestronglyMeasurable f

variable (F p μ)

/-- Map from `lpMeasSubgroup` to `Lp F p (μ.trim hm)`. -/
noncomputable def lpMeasSubgroupToLpTrim (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    Lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_lpMeasSubgroup_iff_aeStronglyMeasurable.mp f.mem).choose
    -- Porting note: had to replace `f` with `f.1` here.
    (memℒp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

variable (𝕜)

/-- Map from `lpMeas` to `Lp F p (μ.trim hm)`. -/
noncomputable def lpMeasToLpTrim (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : Lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_lpMeas_iff_aeStronglyMeasurable.mp f.mem).choose
    -- Porting note: had to replace `f` with `f.1` here.
    (memℒp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

variable {𝕜}

/-- Map from `Lp F p (μ.trim hm)` to `lpMeasSubgroup`, inverse of
`lpMeasSubgroupToLpTrim`. -/
noncomputable def lpTrimToLpMeasSubgroup (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpMeasSubgroup F m p μ :=
  ⟨(memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

variable (𝕜)

/-- Map from `Lp F p (μ.trim hm)` to `lpMeas`, inverse of `Lp_meas_to_Lp_trim`. -/
noncomputable def lpTrimToLpMeas (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ :=
  ⟨(memℒp_of_memℒp_trim hm (Lp.memℒp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

variable {F 𝕜 p μ}

theorem lpMeasSubgroupToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f :=
  -- Porting note: replaced `(↑f)` with `f.1` here.
  (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp (memℒp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aeStronglyMeasurable.mp f.mem).choose_spec.2.symm

theorem lpTrimToLpMeasSubgroup_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f :=
  -- Porting note: filled in the argument
  Memℒp.coeFn_toLp (memℒp_of_memℒp_trim hm (Lp.memℒp f))

theorem lpMeasToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f :=
  -- Porting note: replaced `(↑f)` with `f.1` here.
  (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp (memℒp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aeStronglyMeasurable.mp f.mem).choose_spec.2.symm

theorem lpTrimToLpMeas_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f :=
  -- Porting note: filled in the argument
  Memℒp.coeFn_toLp (memℒp_of_memℒp_trim hm (Lp.memℒp f))

/-- `lpTrimToLpMeasSubgroup` is a right inverse of `lpMeasSubgroupToLpTrim`. -/
theorem lpMeasSubgroupToLpTrim_right_inv (hm : m ≤ m0) :
    Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  refine
    (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) ?_
  exact (lpMeasSubgroupToLpTrim_ae_eq hm _).trans (lpTrimToLpMeasSubgroup_ae_eq hm _)

/-- `lpTrimToLpMeasSubgroup` is a left inverse of `lpMeasSubgroupToLpTrim`. -/
theorem lpMeasSubgroupToLpTrim_left_inv (hm : m ≤ m0) :
    Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  ext1
  rw [← lpMeasSubgroup_coe]
  exact (lpTrimToLpMeasSubgroup_ae_eq hm _).trans (lpMeasSubgroupToLpTrim_ae_eq hm _)

theorem lpMeasSubgroupToLpTrim_add (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f + g) =
      lpMeasSubgroupToLpTrim F p μ hm f + lpMeasSubgroupToLpTrim F p μ hm g := by
  ext1
  refine EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm  ?_ ?_
  · exact (Lp.stronglyMeasurable _).add (Lp.stronglyMeasurable _)
  refine (lpMeasSubgroupToLpTrim_ae_eq hm _).trans ?_
  refine
    EventuallyEq.trans ?_
      (EventuallyEq.add (lpMeasSubgroupToLpTrim_ae_eq hm f).symm
        (lpMeasSubgroupToLpTrim_ae_eq hm g).symm)
  refine (Lp.coeFn_add _ _).trans ?_
  simp_rw [lpMeasSubgroup_coe]
  filter_upwards with x using rfl

theorem lpMeasSubgroupToLpTrim_neg (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f := by
  ext1
  refine EventuallyEq.trans ?_ (Lp.coeFn_neg _).symm
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _).neg
    <| (lpMeasSubgroupToLpTrim_ae_eq hm _).trans <|
    ((Lp.coeFn_neg _).trans ?_).trans  (lpMeasSubgroupToLpTrim_ae_eq hm f).symm.neg
  simp_rw [lpMeasSubgroup_coe]
  exact Eventually.of_forall fun x => by rfl

theorem lpMeasSubgroupToLpTrim_sub (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f - g) =
      lpMeasSubgroupToLpTrim F p μ hm f - lpMeasSubgroupToLpTrim F p μ hm g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, lpMeasSubgroupToLpTrim_add,
    lpMeasSubgroupToLpTrim_neg]

theorem lpMeasToLpTrim_smul (hm : m ≤ m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f := by
  ext1
  refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).const_smul c
  refine (lpMeasToLpTrim_ae_eq hm _).trans ?_
  refine (Lp.coeFn_smul _ _).trans ?_
  refine (lpMeasToLpTrim_ae_eq hm f).mono fun x hx => ?_
  simp only [Pi.smul_apply, hx]

/-- `lpMeasSubgroupToLpTrim` preserves the norm. -/
theorem lpMeasSubgroupToLpTrim_norm_map [hp : Fact (1 ≤ p)] (hm : m ≤ m0)
    (f : lpMeasSubgroup F m p μ) : ‖lpMeasSubgroupToLpTrim F p μ hm f‖ = ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_trim hm (Lp.stronglyMeasurable _),
    eLpNorm_congr_ae (lpMeasSubgroupToLpTrim_ae_eq hm _), lpMeasSubgroup_coe, ← Lp.norm_def]
  congr

theorem isometry_lpMeasSubgroupToLpTrim [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    Isometry (lpMeasSubgroupToLpTrim F p μ hm) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, ← lpMeasSubgroupToLpTrim_sub, lpMeasSubgroupToLpTrim_norm_map,
      dist_eq_norm]

variable (F p μ)

/-- `lpMeasSubgroup` and `Lp F p (μ.trim hm)` are isometric. -/
noncomputable def lpMeasSubgroupToLpTrimIso [Fact (1 ≤ p)] (hm : m ≤ m0) :
    lpMeasSubgroup F m p μ ≃ᵢ Lp F p (μ.trim hm) where
  toFun := lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  isometry_toFun := isometry_lpMeasSubgroupToLpTrim hm

variable (𝕜)

/-- `lpMeasSubgroup` and `lpMeas` are isometric. -/
noncomputable def lpMeasSubgroupToLpMeasIso [Fact (1 ≤ p)] :
    lpMeasSubgroup F m p μ ≃ᵢ lpMeas F 𝕜 m p μ :=
  IsometryEquiv.refl (lpMeasSubgroup F m p μ)

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
    IsComplete {f : Lp F p μ | AEStronglyMeasurable[m] f μ} := by
  rw [← completeSpace_coe_iff_isComplete]
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  change CompleteSpace (lpMeasSubgroup F m p μ)
  infer_instance

theorem isClosed_aeStronglyMeasurable' [Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsClosed {f : Lp F p μ | AEStronglyMeasurable[m] f μ} :=
  IsComplete.isClosed (isComplete_aeStronglyMeasurable' hm)

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

theorem lpMeasToLpTrimLie_symm_toLp [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] (hm : m ≤ m0)
    (f : α → F) (hf : Memℒp f p (μ.trim hm)) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (hf.toLp f) : Lp F p μ) =
      (memℒp_of_memℒp_trim hm hf).toLp f := by
  ext1
  rw [← lpMeas_coe]
  refine (lpTrimToLpMeas_ae_eq hm _).trans ?_
  exact (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp hf)).trans (Memℒp.coeFn_toLp _).symm

end StronglyMeasurable

end LpMeas

section Induction

variable {m m0 : MeasurableSpace α} {μ : Measure α} [Fact (1 ≤ p)] [NormedSpace ℝ F]

/-- Auxiliary lemma for `Lp.induction_stronglyMeasurable`. -/
@[elab_as_elim]
theorem Lp.induction_stronglyMeasurable_aux (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
    (h_ind : ∀ (c : F) {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s < ∞),
      P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add : ∀ ⦃f g⦄, ∀ hf : Memℒp f p μ, ∀ hg : Memℒp g p μ, AEStronglyMeasurable[m] f μ →
      AEStronglyMeasurable[m] g μ → Disjoint (Function.support f) (Function.support g) →
        P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F ℝ m p μ | P f}) :
    ∀ f : Lp F p μ, AEStronglyMeasurable[m] f μ → P f := by
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
    ∀ f : Lp F p μ, AEStronglyMeasurable[m] f μ → P f := by
  intro f hf
  suffices h_add_ae :
    ∀ ⦃f g⦄, ∀ hf : Memℒp f p μ, ∀ hg : Memℒp g p μ, AEStronglyMeasurable[m] f μ →
      AEStronglyMeasurable[m] g μ → Disjoint (Function.support f) (Function.support g) →
        P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g) from
    Lp.induction_stronglyMeasurable_aux hm hp_ne_top _ h_ind h_add_ae h_closed f hf
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
    ∀ ⦃f : α → F⦄, Memℒp f p μ → AEStronglyMeasurable[m] f μ → P f := by
  intro f hf hfm
  let f_Lp := hf.toLp f
  have hfm_Lp : AEStronglyMeasurable[m] f_Lp μ := hfm.congr hf.coeFn_toLp.symm
  refine h_ae hf.coeFn_toLp (Lp.memℒp _) ?_
  change P f_Lp
  refine Lp.induction_stronglyMeasurable hm hp_ne_top (fun f => P f) ?_ ?_ h_closed f_Lp hfm_Lp
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

end Induction

end MeasureTheory
