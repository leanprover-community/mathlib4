/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Probability.UniformOn

/-!
# Essential supremum and infimum
We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ℝ≥0∞` is used in particular to define the norm in
the `L∞` space (see `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see `Mathlib/MeasureTheory/Function/AEEqFun.lean`).

## Main definitions

* `essSup f μ := (ae μ).limsup f`
* `essInf f μ := (ae μ).liminf f`
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {α β : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β] {f : α → β}

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
def essSup {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :=
  (ae μ).limsup f

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
def essInf {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :=
  (ae μ).liminf f

theorem essSup_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essSup f μ = essSup g μ :=
  limsup_congr hfg

theorem essInf_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essInf f μ = essInf g μ :=
  @essSup_congr_ae α βᵒᵈ _ _ _ _ _ hfg

@[simp]
theorem essSup_const' [NeZero μ] (c : β) : essSup (fun _ : α => c) μ = c :=
  limsup_const _

@[simp]
theorem essInf_const' [NeZero μ] (c : β) : essInf (fun _ : α => c) μ = c :=
  liminf_const _

theorem essSup_const (c : β) (hμ : μ ≠ 0) : essSup (fun _ : α => c) μ = c :=
  have := NeZero.mk hμ; essSup_const' _

theorem essInf_const (c : β) (hμ : μ ≠ 0) : essInf (fun _ : α => c) μ = c :=
  have := NeZero.mk hμ; essInf_const' _

section SMul
variable {R : Type*} [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [Module.IsTorsionFree R ℝ≥0∞] {c : R}

@[simp]
lemma essSup_smul_measure (hc : c ≠ 0) (f : α → β) : essSup f (c • μ) = essSup f μ := by
  simp_rw [essSup, Measure.ae_smul_measure_eq hc]

end SMul

@[simp]
lemma essSup_ennreal_smul_measure {c : ℝ≥0∞} (hc : c ≠ 0) (f : α → β) :
    essSup f (c • μ) = essSup f μ := by
  simp_rw [essSup, Measure.ae_ennreal_smul_measure_eq hc]

variable [Nonempty α]

lemma essSup_eq_ciSup (hμ : ∀ a, μ {a} ≠ 0) (hf : BddAbove (Set.range f)) :
    essSup f μ = ⨆ a, f a := by rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_ciSup hf]

lemma essInf_eq_ciInf (hμ : ∀ a, μ {a} ≠ 0) (hf : BddBelow (Set.range f)) :
    essInf f μ = ⨅ a, f a := by rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_ciInf hf]

variable [MeasurableSingletonClass α]

@[simp] lemma essSup_count_eq_ciSup (hf : BddAbove (Set.range f)) :
    essSup f .count = ⨆ a, f a := essSup_eq_ciSup (by simp) hf

@[simp] lemma essInf_count_eq_ciInf (hf : BddBelow (Set.range f)) :
    essInf f .count = ⨅ a, f a := essInf_eq_ciInf (by simp) hf

@[simp] lemma essSup_uniformOn_eq_ciSup [Finite α] (hf : BddAbove (Set.range f)) :
    essSup f (uniformOn univ) = ⨆ a, f a :=
  essSup_eq_ciSup (by simpa [uniformOn, cond_apply]) hf

@[simp] lemma essInf_cond_count_eq_ciInf [Finite α] (hf : BddBelow (Set.range f)) :
    essInf f (uniformOn univ) = ⨅ a, f a :=
  essInf_eq_ciInf (by simpa [uniformOn, cond_apply]) hf

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder β] {x : β} {f : α → β}

theorem essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (f : α → β) :
    essSup f μ = sInf { a | μ { x | a < f x } = 0 } := by
  dsimp [essSup, limsup, limsSup]
  simp only [eventually_map, ae_iff, not_le]

theorem essInf_eq_sSup {m : MeasurableSpace α} (μ : Measure α) (f : α → β) :
    essInf f μ = sSup { a | μ { x | f x < a } = 0 } := by
  dsimp [essInf, liminf, limsInf]
  simp only [eventually_map, ae_iff, not_le]

theorem ae_lt_of_essSup_lt (hx : essSup f μ < x)
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, f y < x :=
  eventually_lt_of_limsup_lt hx hf

theorem ae_lt_of_lt_essInf (hx : x < essInf f μ)
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, x < f y :=
  eventually_lt_of_lt_liminf hx hf

variable [TopologicalSpace β] [FirstCountableTopology β] [OrderTopology β]

theorem ae_le_essSup
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, f y ≤ essSup f μ :=
  eventually_le_limsup hf

theorem ae_essInf_le
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, essInf f μ ≤ f y :=
  eventually_liminf_le hf

theorem meas_essSup_lt
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    μ { y | essSup f μ < f y } = 0 := by
  simp_rw [← not_le]
  exact ae_le_essSup hf

theorem meas_lt_essInf
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    μ { y | f y < essInf f μ } = 0 := by
  simp_rw [← not_le]
  exact ae_essInf_le hf

end ConditionallyCompleteLinearOrder

section CompleteLattice

variable [CompleteLattice β]

@[simp]
theorem essSup_measure_zero {m : MeasurableSpace α} {f : α → β} : essSup f (0 : Measure α) = ⊥ :=
  le_bot_iff.mp (sInf_le (by simp))

@[simp]
theorem essInf_measure_zero {_ : MeasurableSpace α} {f : α → β} : essInf f (0 : Measure α) = ⊤ :=
  @essSup_measure_zero α βᵒᵈ _ _ _

theorem essSup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : essSup f μ ≤ essSup g μ :=
  limsup_le_limsup hfg

theorem essInf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : essInf f μ ≤ essInf g μ :=
  liminf_le_liminf hfg

theorem essSup_le_of_ae_le {f : α → β} (c : β) (hf : f ≤ᵐ[μ] fun _ => c) : essSup f μ ≤ c :=
  limsup_le_of_le (by isBoundedDefault) hf

theorem le_essInf_of_ae_le {f : α → β} (c : β) (hf : (fun _ => c) ≤ᵐ[μ] f) : c ≤ essInf f μ :=
  @essSup_le_of_ae_le α βᵒᵈ _ _ _ _ c hf

theorem essSup_const_bot : essSup (fun _ : α => (⊥ : β)) μ = (⊥ : β) :=
  limsup_const_bot

theorem essInf_const_top : essInf (fun _ : α => (⊤ : β)) μ = (⊤ : β) :=
  liminf_const_top

theorem OrderIso.essSup_apply {m : MeasurableSpace α} {γ} [CompleteLattice γ] (f : α → β)
    (μ : Measure α) (g : β ≃o γ) : g (essSup f μ) = essSup (fun x => g (f x)) μ := by
  refine OrderIso.limsup_apply g ?_ ?_ ?_ ?_
  all_goals isBoundedDefault

theorem OrderIso.essInf_apply {_ : MeasurableSpace α} {γ} [CompleteLattice γ] (f : α → β)
    (μ : Measure α) (g : β ≃o γ) : g (essInf f μ) = essInf (fun x => g (f x)) μ :=
  @OrderIso.essSup_apply α βᵒᵈ _ _ γᵒᵈ _ _ _ g.dual

theorem essSup_mono_measure {f : α → β} (hμν : ν ≪ μ) : essSup f ν ≤ essSup f μ := by
  refine limsup_le_limsup_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) ?_ ?_
  all_goals isBoundedDefault

theorem essSup_mono_measure' {α : Type*} {β : Type*} {_ : MeasurableSpace α}
    {μ ν : MeasureTheory.Measure α} [CompleteLattice β] {f : α → β} (hμν : ν ≤ μ) :
    essSup f ν ≤ essSup f μ :=
  essSup_mono_measure (Measure.absolutelyContinuous_of_le hμν)

theorem essInf_antitone_measure {f : α → β} (hμν : μ ≪ ν) : essInf f ν ≤ essInf f μ := by
  refine liminf_le_liminf_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) ?_ ?_
  all_goals isBoundedDefault

lemma essSup_eq_iSup (hμ : ∀ a, μ {a} ≠ 0) (f : α → β) : essSup f μ = ⨆ i, f i := by
  rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_iSup]

lemma essInf_eq_iInf (hμ : ∀ a, μ {a} ≠ 0) (f : α → β) : essInf f μ = ⨅ i, f i := by
  rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_iInf]

@[simp] lemma essSup_count [MeasurableSingletonClass α] (f : α → β) : essSup f .count = ⨆ i, f i :=
  essSup_eq_iSup (by simp) _

@[simp] lemma essInf_count [MeasurableSingletonClass α] (f : α → β) : essInf f .count = ⨅ i, f i :=
  essInf_eq_iInf (by simp) _

section TopologicalSpace

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : α → γ} {g : γ → β}

theorem essSup_comp_le_essSup_map_measure (hf : AEMeasurable f μ) :
    essSup (g ∘ f) μ ≤ essSup g (Measure.map f μ) := by
  refine limsSup_le_limsSup_of_le ?_
  rw [← Filter.map_map]
  exact Filter.map_mono (Measure.tendsto_ae_map hf)

theorem MeasurableEmbedding.essSup_map_measure (hf : MeasurableEmbedding f) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf.measurable.aemeasurable)
  refine limsSup_le_limsSup (by isBoundedDefault) (by isBoundedDefault) (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  exact hf.ae_map_iff.mpr h_le

variable [MeasurableSpace β] [TopologicalSpace β] [SecondCountableTopology β]
  [OrderClosedTopology β] [OpensMeasurableSpace β]

theorem essSup_map_measure_of_measurable (hg : Measurable g) (hf : AEMeasurable f μ) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf)
  refine limsSup_le_limsSup (by isBoundedDefault) (by isBoundedDefault) (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  rw [ae_map_iff hf (measurableSet_le hg measurable_const)]
  exact h_le

theorem essSup_map_measure (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  rw [essSup_congr_ae hg.ae_eq_mk, essSup_map_measure_of_measurable hg.measurable_mk hf]
  refine essSup_congr_ae ?_
  have h_eq := ae_of_ae_map hf hg.ae_eq_mk
  rw [← EventuallyEq] at h_eq
  exact h_eq.symm

end TopologicalSpace

end CompleteLattice

namespace ENNReal

variable {f : α → ℝ≥0∞}

lemma essSup_piecewise {s : Set α} [DecidablePred (· ∈ s)] {g} (hs : MeasurableSet s) :
    essSup (s.piecewise f g) μ = max (essSup f (μ.restrict s)) (essSup g (μ.restrict sᶜ)) := by
  simp only [essSup, limsup_piecewise, blimsup_eq_limsup, ae_restrict_eq, hs, hs.compl]; rfl

theorem essSup_indicator_eq_essSup_restrict {s : Set α} {f : α → ℝ≥0∞} (hs : MeasurableSet s) :
    essSup (s.indicator f) μ = essSup f (μ.restrict s) := by
  classical
  simp only [← piecewise_eq_indicator, essSup_piecewise hs, max_eq_left_iff]
  exact limsup_const_bot.trans_le (zero_le _)

theorem ae_le_essSup (f : α → ℝ≥0∞) : ∀ᵐ y ∂μ, f y ≤ essSup f μ :=
  eventually_le_limsup f

@[simp]
theorem essSup_eq_zero_iff : essSup f μ = 0 ↔ f =ᵐ[μ] 0 :=
  limsup_eq_zero_iff

theorem essSup_const_mul {a : ℝ≥0∞} : essSup (fun x : α => a * f x) μ = a * essSup f μ :=
  limsup_const_mul

theorem essSup_mul_le (f g : α → ℝ≥0∞) : essSup (f * g) μ ≤ essSup f μ * essSup g μ :=
  limsup_mul_le f g

theorem essSup_add_le (f g : α → ℝ≥0∞) : essSup (f + g) μ ≤ essSup f μ + essSup g μ :=
  limsup_add_le f g

theorem essSup_liminf_le {ι} [Countable ι] [Preorder ι] (f : ι → α → ℝ≥0∞) :
    essSup (fun x => atTop.liminf fun n => f n x) μ ≤
      atTop.liminf fun n => essSup (fun x => f n x) μ := by
  simp_rw [essSup]
  exact ENNReal.limsup_liminf_le_liminf_limsup fun a b => f b a

theorem coe_essSup {f : α → ℝ≥0} (hf : IsBoundedUnder (· ≤ ·) (ae μ) f) :
    ((essSup f μ : ℝ≥0) : ℝ≥0∞) = essSup (fun x => (f x : ℝ≥0∞)) μ :=
  (ENNReal.coe_sInf <| hf).trans <|
    eq_of_forall_le_iff fun r => by
      simp [essSup, limsup, limsSup, eventually_map, ENNReal.forall_ennreal]; rfl

lemma ofReal_essSup {f : α → ℝ} (h₁ : IsCoboundedUnder (· ≤ ·) (ae μ) f)
    (h₂ : IsBoundedUnder (· ≤ ·) (ae μ) f) :
    ENNReal.ofReal (essSup f μ) = essSup (fun a ↦ .ofReal (f a)) μ := ENNReal.ofReal_limsup

lemma toReal_essSup {f : α → ℝ≥0∞} (h₁ : ∀ᵐ a ∂μ, f a ≠ ⊤)
    (h₂ : IsBoundedUnder (· ≤ ·) (ae μ) fun i ↦ (f i).toReal) :
    (essSup f μ).toReal = essSup (fun a ↦ (f a).toReal) μ := by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · simp [essSup, limsup, limsSup]
  · exact ENNReal.toReal_limsup h₁

lemma essSup_restrict_eq_of_support_subset {s : Set α} {f : α → ℝ≥0∞} (hsf : f.support ⊆ s) :
    essSup f (μ.restrict s) = essSup f μ := by
  apply le_antisymm (essSup_mono_measure' Measure.restrict_le_self)
  apply le_of_forall_lt (fun c hc ↦ ?_)
  obtain ⟨d, cd, hd⟩ : ∃ d, c < d ∧ d < essSup f μ := exists_between hc
  let t := {x | d < f x}
  have A : 0 < (μ.restrict t) t := by
    simp only [Measure.restrict_apply_self]
    rw [essSup_eq_sInf] at hd
    have : d ∉ {a | μ {x | a < f x} = 0} := notMem_of_lt_csInf hd (OrderBot.bddBelow _)
    exact bot_lt_iff_ne_bot.2 this
  have B : 0 < (μ.restrict s) t := by
    have : μ.restrict t ≤ μ.restrict s := by
      apply Measure.restrict_mono _ le_rfl
      apply subset_trans _ hsf
      intro x (hx : d < f x)
      exact (lt_of_le_of_lt bot_le hx).ne'
    exact lt_of_lt_of_le A (this _)
  apply cd.trans_le
  rw [essSup_eq_sInf]
  apply le_sInf (fun b hb ↦ ?_)
  contrapose! hb
  exact ne_of_gt (B.trans_le (measure_mono (fun x hx ↦ hb.trans hx)))

end ENNReal
