/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.Filter.ENNReal

#align_import measure_theory.function.ess_sup from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

/-!
# Essential supremum and infimum
We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ℝ≥0∞` is used in particular to define the norm in
the `L∞` space (see `Mathlib.MeasureTheory.Function.LpSpace`).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see `Mathlib.MeasureTheory.Function.AEEqFun`).

## Main definitions

* `essSup f μ := (ae μ).limsup f`
* `essInf f μ := (ae μ).liminf f`
-/


open MeasureTheory Filter Set TopologicalSpace

open ENNReal MeasureTheory NNReal

variable {α β : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β]

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
def essSup {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :=
  (ae μ).limsup f
#align ess_sup essSup

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
def essInf {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :=
  (ae μ).liminf f
#align ess_inf essInf

theorem essSup_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essSup f μ = essSup g μ :=
  limsup_congr hfg
#align ess_sup_congr_ae essSup_congr_ae

theorem essInf_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essInf f μ = essInf g μ :=
  @essSup_congr_ae α βᵒᵈ _ _ _ _ _ hfg
#align ess_inf_congr_ae essInf_congr_ae

@[simp]
theorem essSup_const' [NeZero μ] (c : β) : essSup (fun _ : α => c) μ = c :=
  limsup_const _
#align ess_sup_const' essSup_const'

@[simp]
theorem essInf_const' [NeZero μ] (c : β) : essInf (fun _ : α => c) μ = c :=
  liminf_const _
#align ess_inf_const' essInf_const'

theorem essSup_const (c : β) (hμ : μ ≠ 0) : essSup (fun _ : α => c) μ = c :=
  have := NeZero.mk hμ; essSup_const' _
#align ess_sup_const essSup_const

theorem essInf_const (c : β) (hμ : μ ≠ 0) : essInf (fun _ : α => c) μ = c :=
  have := NeZero.mk hμ; essInf_const' _
#align ess_inf_const essInf_const

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder β] {x : β} {f : α → β}

theorem essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (f : α → β) :
    essSup f μ = sInf { a | μ { x | a < f x } = 0 } := by
  dsimp [essSup, limsup, limsSup]
  simp only [eventually_map, ae_iff, not_le]
#align ess_sup_eq_Inf essSup_eq_sInf

theorem essInf_eq_sSup {m : MeasurableSpace α} (μ : Measure α) (f : α → β) :
    essInf f μ = sSup { a | μ { x | f x < a } = 0 } := by
  dsimp [essInf, liminf, limsInf]
  simp only [eventually_map, ae_iff, not_le]
#align ess_inf_eq_Sup essInf_eq_sSup

theorem ae_lt_of_essSup_lt (hx : essSup f μ < x)
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, f y < x :=
  eventually_lt_of_limsup_lt hx hf
#align ae_lt_of_ess_sup_lt ae_lt_of_essSup_lt

theorem ae_lt_of_lt_essInf (hx : x < essInf f μ)
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, x < f y :=
  eventually_lt_of_lt_liminf hx hf
#align ae_lt_of_lt_ess_inf ae_lt_of_lt_essInf

variable [TopologicalSpace β] [FirstCountableTopology β] [OrderTopology β]

theorem ae_le_essSup
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, f y ≤ essSup f μ :=
  eventually_le_limsup hf
#align ae_le_ess_sup ae_le_essSup

theorem ae_essInf_le
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    ∀ᵐ y ∂μ, essInf f μ ≤ f y :=
  eventually_liminf_le hf
#align ae_ess_inf_le ae_essInf_le

theorem meas_essSup_lt
    (hf : IsBoundedUnder (· ≤ ·) (ae μ) f := by isBoundedDefault) :
    μ { y | essSup f μ < f y } = 0 := by
  simp_rw [← not_le]
  exact ae_le_essSup hf
#align meas_ess_sup_lt meas_essSup_lt

theorem meas_lt_essInf
    (hf : IsBoundedUnder (· ≥ ·) (ae μ) f := by isBoundedDefault) :
    μ { y | f y < essInf f μ } = 0 := by
  simp_rw [← not_le]
  exact ae_essInf_le hf
#align meas_lt_ess_inf meas_lt_essInf

end ConditionallyCompleteLinearOrder

section CompleteLattice

variable [CompleteLattice β]

@[simp]
theorem essSup_measure_zero {m : MeasurableSpace α} {f : α → β} : essSup f (0 : Measure α) = ⊥ :=
  le_bot_iff.mp (sInf_le (by simp [Set.mem_setOf_eq, EventuallyLE, ae_iff]))
#align ess_sup_measure_zero essSup_measure_zero

@[simp]
theorem essInf_measure_zero {_ : MeasurableSpace α} {f : α → β} : essInf f (0 : Measure α) = ⊤ :=
  @essSup_measure_zero α βᵒᵈ _ _ _
#align ess_inf_measure_zero essInf_measure_zero

theorem essSup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : essSup f μ ≤ essSup g μ :=
  limsup_le_limsup hfg
#align ess_sup_mono_ae essSup_mono_ae

theorem essInf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : essInf f μ ≤ essInf g μ :=
  liminf_le_liminf hfg
#align ess_inf_mono_ae essInf_mono_ae

theorem essSup_le_of_ae_le {f : α → β} (c : β) (hf : f ≤ᵐ[μ] fun _ => c) : essSup f μ ≤ c :=
  limsup_le_of_le (by isBoundedDefault) hf
#align ess_sup_le_of_ae_le essSup_le_of_ae_le

theorem le_essInf_of_ae_le {f : α → β} (c : β) (hf : (fun _ => c) ≤ᵐ[μ] f) : c ≤ essInf f μ :=
  @essSup_le_of_ae_le α βᵒᵈ _ _ _ _ c hf
#align le_ess_inf_of_ae_le le_essInf_of_ae_le

theorem essSup_const_bot : essSup (fun _ : α => (⊥ : β)) μ = (⊥ : β) :=
  limsup_const_bot
#align ess_sup_const_bot essSup_const_bot

theorem essInf_const_top : essInf (fun _ : α => (⊤ : β)) μ = (⊤ : β) :=
  liminf_const_top
#align ess_inf_const_top essInf_const_top

theorem OrderIso.essSup_apply {m : MeasurableSpace α} {γ} [CompleteLattice γ] (f : α → β)
    (μ : Measure α) (g : β ≃o γ) : g (essSup f μ) = essSup (fun x => g (f x)) μ := by
  refine OrderIso.limsup_apply g ?_ ?_ ?_ ?_
  all_goals isBoundedDefault
#align order_iso.ess_sup_apply OrderIso.essSup_apply

theorem OrderIso.essInf_apply {_ : MeasurableSpace α} {γ} [CompleteLattice γ] (f : α → β)
    (μ : Measure α) (g : β ≃o γ) : g (essInf f μ) = essInf (fun x => g (f x)) μ :=
  @OrderIso.essSup_apply α βᵒᵈ _ _ γᵒᵈ _ _ _ g.dual
#align order_iso.ess_inf_apply OrderIso.essInf_apply

theorem essSup_mono_measure {f : α → β} (hμν : ν ≪ μ) : essSup f ν ≤ essSup f μ := by
  refine limsup_le_limsup_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) ?_ ?_
  all_goals isBoundedDefault
#align ess_sup_mono_measure essSup_mono_measure

theorem essSup_mono_measure' {α : Type*} {β : Type*} {_ : MeasurableSpace α}
    {μ ν : MeasureTheory.Measure α} [CompleteLattice β] {f : α → β} (hμν : ν ≤ μ) :
    essSup f ν ≤ essSup f μ :=
  essSup_mono_measure (Measure.absolutelyContinuous_of_le hμν)
#align ess_sup_mono_measure' essSup_mono_measure'

theorem essInf_antitone_measure {f : α → β} (hμν : μ ≪ ν) : essInf f ν ≤ essInf f μ := by
  refine liminf_le_liminf_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) ?_ ?_
  all_goals isBoundedDefault
#align ess_inf_antitone_measure essInf_antitone_measure

theorem essSup_smul_measure {f : α → β} {c : ℝ≥0∞} (hc : c ≠ 0) :
    essSup f (c • μ) = essSup f μ := by
  simp_rw [essSup]
  suffices h_smul : ae (c • μ) = ae μ by rw [h_smul]
  ext1
  simp_rw [mem_ae_iff]
  simp [hc]
#align ess_sup_smul_measure essSup_smul_measure

section TopologicalSpace

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : α → γ} {g : γ → β}

theorem essSup_comp_le_essSup_map_measure (hf : AEMeasurable f μ) :
    essSup (g ∘ f) μ ≤ essSup g (Measure.map f μ) := by
  refine limsSup_le_limsSup_of_le ?_
  rw [← Filter.map_map]
  exact Filter.map_mono (Measure.tendsto_ae_map hf)
#align ess_sup_comp_le_ess_sup_map_measure essSup_comp_le_essSup_map_measure

theorem MeasurableEmbedding.essSup_map_measure (hf : MeasurableEmbedding f) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf.measurable.aemeasurable)
  refine limsSup_le_limsSup (by isBoundedDefault) (by isBoundedDefault) (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  exact hf.ae_map_iff.mpr h_le
#align measurable_embedding.ess_sup_map_measure MeasurableEmbedding.essSup_map_measure

variable [MeasurableSpace β] [TopologicalSpace β] [SecondCountableTopology β]
  [OrderClosedTopology β] [OpensMeasurableSpace β]

theorem essSup_map_measure_of_measurable (hg : Measurable g) (hf : AEMeasurable f μ) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf)
  refine limsSup_le_limsSup (by isBoundedDefault) (by isBoundedDefault) (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  rw [ae_map_iff hf (measurableSet_le hg measurable_const)]
  exact h_le
#align ess_sup_map_measure_of_measurable essSup_map_measure_of_measurable

theorem essSup_map_measure (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  rw [essSup_congr_ae hg.ae_eq_mk, essSup_map_measure_of_measurable hg.measurable_mk hf]
  refine essSup_congr_ae ?_
  have h_eq := ae_of_ae_map hf hg.ae_eq_mk
  rw [← EventuallyEq] at h_eq
  exact h_eq.symm
#align ess_sup_map_measure essSup_map_measure

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
#align ennreal.ae_le_ess_sup ENNReal.ae_le_essSup

@[simp]
theorem essSup_eq_zero_iff : essSup f μ = 0 ↔ f =ᵐ[μ] 0 :=
  limsup_eq_zero_iff
#align ennreal.ess_sup_eq_zero_iff ENNReal.essSup_eq_zero_iff

theorem essSup_const_mul {a : ℝ≥0∞} : essSup (fun x : α => a * f x) μ = a * essSup f μ :=
  limsup_const_mul
#align ennreal.ess_sup_const_mul ENNReal.essSup_const_mul

theorem essSup_mul_le (f g : α → ℝ≥0∞) : essSup (f * g) μ ≤ essSup f μ * essSup g μ :=
  limsup_mul_le f g
#align ennreal.ess_sup_mul_le ENNReal.essSup_mul_le

theorem essSup_add_le (f g : α → ℝ≥0∞) : essSup (f + g) μ ≤ essSup f μ + essSup g μ :=
  limsup_add_le f g
#align ennreal.ess_sup_add_le ENNReal.essSup_add_le

theorem essSup_liminf_le {ι} [Countable ι] [LinearOrder ι] (f : ι → α → ℝ≥0∞) :
    essSup (fun x => atTop.liminf fun n => f n x) μ ≤
      atTop.liminf fun n => essSup (fun x => f n x) μ := by
  simp_rw [essSup]
  exact ENNReal.limsup_liminf_le_liminf_limsup fun a b => f b a
#align ennreal.ess_sup_liminf_le ENNReal.essSup_liminf_le

theorem coe_essSup {f : α → ℝ≥0} (hf : IsBoundedUnder (· ≤ ·) (ae μ) f) :
    ((essSup f μ : ℝ≥0) : ℝ≥0∞) = essSup (fun x => (f x : ℝ≥0∞)) μ :=
  (ENNReal.coe_sInf <| hf).trans <|
    eq_of_forall_le_iff fun r => by
      simp [essSup, limsup, limsSup, eventually_map, ENNReal.forall_ennreal]; rfl
#align ennreal.coe_ess_sup ENNReal.coe_essSup

end ENNReal
