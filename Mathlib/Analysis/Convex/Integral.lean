/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Average

#align_import analysis.convex.integral from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Jensen's inequality for integrals

In this file we prove several forms of Jensen's inequality for integrals.

- for convex sets: `Convex.average_mem`, `Convex.set_average_mem`, `Convex.integral_mem`;

- for convex functions: `ConvexOn.average_mem_epigraph`, `ConvexOn.map_average_le`,
  `ConvexOn.set_average_mem_epigraph`, `ConvexOn.map_set_average_le`, `ConvexOn.map_integral_le`;

- for strictly convex sets: `StrictConvex.ae_eq_const_or_average_mem_interior`;

- for a closed ball in a strictly convex normed space:
  `ae_eq_const_or_norm_integral_lt_of_norm_le_const`;

- for strictly convex functions: `StrictConvexOn.ae_eq_const_or_map_average_lt`.

## TODO

- Use a typeclass for strict convexity of a closed ball.

## Tags

convex, integral, center mass, average value, Jensen's inequality
-/


open MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology BigOperators ENNReal Convex

variable {α E F : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μ : Measure α}
  {s : Set E} {t : Set α} {f : α → E} {g : E → ℝ} {C : ℝ}

/-!
### Non-strict Jensen's inequality
-/


/-- If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `Convex.sum_mem` for a finite sum version of this lemma. -/
theorem Convex.integral_mem [IsProbabilityMeasure μ] (hs : Convex ℝ s) (hsc : IsClosed s)
    (hf : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (∫ x, f x ∂μ) ∈ s := by
  borelize E
  -- ⊢ ∫ (x : α), f x ∂μ ∈ s
  rcases hfi.aestronglyMeasurable with ⟨g, hgm, hfg⟩
  -- ⊢ ∫ (x : α), f x ∂μ ∈ s
  haveI : SeparableSpace (range g ∩ s : Set E) :=
    (hgm.isSeparable_range.mono (inter_subset_left _ _)).separableSpace
  obtain ⟨y₀, h₀⟩ : (range g ∩ s).Nonempty := by
    rcases(hf.and hfg).exists with ⟨x₀, h₀⟩
    exact ⟨f x₀, by simp only [h₀.2, mem_range_self], h₀.1⟩
  rw [integral_congr_ae hfg]; rw [integrable_congr hfg] at hfi
  -- ⊢ ∫ (a : α), g a ∂μ ∈ s
                              -- ⊢ ∫ (a : α), g a ∂μ ∈ s
  have hg : ∀ᵐ x ∂μ, g x ∈ closure (range g ∩ s) := by
    filter_upwards [hfg.rw (fun _ y => y ∈ s) hf] with x hx
    apply subset_closure
    exact ⟨mem_range_self _, hx⟩
  set G : ℕ → SimpleFunc α E := SimpleFunc.approxOn _ hgm.measurable (range g ∩ s) y₀ h₀
  -- ⊢ ∫ (a : α), g a ∂μ ∈ s
  have : Tendsto (fun n => (G n).integral μ) atTop (𝓝 <| ∫ x, g x ∂μ) :=
    tendsto_integral_approxOn_of_measurable hfi _ hg _ (integrable_const _)
  refine' hsc.mem_of_tendsto this (eventually_of_forall fun n => hs.sum_mem _ _ _)
  · exact fun _ _ => ENNReal.toReal_nonneg
    -- 🎉 no goals
  · rw [← ENNReal.toReal_sum, (G n).sum_range_measure_preimage_singleton, measure_univ,
      ENNReal.one_toReal]
    exact fun _ _ => measure_ne_top _ _
    -- 🎉 no goals
  · simp only [SimpleFunc.mem_range, forall_range_iff]
    -- ⊢ ∀ (i : α), ↑↑(ContinuousLinearMap.id ℝ E) (↑(SimpleFunc.approxOn g (_ : Meas …
    intro x
    -- ⊢ ↑↑(ContinuousLinearMap.id ℝ E) (↑(SimpleFunc.approxOn g (_ : Measurable g) ( …
    apply inter_subset_right (range g)
    -- ⊢ ↑↑(ContinuousLinearMap.id ℝ E) (↑(SimpleFunc.approxOn g (_ : Measurable g) ( …
    exact SimpleFunc.approxOn_mem hgm.measurable h₀ _ _
    -- 🎉 no goals
#align convex.integral_mem Convex.integral_mem

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
theorem Convex.average_mem [IsFiniteMeasure μ] [NeZero μ] (hs : Convex ℝ s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (⨍ x, f x ∂μ) ∈ s := by
  refine' hs.integral_mem hsc (ae_mono' _ hfs) hfi.to_average
  -- ⊢ (↑↑μ univ)⁻¹ • μ ≪ μ
  exact AbsolutelyContinuous.smul (refl _) _
  -- 🎉 no goals
#align convex.average_mem Convex.average_mem

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
theorem Convex.set_average_mem (hs : Convex ℝ s) (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ) : (⨍ x in t, f x ∂μ) ∈ s :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hs.average_mem hsc hfs hfi
#align convex.set_average_mem Convex.set_average_mem

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex set in `E`, and `f` is an integrable
function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `closure s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
theorem Convex.set_average_mem_closure (hs : Convex ℝ s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ) :
    (⨍ x in t, f x ∂μ) ∈ closure s :=
  hs.closure.set_average_mem isClosed_closure h0 ht (hfs.mono fun _ hx => subset_closure hx) hfi
#align convex.set_average_mem_closure Convex.set_average_mem_closure

theorem ConvexOn.average_mem_epigraph [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  have ht_mem : ∀ᵐ x ∂μ, (f x, g (f x)) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
    hfs.mono fun x hx => ⟨hx, le_rfl⟩
  exact average_pair hfi hgi ▸
    hg.convex_epigraph.average_mem (hsc.epigraph hgc) ht_mem (hfi.prod_mk hgi)
#align convex_on.average_mem_epigraph ConvexOn.average_mem_epigraph

theorem ConcaveOn.average_mem_hypograph [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  simpa only [mem_setOf_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.average_mem_epigraph hgc.neg hsc hfs hfi hgi.neg
#align concave_on.average_mem_hypograph ConcaveOn.average_mem_hypograph

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points to `s`, then the value of `g` at the average value of `f` is less than or equal to
the average value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`ConvexOn.map_centerMass_le` for a finite sum version of this lemma. -/
theorem ConvexOn.map_average_le [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    g (⨍ x, f x ∂μ) ≤ ⨍ x, g (f x) ∂μ :=
  (hg.average_mem_epigraph hgc hsc hfs hfi hgi).2
#align convex_on.map_average_le ConvexOn.map_average_le

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points to `s`, then the average value of `g ∘ f` is less than or equal to the value of `g`
at the average value of `f` provided that both `f` and `g ∘ f` are integrable. See also
`ConcaveOn.le_map_centerMass` for a finite sum version of this lemma. -/
theorem ConcaveOn.le_map_average [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, g (f x) ∂μ) ≤ g (⨍ x, f x ∂μ) :=
  (hg.average_mem_hypograph hgc hsc hfs hfi hgi).2
#align concave_on.le_map_average ConcaveOn.le_map_average

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
theorem ConvexOn.set_average_mem_epigraph (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.average_mem_epigraph hgc hsc hfs hfi hgi
#align convex_on.set_average_mem_epigraph ConvexOn.set_average_mem_epigraph

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` is less than or
equal to the value of `g` at the average value of `f` over `t` provided that both `f` and `g ∘ f`
are integrable. -/
theorem ConcaveOn.set_average_mem_hypograph (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  simpa only [mem_setOf_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.set_average_mem_epigraph hgc.neg hsc h0 ht hfs hfi hgi.neg
#align concave_on.set_average_mem_hypograph ConcaveOn.set_average_mem_hypograph

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
theorem ConvexOn.map_set_average_le (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
  (hg.set_average_mem_epigraph hgc hsc h0 ht hfs hfi hgi).2
#align convex_on.map_set_average_le ConvexOn.map_set_average_le

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` is less than or
equal to the value of `g` at the average value of `f` over `t` provided that both `f` and `g ∘ f`
are integrable. -/
theorem ConcaveOn.le_map_set_average (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, g (f x) ∂μ) ≤ g (⨍ x in t, f x ∂μ) :=
  (hg.set_average_mem_hypograph hgc hsc h0 ht hfs hfi hgi).2
#align concave_on.le_map_set_average ConcaveOn.le_map_set_average

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.  points
to `s`, then the value of `g` at the expected value of `f` is less than or equal to the expected
value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`ConvexOn.map_centerMass_le` for a finite sum version of this lemma. -/
theorem ConvexOn.map_integral_le [IsProbabilityMeasure μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by
  simpa only [average_eq_integral] using hg.map_average_le hgc hsc hfs hfi hgi
  -- 🎉 no goals
#align convex_on.map_integral_le ConvexOn.map_integral_le

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.  points
to `s`, then the expected value of `g ∘ f` is less than or equal to the value of `g` at the expected
value of `f` provided that both `f` and `g ∘ f` are integrable. -/
theorem ConcaveOn.le_map_integral [IsProbabilityMeasure μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) ≤ g (∫ x, f x ∂μ) := by
  simpa only [average_eq_integral] using hg.le_map_average hgc hsc hfs hfi hgi
  -- 🎉 no goals
#align concave_on.le_map_integral ConcaveOn.le_map_integral

/-!
### Strict Jensen's inequality
-/


/-- If `f : α → E` is an integrable function, then either it is a.e. equal to the constant
`⨍ x, f x ∂μ` or there exists a measurable set such that `μ t ≠ 0`, `μ tᶜ ≠ 0`, and the average
values of `f` over `t` and `tᶜ` are different. -/
theorem ae_eq_const_or_exists_average_ne_compl [IsFiniteMeasure μ] (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨
      ∃ t, MeasurableSet t ∧ μ t ≠ 0 ∧ μ tᶜ ≠ 0 ∧ (⨍ x in t, f x ∂μ) ≠ ⨍ x in tᶜ, f x ∂μ := by
  refine' or_iff_not_imp_right.mpr fun H => _; push_neg at H
  -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ)
                                               -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ)
  refine' hfi.ae_eq_of_forall_set_integral_eq _ _ (integrable_const _) fun t ht ht' => _; clear ht'
  -- ⊢ ∫ (x : α) in t, f x ∂μ = ∫ (x : α) in t, const α (⨍ (x : α), f x ∂μ) x ∂μ
                                                                                          -- ⊢ ∫ (x : α) in t, f x ∂μ = ∫ (x : α) in t, const α (⨍ (x : α), f x ∂μ) x ∂μ
  simp only [const_apply, set_integral_const]
  -- ⊢ ∫ (x : α) in t, f x ∂μ = ENNReal.toReal (↑↑μ t) • ⨍ (x : α), f x ∂μ
  by_cases h₀ : μ t = 0
  -- ⊢ ∫ (x : α) in t, f x ∂μ = ENNReal.toReal (↑↑μ t) • ⨍ (x : α), f x ∂μ
  · rw [restrict_eq_zero.2 h₀, integral_zero_measure, h₀, ENNReal.zero_toReal, zero_smul]
    -- 🎉 no goals
  by_cases h₀' : μ tᶜ = 0
  -- ⊢ ∫ (x : α) in t, f x ∂μ = ENNReal.toReal (↑↑μ t) • ⨍ (x : α), f x ∂μ
  · rw [← ae_eq_univ] at h₀'
    -- ⊢ ∫ (x : α) in t, f x ∂μ = ENNReal.toReal (↑↑μ t) • ⨍ (x : α), f x ∂μ
    rw [restrict_congr_set h₀', restrict_univ, measure_congr h₀', measure_smul_average]
    -- 🎉 no goals
  have := average_mem_openSegment_compl_self ht.nullMeasurableSet h₀ h₀' hfi
  -- ⊢ ∫ (x : α) in t, f x ∂μ = ENNReal.toReal (↑↑μ t) • ⨍ (x : α), f x ∂μ
  rw [← H t ht h₀ h₀', openSegment_same, mem_singleton_iff] at this
  -- ⊢ ∫ (x : α) in t, f x ∂μ = ENNReal.toReal (↑↑μ t) • ⨍ (x : α), f x ∂μ
  rw [this, measure_smul_setAverage _ (measure_ne_top μ _)]
  -- 🎉 no goals
#align ae_eq_const_or_exists_average_ne_compl ae_eq_const_or_exists_average_ne_compl

/-- If an integrable function `f : α → E` takes values in a convex set `s` and for some set `t` of
positive measure, the average value of `f` over `t` belongs to the interior of `s`, then the average
of `f` over the whole space belongs to the interior of `s`. -/
theorem Convex.average_mem_interior_of_set [IsFiniteMeasure μ] (hs : Convex ℝ s) (h0 : μ t ≠ 0)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (ht : (⨍ x in t, f x ∂μ) ∈ interior s) :
    (⨍ x, f x ∂μ) ∈ interior s := by
  rw [← measure_toMeasurable] at h0; rw [← restrict_toMeasurable (measure_ne_top μ t)] at ht
  -- ⊢ ⨍ (x : α), f x ∂μ ∈ interior s
                                     -- ⊢ ⨍ (x : α), f x ∂μ ∈ interior s
  by_cases h0' : μ (toMeasurable μ t)ᶜ = 0
  -- ⊢ ⨍ (x : α), f x ∂μ ∈ interior s
  · rw [← ae_eq_univ] at h0'
    -- ⊢ ⨍ (x : α), f x ∂μ ∈ interior s
    rwa [restrict_congr_set h0', restrict_univ] at ht
    -- 🎉 no goals
  exact
    hs.openSegment_interior_closure_subset_interior ht
      (hs.set_average_mem_closure h0' (measure_ne_top _ _) (ae_restrict_of_ae hfs)
        hfi.integrableOn)
      (average_mem_openSegment_compl_self (measurableSet_toMeasurable μ t).nullMeasurableSet h0
        h0' hfi)
#align convex.average_mem_interior_of_set Convex.average_mem_interior_of_set

/-- If an integrable function `f : α → E` takes values in a strictly convex closed set `s`, then
either it is a.e. equal to its average value, or its average value belongs to the interior of
`s`. -/
theorem StrictConvex.ae_eq_const_or_average_mem_interior [IsFiniteMeasure μ] (hs : StrictConvex ℝ s)
    (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, f x ∂μ) ∈ interior s := by
  have : ∀ {t}, μ t ≠ 0 → (⨍ x in t, f x ∂μ) ∈ s := fun ht =>
    hs.convex.set_average_mem hsc ht (measure_ne_top _ _) (ae_restrict_of_ae hfs) hfi.integrableOn
  refine' (ae_eq_const_or_exists_average_ne_compl hfi).imp_right _
  -- ⊢ (∃ t, MeasurableSet t ∧ ↑↑μ t ≠ 0 ∧ ↑↑μ tᶜ ≠ 0 ∧ ⨍ (x : α) in t, f x ∂μ ≠ ⨍  …
  rintro ⟨t, hm, h₀, h₀', hne⟩
  -- ⊢ ⨍ (x : α), f x ∂μ ∈ interior s
  exact
    hs.openSegment_subset (this h₀) (this h₀') hne
      (average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' hfi)
#align strict_convex.ae_eq_const_or_average_mem_interior StrictConvex.ae_eq_const_or_average_mem_interior

/-- **Jensen's inequality**, strict version: if an integrable function `f : α → E` takes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly convex on `s`, then
either `f` is a.e. equal to its average value, or `g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ`. -/
theorem StrictConvexOn.ae_eq_const_or_map_average_lt [IsFiniteMeasure μ] (hg : StrictConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ := by
  have : ∀ {t}, μ t ≠ 0 → (⨍ x in t, f x ∂μ) ∈ s ∧ g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
    fun ht =>
    hg.convexOn.set_average_mem_epigraph hgc hsc ht (measure_ne_top _ _) (ae_restrict_of_ae hfs)
      hfi.integrableOn hgi.integrableOn
  refine' (ae_eq_const_or_exists_average_ne_compl hfi).imp_right _
  -- ⊢ (∃ t, MeasurableSet t ∧ ↑↑μ t ≠ 0 ∧ ↑↑μ tᶜ ≠ 0 ∧ ⨍ (x : α) in t, f x ∂μ ≠ ⨍  …
  rintro ⟨t, hm, h₀, h₀', hne⟩
  -- ⊢ g (⨍ (x : α), f x ∂μ) < ⨍ (x : α), g (f x) ∂μ
  rcases average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' (hfi.prod_mk hgi) with
    ⟨a, b, ha, hb, hab, h_avg⟩
  rw [average_pair hfi hgi, average_pair hfi.integrableOn hgi.integrableOn,
    average_pair hfi.integrableOn hgi.integrableOn, Prod.smul_mk,
    Prod.smul_mk, Prod.mk_add_mk, Prod.mk.inj_iff] at h_avg
  simp only [Function.comp] at h_avg
  -- ⊢ g (⨍ (x : α), f x ∂μ) < ⨍ (x : α), g (f x) ∂μ
  rw [← h_avg.1, ← h_avg.2]
  -- ⊢ g (a • ⨍ (x : α) in t, f x ∂μ + b • ⨍ (x : α) in tᶜ, f x ∂μ) < a • ⨍ (x : α) …
  calc
    g ((a • ⨍ x in t, f x ∂μ) + b • ⨍ x in tᶜ, f x ∂μ) <
        a * g (⨍ x in t, f x ∂μ) + b * g (⨍ x in tᶜ, f x ∂μ) :=
      hg.2 (this h₀).1 (this h₀').1 hne ha hb hab
    _ ≤ (a * ⨍ x in t, g (f x) ∂μ) + b * ⨍ x in tᶜ, g (f x) ∂μ :=
      add_le_add (mul_le_mul_of_nonneg_left (this h₀).2 ha.le)
        (mul_le_mul_of_nonneg_left (this h₀').2 hb.le)
#align strict_convex_on.ae_eq_const_or_map_average_lt StrictConvexOn.ae_eq_const_or_map_average_lt

/-- **Jensen's inequality**, strict version: if an integrable function `f : α → E` takes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly concave on `s`, then
either `f` is a.e. equal to its average value, or `⨍ x, g (f x) ∂μ < g (⨍ x, f x ∂μ)`. -/
theorem StrictConcaveOn.ae_eq_const_or_lt_map_average [IsFiniteMeasure μ]
    (hg : StrictConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, g (f x) ∂μ) < g (⨍ x, f x ∂μ) := by
  simpa only [Pi.neg_apply, average_neg, neg_lt_neg_iff] using
    hg.neg.ae_eq_const_or_map_average_lt hgc.neg hsc hfs hfi hgi.neg
#align strict_concave_on.ae_eq_const_or_lt_map_average StrictConcaveOn.ae_eq_const_or_lt_map_average

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm of its average value
is strictly less than `C`. -/
theorem ae_eq_const_or_norm_average_lt_of_norm_le_const [StrictConvexSpace ℝ E]
    (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖⨍ x, f x ∂μ‖ < C := by
  cases' le_or_lt C 0 with hC0 hC0
  -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ) ∨ ‖⨍ (x : α), f x ∂μ‖ < C
  · have : f =ᵐ[μ] 0 := h_le.mono fun x hx => norm_le_zero_iff.1 (hx.trans hC0)
    -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ) ∨ ‖⨍ (x : α), f x ∂μ‖ < C
    simp only [average_congr this, Pi.zero_apply, average_zero]
    -- ⊢ f =ᶠ[ae μ] const α 0 ∨ ‖0‖ < C
    exact Or.inl this
    -- 🎉 no goals
  by_cases hfi : Integrable f μ; swap
  -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ) ∨ ‖⨍ (x : α), f x ∂μ‖ < C
                                 -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ) ∨ ‖⨍ (x : α), f x ∂μ‖ < C
  · simp [average_eq, integral_undef hfi, hC0, ENNReal.toReal_pos_iff]
    -- 🎉 no goals
  cases' (le_top : μ univ ≤ ∞).eq_or_lt with hμt hμt; · simp [average_eq, hμt, hC0]
  -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ) ∨ ‖⨍ (x : α), f x ∂μ‖ < C
                                                        -- 🎉 no goals
  haveI : IsFiniteMeasure μ := ⟨hμt⟩
  -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ) ∨ ‖⨍ (x : α), f x ∂μ‖ < C
  replace h_le : ∀ᵐ x ∂μ, f x ∈ closedBall (0 : E) C; · simpa only [mem_closedBall_zero_iff]
  -- ⊢ ∀ᵐ (x : α) ∂μ, f x ∈ closedBall 0 C
                                                        -- 🎉 no goals
  simpa only [interior_closedBall _ hC0.ne', mem_ball_zero_iff] using
    (strictConvex_closedBall ℝ (0 : E) C).ae_eq_const_or_average_mem_interior isClosed_ball h_le
      hfi
#align ae_eq_const_or_norm_average_lt_of_norm_le_const ae_eq_const_or_norm_average_lt_of_norm_le_const

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm of its integral is
strictly less than `(μ univ).toReal * C`. -/
theorem ae_eq_const_or_norm_integral_lt_of_norm_le_const [StrictConvexSpace ℝ E] [IsFiniteMeasure μ]
    (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖∫ x, f x ∂μ‖ < (μ univ).toReal * C := by
  cases' eq_or_ne μ 0 with h₀ h₀; · left; simp [h₀, EventuallyEq]
  -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ) ∨ ‖∫ (x : α), f x ∂μ‖ < ENNReal.toRea …
                                    -- ⊢ f =ᶠ[ae μ] const α (⨍ (x : α), f x ∂μ)
                                          -- 🎉 no goals
  have hμ : 0 < (μ univ).toReal := by
    simp [ENNReal.toReal_pos_iff, pos_iff_ne_zero, h₀, measure_lt_top]
  refine' (ae_eq_const_or_norm_average_lt_of_norm_le_const h_le).imp_right fun H => _
  -- ⊢ ‖∫ (x : α), f x ∂μ‖ < ENNReal.toReal (↑↑μ univ) * C
  rwa [average_eq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hμ, ← div_eq_inv_mul,
    div_lt_iff' hμ] at H
#align ae_eq_const_or_norm_integral_lt_of_norm_le_const ae_eq_const_or_norm_integral_lt_of_norm_le_const

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e. on a set `t` of finite measure, then either this function is a.e. equal to its average value on
`t`, or the norm of its integral over `t` is strictly less than `(μ t).toReal * C`. -/
theorem ae_eq_const_or_norm_set_integral_lt_of_norm_le_const [StrictConvexSpace ℝ E] (ht : μ t ≠ ∞)
    (h_le : ∀ᵐ x ∂μ.restrict t, ‖f x‖ ≤ C) :
    f =ᵐ[μ.restrict t] const α (⨍ x in t, f x ∂μ) ∨ ‖∫ x in t, f x ∂μ‖ < (μ t).toReal * C := by
  haveI := Fact.mk ht.lt_top
  -- ⊢ f =ᶠ[ae (Measure.restrict μ t)] const α (⨍ (x : α) in t, f x ∂μ) ∨ ‖∫ (x : α …
  rw [← restrict_apply_univ]
  -- ⊢ f =ᶠ[ae (Measure.restrict μ t)] const α (⨍ (x : α) in t, f x ∂μ) ∨ ‖∫ (x : α …
  exact ae_eq_const_or_norm_integral_lt_of_norm_le_const h_le
  -- 🎉 no goals
#align ae_eq_const_or_norm_set_integral_lt_of_norm_le_const ae_eq_const_or_norm_set_integral_lt_of_norm_le_const
