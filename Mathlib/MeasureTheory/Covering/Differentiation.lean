/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Covering.VitaliFamily
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Differentiation of measures

On a second countable metric space with a measure `μ`, consider a Vitali family (i.e., for each `x`
one has a family of sets shrinking to `x`, with a good behavior with respect to covering theorems).
Consider also another measure `ρ`. Then, for almost every `x`, the ratio `ρ a / μ a` converges when
`a` shrinks to `x` along the Vitali family, towards the Radon-Nikodym derivative of `ρ` with
respect to `μ`. This is the main theorem on differentiation of measures.

This theorem is proved in this file, under the name `VitaliFamily.ae_tendsto_rnDeriv`. Note that,
almost surely, `μ a` is eventually positive and finite (see
`VitaliFamily.ae_eventually_measure_pos` and `VitaliFamily.eventually_measure_lt_top`), so the
ratio really makes sense.

For concrete applications, one needs concrete instances of Vitali families, as provided for instance
by `Besicovitch.vitaliFamily` (for balls) or by `Vitali.vitaliFamily` (for doubling measures).

Specific applications to Lebesgue density points and the Lebesgue differentiation theorem are also
derived:

* `VitaliFamily.ae_tendsto_measure_inter_div` states that, for almost every point `x ∈ s`,
  then `μ (s ∩ a) / μ a` tends to `1` as `a` shrinks to `x` along a Vitali family.
* `VitaliFamily.ae_tendsto_average_norm_sub` states that, for almost every point `x`, then the
  average of `y ↦ ‖f y - f x‖` on `a` tends to `0` as `a` shrinks to `x` along a Vitali family.

## Sketch of proof

Let `v` be a Vitali family for `μ`. Assume for simplicity that `ρ` is absolutely continuous with
respect to `μ`, as the case of a singular measure is easier.

It is easy to see that a set `s` on which `liminf ρ a / μ a < q` satisfies `ρ s ≤ q * μ s`, by using
a disjoint subcovering provided by the definition of Vitali families. Similarly for the limsup.
It follows that a set on which `ρ a / μ a` oscillates has measure `0`, and therefore that
`ρ a / μ a` converges almost surely (`VitaliFamily.ae_tendsto_div`). Moreover, on a set where the
limit is close to a constant `c`, one gets `ρ s ∼ c μ s`, using again a covering lemma as above.
It follows that `ρ` is equal to `μ.withDensity (v.limRatio ρ x)`, where `v.limRatio ρ x` is the
limit of `ρ a / μ a` at `x` (which is well defined almost everywhere). By uniqueness of the
Radon-Nikodym derivative, one gets `v.limRatio ρ x = ρ.rnDeriv μ x` almost everywhere, completing
the proof.

There is a difficulty in this sketch: this argument works well when `v.limRatio ρ` is measurable,
but there is no guarantee that this is the case, especially if one doesn't make further assumptions
on the Vitali family. We use an indirect argument to show that `v.limRatio ρ` is always
almost everywhere measurable, again based on the disjoint subcovering argument
(see `VitaliFamily.exists_measurable_supersets_limRatio`), and then proceed as sketched above
but replacing `v.limRatio ρ` by a measurable version called `v.limRatioMeas ρ`.

## Counterexample

The standing assumption in this file is that spaces are second countable. Without this assumption,
measures may be zero locally but nonzero globally, which is not compatible with differentiation
theory (which deduces global information from local one). Here is an example displaying this
behavior.

Define a measure `μ` by `μ s = 0` if `s` is covered by countably many balls of radius `1`,
and `μ s = ∞` otherwise. This is indeed a countably additive measure, which is moreover
locally finite and doubling at small scales. It vanishes on every ball of radius `1`, so all the
quantities in differentiation theory (defined as ratios of measures as the radius tends to zero)
make no sense. However, the measure is not globally zero if the space is big enough.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.9][Federer1996]
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure

open scoped Filter ENNReal MeasureTheory NNReal Topology

variable {α : Type*} [PseudoMetricSpace α] {m0 : MeasurableSpace α} {μ : Measure α}
  (v : VitaliFamily μ)
  {E : Type*} [NormedAddCommGroup E]

namespace VitaliFamily

/-- The limit along a Vitali family of `ρ a / μ a` where it makes sense, and garbage otherwise.
Do *not* use this definition: it is only a temporary device to show that this ratio tends almost
everywhere to the Radon-Nikodym derivative. -/
noncomputable def limRatio (ρ : Measure α) (x : α) : ℝ≥0∞ :=
  limUnder (v.filterAt x) fun a => ρ a / μ a

/-- For almost every point `x`, sufficiently small sets in a Vitali family around `x` have positive
measure. (This is a nontrivial result, following from the covering property of Vitali families). -/
theorem ae_eventually_measure_pos [SecondCountableTopology α] :
    ∀ᵐ x ∂μ, ∀ᶠ a in v.filterAt x, 0 < μ a := by
  set s := {x | ¬∀ᶠ a in v.filterAt x, 0 < μ a} with hs
  simp -zeta only [not_lt, not_eventually, nonpos_iff_eq_zero] at hs
  change μ s = 0
  let f : α → Set (Set α) := fun _ => {a | μ a = 0}
  have h : v.FineSubfamilyOn f s := by
    intro x hx ε εpos
    rw [hs] at hx
    simp only [frequently_filterAt_iff, gt_iff_lt, mem_setOf_eq] at hx
    rcases hx ε εpos with ⟨a, a_sets, ax, μa⟩
    exact ⟨a, ⟨a_sets, μa⟩, ax⟩
  refine le_antisymm ?_ bot_le
  calc
    μ s ≤ ∑' x : h.index, μ (h.covering x) := h.measure_le_tsum
    _ = ∑' x : h.index, 0 := by congr; ext1 x; exact h.covering_mem x.2
    _ = 0 := by simp only [tsum_zero]

/-- For every point `x`, sufficiently small sets in a Vitali family around `x` have finite measure.
(This is a trivial result, following from the fact that the measure is locally finite). -/
theorem eventually_measure_lt_top [IsLocallyFiniteMeasure μ] (x : α) :
    ∀ᶠ a in v.filterAt x, μ a < ∞ :=
  (μ.finiteAt_nhds x).eventually.filter_mono inf_le_left

/-- If two measures `ρ` and `ν` have, at every point of a set `s`, arbitrarily small sets in a
Vitali family satisfying `ρ a ≤ ν a`, then `ρ s ≤ ν s` if `ρ ≪ μ`. -/
theorem measure_le_of_frequently_le [SecondCountableTopology α] [BorelSpace α] {ρ : Measure α}
    (ν : Measure α) [IsLocallyFiniteMeasure ν] (hρ : ρ ≪ μ) (s : Set α)
    (hs : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, ρ a ≤ ν a) : ρ s ≤ ν s := by
  -- this follows from a covering argument using the sets satisfying `ρ a ≤ ν a`.
  apply ENNReal.le_of_forall_pos_le_add fun ε εpos _ => ?_
  obtain ⟨U, sU, U_open, νU⟩ : ∃ (U : Set α), s ⊆ U ∧ IsOpen U ∧ ν U ≤ ν s + ε :=
    exists_isOpen_le_add s ν (ENNReal.coe_pos.2 εpos).ne'
  let f : α → Set (Set α) := fun _ => {a | ρ a ≤ ν a ∧ a ⊆ U}
  have h : v.FineSubfamilyOn f s := by
    apply v.fineSubfamilyOn_of_frequently f s fun x hx => ?_
    have :=
      (hs x hx).and_eventually
        ((v.eventually_filterAt_mem_setsAt x).and
          (v.eventually_filterAt_subset_of_nhds (U_open.mem_nhds (sU hx))))
    apply Frequently.mono this
    rintro a ⟨ρa, _, aU⟩
    exact ⟨ρa, aU⟩
  haveI : Encodable h.index := h.index_countable.toEncodable
  calc
    ρ s ≤ ∑' x : h.index, ρ (h.covering x) := h.measure_le_tsum_of_absolutelyContinuous hρ
    _ ≤ ∑' x : h.index, ν (h.covering x) := ENNReal.tsum_le_tsum fun x => (h.covering_mem x.2).1
    _ = ν (⋃ x : h.index, h.covering x) := by
      rw [measure_iUnion h.covering_disjoint_subtype fun i => h.measurableSet_u i.2]
    _ ≤ ν U := (measure_mono (iUnion_subset fun i => (h.covering_mem i.2).2))
    _ ≤ ν s + ε := νU

theorem eventually_filterAt_integrableOn (x : α) {f : α → E} (hf : LocallyIntegrable f μ) :
    ∀ᶠ a in v.filterAt x, IntegrableOn f a μ := by
  rcases hf x with ⟨w, w_nhds, hw⟩
  filter_upwards [v.eventually_filterAt_subset_of_nhds w_nhds] with a ha
  exact hw.mono_set ha

section

variable [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ] {ρ : Measure α}
  [IsLocallyFiniteMeasure ρ]

/-- If a measure `ρ` is singular with respect to `μ`, then for `μ` almost every `x`, the ratio
`ρ a / μ a` tends to zero when `a` shrinks to `x` along the Vitali family. This makes sense
as `μ a` is eventually positive by `ae_eventually_measure_pos`. -/
theorem ae_eventually_measure_zero_of_singular (hρ : ρ ⟂ₘ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 0) := by
  have A : ∀ ε > (0 : ℝ≥0), ∀ᵐ x ∂μ, ∀ᶠ a in v.filterAt x, ρ a < ε * μ a := by
    intro ε εpos
    set s := {x | ¬∀ᶠ a in v.filterAt x, ρ a < ε * μ a} with hs
    change μ s = 0
    obtain ⟨o, _, ρo, μo⟩ : ∃ o : Set α, MeasurableSet o ∧ ρ o = 0 ∧ μ oᶜ = 0 := hρ
    apply le_antisymm _ bot_le
    calc
      μ s ≤ μ (s ∩ o ∪ oᶜ) := by
        conv_lhs => rw [← inter_union_compl s o]
        gcongr
        apply inter_subset_right
      _ ≤ μ (s ∩ o) + μ oᶜ := measure_union_le _ _
      _ = μ (s ∩ o) := by rw [μo, add_zero]
      _ = (ε : ℝ≥0∞)⁻¹ * (ε • μ) (s ∩ o) := by
        simp only [coe_nnreal_smul_apply, ← mul_assoc, mul_comm _ (ε : ℝ≥0∞)]
        rw [ENNReal.mul_inv_cancel (ENNReal.coe_pos.2 εpos).ne' ENNReal.coe_ne_top, one_mul]
      _ ≤ (ε : ℝ≥0∞)⁻¹ * ρ (s ∩ o) := by
        gcongr _ * ?_
        refine v.measure_le_of_frequently_le ρ smul_absolutelyContinuous _ ?_
        intro x hx
        rw [hs] at hx
        simp only [mem_inter_iff, not_lt, not_eventually, mem_setOf_eq] at hx
        exact hx.1
      _ ≤ (ε : ℝ≥0∞)⁻¹ * ρ o := by gcongr; apply inter_subset_right
      _ = 0 := by rw [ρo, mul_zero]
  obtain ⟨u, _, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ≥0)
  have B : ∀ᵐ x ∂μ, ∀ n, ∀ᶠ a in v.filterAt x, ρ a < u n * μ a :=
    ae_all_iff.2 fun n => A (u n) (u_pos n)
  filter_upwards [B, v.ae_eventually_measure_pos]
  intro x hx h'x
  refine tendsto_order.2 ⟨fun z hz => (ENNReal.not_lt_zero hz).elim, fun z hz => ?_⟩
  obtain ⟨w, w_pos, w_lt⟩ : ∃ w : ℝ≥0, (0 : ℝ≥0∞) < w ∧ (w : ℝ≥0∞) < z :=
    ENNReal.lt_iff_exists_nnreal_btwn.1 hz
  obtain ⟨n, hn⟩ : ∃ n, u n < w := ((tendsto_order.1 u_lim).2 w (ENNReal.coe_pos.1 w_pos)).exists
  filter_upwards [hx n, h'x, v.eventually_measure_lt_top x]
  intro a ha μa_pos μa_lt_top
  grw [ENNReal.div_lt_iff (.inl μa_pos.ne') (.inl μa_lt_top.ne), ha, hn]
  gcongr
  exact μa_lt_top.ne

section AbsolutelyContinuous

variable (hρ : ρ ≪ μ)
include hρ

/-- A set of points `s` satisfying both `ρ a ≤ c * μ a` and `ρ a ≥ d * μ a` at arbitrarily small
sets in a Vitali family has measure `0` if `c < d`. Indeed, the first inequality should imply
that `ρ s ≤ c * μ s`, and the second one that `ρ s ≥ d * μ s`, a contradiction if `0 < μ s`. -/
theorem null_of_frequently_le_of_frequently_ge {c d : ℝ≥0} (hcd : c < d) (s : Set α)
    (hc : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, ρ a ≤ c * μ a)
    (hd : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, (d : ℝ≥0∞) * μ a ≤ ρ a) : μ s = 0 := by
  apply measure_null_of_locally_null s fun x _ => ?_
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : Set α, x ∈ o ∧ IsOpen o ∧ μ o < ∞ :=
    Measure.exists_isOpen_measure_lt_top μ x
  refine ⟨s ∩ o, inter_mem_nhdsWithin _ (o_open.mem_nhds xo), ?_⟩
  let s' := s ∩ o
  by_contra h
  apply lt_irrefl (ρ s')
  calc
    ρ s' ≤ c * μ s' := v.measure_le_of_frequently_le (c • μ) hρ s' fun x hx => hc x hx.1
    _ < d * μ s' := by gcongr; exact measure_ne_top_of_subset inter_subset_right μo.ne
    _ ≤ ρ s' := v.measure_le_of_frequently_le ρ smul_absolutelyContinuous s' fun x hx ↦ hd x hx.1

/-- If `ρ` is absolutely continuous with respect to `μ`, then for almost every `x`,
the ratio `ρ a / μ a` converges as `a` shrinks to `x` along a Vitali family for `μ`. -/
theorem ae_tendsto_div : ∀ᵐ x ∂μ, ∃ c, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 c) := by
  obtain ⟨w, w_count, w_dense, _, w_top⟩ :
    ∃ w : Set ℝ≥0∞, w.Countable ∧ Dense w ∧ 0 ∉ w ∧ ∞ ∉ w :=
    ENNReal.exists_countable_dense_no_zero_top
  have I : ∀ x ∈ w, x ≠ ∞ := fun x xs hx => w_top (hx ▸ xs)
  have A : ∀ c ∈ w, ∀ d ∈ w, c < d → ∀ᵐ x ∂μ,
      ¬((∃ᶠ a in v.filterAt x, ρ a / μ a < c) ∧ ∃ᶠ a in v.filterAt x, d < ρ a / μ a) := by
    intro c hc d hd hcd
    lift c to ℝ≥0 using I c hc
    lift d to ℝ≥0 using I d hd
    apply v.null_of_frequently_le_of_frequently_ge hρ (ENNReal.coe_lt_coe.1 hcd)
    · simp only [and_imp, exists_prop, not_frequently, not_and, not_lt, not_le, not_eventually,
        mem_setOf_eq, mem_compl_iff, not_forall]
      intro x h1x _
      apply h1x.mono fun a ha => ?_
      refine (ENNReal.div_le_iff_le_mul ?_ (Or.inr (bot_le.trans_lt ha).ne')).1 ha.le
      simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]
    · simp only [and_imp, exists_prop, not_frequently, not_and, not_lt, not_le, not_eventually,
        mem_setOf_eq, mem_compl_iff, not_forall]
      intro x _ h2x
      apply h2x.mono fun a ha => ?_
      exact ENNReal.mul_le_of_le_div ha.le
  have B : ∀ᵐ x ∂μ, ∀ c ∈ w, ∀ d ∈ w, c < d →
      ¬((∃ᶠ a in v.filterAt x, ρ a / μ a < c) ∧ ∃ᶠ a in v.filterAt x, d < ρ a / μ a) := by
    simpa only [ae_ball_iff w_count, ae_all_iff]
  filter_upwards [B]
  intro x hx
  exact tendsto_of_no_upcrossings w_dense hx

theorem ae_tendsto_limRatio :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatio ρ x)) := by
  filter_upwards [v.ae_tendsto_div hρ]
  intro x hx
  exact tendsto_nhds_limUnder hx

/-- Given two thresholds `p < q`, the sets `{x | v.limRatio ρ x < p}`
and `{x | q < v.limRatio ρ x}` are obviously disjoint. The key to proving that `v.limRatio ρ` is
almost everywhere measurable is to show that these sets have measurable supersets which are also
disjoint, up to zero measure. This is the content of this lemma. -/
theorem exists_measurable_supersets_limRatio {p q : ℝ≥0} (hpq : p < q) :
    ∃ a b, MeasurableSet a ∧ MeasurableSet b ∧
      {x | v.limRatio ρ x < p} ⊆ a ∧ {x | (q : ℝ≥0∞) < v.limRatio ρ x} ⊆ b ∧ μ (a ∩ b) = 0 := by
  /- Here is a rough sketch, assuming that the measure is finite and the limit is well defined
    everywhere. Let `u := {x | v.limRatio ρ x < p}` and `w := {x | q < v.limRatio ρ x}`. They
    have measurable supersets `u'` and `w'` of the same measure. We will show that these satisfy
    the conclusion of the theorem, i.e., `μ (u' ∩ w') = 0`. For this, note that
    `ρ (u' ∩ w') = ρ (u ∩ w')` (as `w'` is measurable, see `measure_toMeasurable_add_inter_left`).
    The latter set is included in the set where the limit of the ratios is `< p`, and therefore
    its measure is `≤ p * μ (u ∩ w')`. Using the same trick in the other direction gives that this
    is `p * μ (u' ∩ w')`. We have shown that `ρ (u' ∩ w') ≤ p * μ (u' ∩ w')`. Arguing in the same
    way but using the `w` part gives `q * μ (u' ∩ w') ≤ ρ (u' ∩ w')`. If `μ (u' ∩ w')` were nonzero,
    this would be a contradiction as `p < q`.

    For the rigorous proof, we need to work on a part of the space where the measure is finite
    (provided by `spanningSets (ρ + μ)`) and to restrict to the set where the limit is well defined
    (called `s` below, of full measure). Otherwise, the argument goes through.
    -/
  let s := {x | ∃ c, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 c)}
  let o : ℕ → Set α := spanningSets (ρ + μ)
  let u n := s ∩ {x | v.limRatio ρ x < p} ∩ o n
  let w n := s ∩ {x | (q : ℝ≥0∞) < v.limRatio ρ x} ∩ o n
  -- the supersets are obtained by restricting to the set `s` where the limit is well defined, to
  -- a finite measure part `o n`, taking a measurable superset here, and then taking the union over
  -- `n`.
  refine
    ⟨toMeasurable μ sᶜ ∪ ⋃ n, toMeasurable (ρ + μ) (u n),
      toMeasurable μ sᶜ ∪ ⋃ n, toMeasurable (ρ + μ) (w n), ?_, ?_, ?_, ?_, ?_⟩
  -- check that these sets are measurable supersets as required
  · exact
      (measurableSet_toMeasurable _ _).union
        (MeasurableSet.iUnion fun n => measurableSet_toMeasurable _ _)
  · exact
      (measurableSet_toMeasurable _ _).union
        (MeasurableSet.iUnion fun n => measurableSet_toMeasurable _ _)
  · intro x hx
    by_cases h : x ∈ s
    · refine Or.inr (mem_iUnion.2 ⟨spanningSetsIndex (ρ + μ) x, ?_⟩)
      exact subset_toMeasurable _ _ ⟨⟨h, hx⟩, mem_spanningSetsIndex _ _⟩
    · exact Or.inl (subset_toMeasurable μ sᶜ h)
  · intro x hx
    by_cases h : x ∈ s
    · refine Or.inr (mem_iUnion.2 ⟨spanningSetsIndex (ρ + μ) x, ?_⟩)
      exact subset_toMeasurable _ _ ⟨⟨h, hx⟩, mem_spanningSetsIndex _ _⟩
    · exact Or.inl (subset_toMeasurable μ sᶜ h)
  -- it remains to check the nontrivial part that these sets have zero measure intersection.
  -- it suffices to do it for fixed `m` and `n`, as one is taking countable unions.
  suffices H : ∀ m n : ℕ, μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) = 0 by
    have A :
      (toMeasurable μ sᶜ ∪ ⋃ n, toMeasurable (ρ + μ) (u n)) ∩
          (toMeasurable μ sᶜ ∪ ⋃ n, toMeasurable (ρ + μ) (w n)) ⊆
        toMeasurable μ sᶜ ∪
          ⋃ (m) (n), toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n) := by
      simp only [inter_union_distrib_left, union_inter_distrib_right, true_and,
        subset_union_left, union_subset_iff, inter_self]
      refine ⟨?_, ?_, ?_⟩
      · exact inter_subset_right.trans subset_union_left
      · exact inter_subset_left.trans subset_union_left
      · simp_rw [iUnion_inter, inter_iUnion]; exact subset_union_right
    refine le_antisymm ((measure_mono A).trans ?_) bot_le
    calc
      μ (toMeasurable μ sᶜ ∪
        ⋃ (m) (n), toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≤
          μ (toMeasurable μ sᶜ) +
            μ (⋃ (m) (n), toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
        measure_union_le _ _
      _ = μ (⋃ (m) (n), toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := by
        have : μ sᶜ = 0 := v.ae_tendsto_div hρ; rw [measure_toMeasurable, this, zero_add]
      _ ≤ ∑' (m) (n), μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
        ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => measure_iUnion_le _))
      _ = 0 := by simp only [H, tsum_zero]
  -- now starts the nontrivial part of the argument. We fix `m` and `n`, and show that the
  -- measurable supersets of `u m` and `w n` have zero measure intersection by using the lemmas
  -- `measure_toMeasurable_add_inter_left` (to reduce to `u m` or `w n` instead of the measurable
  -- superset) and `measure_le_of_frequently_le` to compare their measures for `ρ` and `μ`.
  intro m n
  have I : (ρ + μ) (u m) ≠ ∞ := by
    apply (lt_of_le_of_lt (measure_mono _) (measure_spanningSets_lt_top (ρ + μ) m)).ne
    exact inter_subset_right
  have J : (ρ + μ) (w n) ≠ ∞ := by
    apply (lt_of_le_of_lt (measure_mono _) (measure_spanningSets_lt_top (ρ + μ) n)).ne
    exact inter_subset_right
  have A :
    ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≤
      p * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
    calc
      ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) =
          ρ (u m ∩ toMeasurable (ρ + μ) (w n)) :=
        measure_toMeasurable_add_inter_left (measurableSet_toMeasurable _ _) I
      _ ≤ (p • μ) (u m ∩ toMeasurable (ρ + μ) (w n)) := by
        refine v.measure_le_of_frequently_le (p • μ) hρ _ fun x hx => ?_
        have L : Tendsto (fun a : Set α => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatio ρ x)) :=
          tendsto_nhds_limUnder hx.1.1.1
        have I : ∀ᶠ b : Set α in v.filterAt x, ρ b / μ b < p := (tendsto_order.1 L).2 _ hx.1.1.2
        apply I.frequently.mono fun a ha => ?_
        rw [coe_nnreal_smul_apply]
        refine (ENNReal.div_le_iff_le_mul ?_ (Or.inr (bot_le.trans_lt ha).ne')).1 ha.le
        simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]
      _ = p * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := by
        simp only [coe_nnreal_smul_apply,
          measure_toMeasurable_add_inter_right (measurableSet_toMeasurable _ _) I]
  have B :
    (q : ℝ≥0∞) * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≤
      ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
    calc
      (q : ℝ≥0∞) * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) =
          (q : ℝ≥0∞) * μ (toMeasurable (ρ + μ) (u m) ∩ w n) := by
        conv_rhs => rw [inter_comm]
        rw [inter_comm, measure_toMeasurable_add_inter_right (measurableSet_toMeasurable _ _) J]
      _ ≤ ρ (toMeasurable (ρ + μ) (u m) ∩ w n) := by
        rw [← coe_nnreal_smul_apply]
        refine v.measure_le_of_frequently_le _ (.smul_left .rfl _) _ ?_
        intro x hx
        have L : Tendsto (fun a : Set α => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatio ρ x)) :=
          tendsto_nhds_limUnder hx.2.1.1
        have I : ∀ᶠ b : Set α in v.filterAt x, (q : ℝ≥0∞) < ρ b / μ b :=
          (tendsto_order.1 L).1 _ hx.2.1.2
        apply I.frequently.mono fun a ha => ?_
        rw [coe_nnreal_smul_apply]
        exact ENNReal.mul_le_of_le_div ha.le
      _ = ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := by
        conv_rhs => rw [inter_comm]
        rw [inter_comm]
        exact (measure_toMeasurable_add_inter_left (measurableSet_toMeasurable _ _) J).symm
  by_contra h
  apply lt_irrefl (ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)))
  calc
    ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≤
        p * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
      A
    _ < q * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := by
      gcongr
      suffices H : (ρ + μ) (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≠ ∞ by
        simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at H
        exact H.2
      apply (lt_of_le_of_lt (measure_mono inter_subset_left) _).ne
      rw [measure_toMeasurable]
      apply lt_of_le_of_lt (measure_mono _) (measure_spanningSets_lt_top (ρ + μ) m)
      exact inter_subset_right
    _ ≤ ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := B

theorem aemeasurable_limRatio : AEMeasurable (v.limRatio ρ) μ := by
  apply ENNReal.aemeasurable_of_exist_almost_disjoint_supersets _ _ fun p q hpq => ?_
  exact v.exists_measurable_supersets_limRatio hρ hpq

/-- A measurable version of `v.limRatio ρ`. Do *not* use this definition: it is only a temporary
device to show that `v.limRatio` is almost everywhere equal to the Radon-Nikodym derivative. -/
noncomputable def limRatioMeas : α → ℝ≥0∞ :=
  (v.aemeasurable_limRatio hρ).mk _

theorem limRatioMeas_measurable : Measurable (v.limRatioMeas hρ) :=
  AEMeasurable.measurable_mk _

theorem ae_tendsto_limRatioMeas :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x)) := by
  filter_upwards [v.ae_tendsto_limRatio hρ, AEMeasurable.ae_eq_mk (v.aemeasurable_limRatio hρ)]
  intro x hx h'x
  rwa [h'x] at hx

/-- If, for all `x` in a set `s`, one has frequently `ρ a / μ a < p`, then `ρ s ≤ p * μ s`, as
proved in `measure_le_of_frequently_le`. Since `ρ a / μ a` tends almost everywhere to
`v.limRatioMeas hρ x`, the same property holds for sets `s` on which `v.limRatioMeas hρ < p`. -/
theorem measure_le_mul_of_subset_limRatioMeas_lt {p : ℝ≥0} {s : Set α}
    (h : s ⊆ {x | v.limRatioMeas hρ x < p}) : ρ s ≤ p * μ s := by
  let t := {x : α | Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x))}
  have A : μ tᶜ = 0 := v.ae_tendsto_limRatioMeas hρ
  suffices H : ρ (s ∩ t) ≤ (p • μ) (s ∩ t) by calc
    ρ s = ρ (s ∩ t ∪ s ∩ tᶜ) := by rw [inter_union_compl]
    _ ≤ ρ (s ∩ t) + ρ (s ∩ tᶜ) := measure_union_le _ _
    _ ≤ (p • μ) (s ∩ t) + ρ tᶜ := by gcongr; apply inter_subset_right
    _ ≤ p * μ (s ∩ t) := by simp [(hρ A)]
    _ ≤ p * μ s := by gcongr; apply inter_subset_left
  refine v.measure_le_of_frequently_le (p • μ) hρ _ fun x hx => ?_
  have I : ∀ᶠ b : Set α in v.filterAt x, ρ b / μ b < p := (tendsto_order.1 hx.2).2 _ (h hx.1)
  apply I.frequently.mono fun a ha => ?_
  rw [coe_nnreal_smul_apply]
  refine (ENNReal.div_le_iff_le_mul ?_ (Or.inr (bot_le.trans_lt ha).ne')).1 ha.le
  simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]

/-- If, for all `x` in a set `s`, one has frequently `q < ρ a / μ a`, then `q * μ s ≤ ρ s`, as
proved in `measure_le_of_frequently_le`. Since `ρ a / μ a` tends almost everywhere to
`v.limRatioMeas hρ x`, the same property holds for sets `s` on which `q < v.limRatioMeas hρ`. -/
theorem mul_measure_le_of_subset_lt_limRatioMeas {q : ℝ≥0} {s : Set α}
    (h : s ⊆ {x | (q : ℝ≥0∞) < v.limRatioMeas hρ x}) : (q : ℝ≥0∞) * μ s ≤ ρ s := by
  let t := {x : α | Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x))}
  have A : μ tᶜ = 0 := v.ae_tendsto_limRatioMeas hρ
  suffices H : (q • μ) (s ∩ t) ≤ ρ (s ∩ t) by calc
    (q • μ) s = (q • μ) (s ∩ t ∪ s ∩ tᶜ) := by rw [inter_union_compl]
    _ ≤ (q • μ) (s ∩ t) + (q • μ) (s ∩ tᶜ) := measure_union_le _ _
    _ ≤ ρ (s ∩ t) + (q • μ) tᶜ := by gcongr; apply inter_subset_right
    _ = ρ (s ∩ t) := by simp [A]
    _ ≤ ρ s := by gcongr; apply inter_subset_left
  refine v.measure_le_of_frequently_le _ (.smul_left .rfl _) _ ?_
  intro x hx
  have I : ∀ᶠ a in v.filterAt x, (q : ℝ≥0∞) < ρ a / μ a := (tendsto_order.1 hx.2).1 _ (h hx.1)
  apply I.frequently.mono fun a ha => ?_
  rw [coe_nnreal_smul_apply]
  exact ENNReal.mul_le_of_le_div ha.le

/-- The points with `v.limRatioMeas hρ x = ∞` have measure `0` for `μ`. -/
theorem measure_limRatioMeas_top : μ {x | v.limRatioMeas hρ x = ∞} = 0 := by
  refine measure_null_of_locally_null _ fun x _ => ?_
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : Set α, x ∈ o ∧ IsOpen o ∧ ρ o < ∞ :=
    Measure.exists_isOpen_measure_lt_top ρ x
  let s := {x : α | v.limRatioMeas hρ x = ∞} ∩ o
  refine ⟨s, inter_mem_nhdsWithin _ (o_open.mem_nhds xo), le_antisymm ?_ bot_le⟩
  have ρs : ρ s ≠ ∞ := measure_ne_top_of_subset inter_subset_right μo.ne
  have A : ∀ q : ℝ≥0, 1 ≤ q → μ s ≤ (q : ℝ≥0∞)⁻¹ * ρ s := by
    intro q hq
    rw [mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le _ (Or.inr ρs), mul_comm]
    · apply v.mul_measure_le_of_subset_lt_limRatioMeas hρ
      intro y hy
      have : v.limRatioMeas hρ y = ∞ := hy.1
      simp only [this, ENNReal.coe_lt_top, mem_setOf_eq]
    · simp only [(zero_lt_one.trans_le hq).ne', true_or, ENNReal.coe_eq_zero, Ne,
        not_false_iff]
  have B : Tendsto (fun q : ℝ≥0 => (q : ℝ≥0∞)⁻¹ * ρ s) atTop (𝓝 (∞⁻¹ * ρ s)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inr ρs)
    exact tendsto_inv_iff.2 (ENNReal.tendsto_coe_nhds_top.2 tendsto_id)
  simp only [zero_mul, ENNReal.inv_top] at B
  apply ge_of_tendsto B
  exact eventually_atTop.2 ⟨1, A⟩

/-- The points with `v.limRatioMeas hρ x = 0` have measure `0` for `ρ`. -/
theorem measure_limRatioMeas_zero : ρ {x | v.limRatioMeas hρ x = 0} = 0 := by
  refine measure_null_of_locally_null _ fun x _ => ?_
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : Set α, x ∈ o ∧ IsOpen o ∧ μ o < ∞ :=
    Measure.exists_isOpen_measure_lt_top μ x
  let s := {x : α | v.limRatioMeas hρ x = 0} ∩ o
  refine ⟨s, inter_mem_nhdsWithin _ (o_open.mem_nhds xo), le_antisymm ?_ bot_le⟩
  have μs : μ s ≠ ∞ := measure_ne_top_of_subset inter_subset_right μo.ne
  have A : ∀ q : ℝ≥0, 0 < q → ρ s ≤ q * μ s := by
    intro q hq
    apply v.measure_le_mul_of_subset_limRatioMeas_lt hρ
    intro y hy
    have : v.limRatioMeas hρ y = 0 := hy.1
    simp only [this, mem_setOf_eq, hq, ENNReal.coe_pos]
  have B : Tendsto (fun q : ℝ≥0 => (q : ℝ≥0∞) * μ s) (𝓝[>] (0 : ℝ≥0)) (𝓝 ((0 : ℝ≥0) * μ s)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inr μs)
    rw [ENNReal.tendsto_coe]
    exact nhdsWithin_le_nhds
  simp only [zero_mul, ENNReal.coe_zero] at B
  apply ge_of_tendsto B
  filter_upwards [self_mem_nhdsWithin] using A

/-- As an intermediate step to show that `μ.withDensity (v.limRatioMeas hρ) = ρ`, we show here
that `μ.withDensity (v.limRatioMeas hρ) ≤ t^2 ρ` for any `t > 1`. -/
theorem withDensity_le_mul {s : Set α} (hs : MeasurableSet s) {t : ℝ≥0} (ht : 1 < t) :
    μ.withDensity (v.limRatioMeas hρ) s ≤ (t : ℝ≥0∞) ^ 2 * ρ s := by
  /- We cut `s` into the sets where `v.limRatioMeas hρ = 0`, where `v.limRatioMeas hρ = ∞`, and
    where `v.limRatioMeas hρ ∈ [t^n, t^(n+1))` for `n : ℤ`. The first and second have measure `0`.
    For the latter, since `v.limRatioMeas hρ` fluctuates by at most `t` on this slice, we can use
    `measure_le_mul_of_subset_limRatioMeas_lt` and `mul_measure_le_of_subset_lt_limRatioMeas` to
    show that the two measures are comparable up to `t` (in fact `t^2` for technical reasons of
    strict inequalities). -/
  have t_ne_zero' : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have t_ne_zero : (t : ℝ≥0∞) ≠ 0 := by simpa only [ENNReal.coe_eq_zero, Ne] using t_ne_zero'
  let ν := μ.withDensity (v.limRatioMeas hρ)
  let f := v.limRatioMeas hρ
  have f_meas : Measurable f := v.limRatioMeas_measurable hρ
  -- Note(kmill): smul elaborator when used for CoeFun fails to get CoeFun instance to trigger
  -- unless you use the `(... :)` notation. Another fix is using `(2 : Nat)`, so this appears
  -- to be an unpleasant interaction with default instances.
  have A : ν (s ∩ f ⁻¹' {0}) ≤ ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' {0}) := by
    apply le_trans _ (zero_le _)
    have M : MeasurableSet (s ∩ f ⁻¹' {0}) := hs.inter (f_meas (measurableSet_singleton _))
    simp only [f, ν, nonpos_iff_eq_zero, M, withDensity_apply, lintegral_eq_zero_iff f_meas]
    apply (ae_restrict_iff' M).2
    exact Eventually.of_forall fun x hx => hx.2
  have B : ν (s ∩ f ⁻¹' {∞}) ≤ ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' {∞}) := by
    apply le_trans (le_of_eq _) (zero_le _)
    apply withDensity_absolutelyContinuous μ _
    rw [← nonpos_iff_eq_zero]
    exact (measure_mono inter_subset_right).trans (v.measure_limRatioMeas_top hρ).le
  have C :
    ∀ n : ℤ,
      ν (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) ≤
        ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
    intro n
    let I := Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))
    have M : MeasurableSet (s ∩ f ⁻¹' I) := hs.inter (f_meas measurableSet_Ico)
    simp only [ν, I, M, withDensity_apply]
    calc
      (∫⁻ x in s ∩ f ⁻¹' I, f x ∂μ) ≤ ∫⁻ _ in s ∩ f ⁻¹' I, (t : ℝ≥0∞) ^ (n + 1) ∂μ :=
        lintegral_mono_ae ((ae_restrict_iff' M).2 (Eventually.of_forall fun x hx => hx.2.2.le))
      _ = (t : ℝ≥0∞) ^ (n + 1) * μ (s ∩ f ⁻¹' I) := by
        simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
      _ = (t : ℝ≥0∞) ^ (2 : ℤ) * ((t : ℝ≥0∞) ^ (n - 1) * μ (s ∩ f ⁻¹' I)) := by
        rw [← mul_assoc, ← ENNReal.zpow_add t_ne_zero ENNReal.coe_ne_top]
        congr 2
        abel
      _ ≤ (t : ℝ≥0∞) ^ (2 : ℤ) * ρ (s ∩ f ⁻¹' I) := by
        gcongr
        rw [← ENNReal.coe_zpow (zero_lt_one.trans ht).ne']
        apply v.mul_measure_le_of_subset_lt_limRatioMeas hρ
        intro x hx
        apply lt_of_lt_of_le _ hx.2.1
        rw [← ENNReal.coe_zpow (zero_lt_one.trans ht).ne', ENNReal.coe_lt_coe, sub_eq_add_neg,
          zpow_add₀ t_ne_zero']
        conv_rhs => rw [← mul_one (t ^ n)]
        gcongr
        rw [zpow_neg_one]
        exact inv_lt_one_of_one_lt₀ ht
  calc
    ν s =
      ν (s ∩ f ⁻¹' {0}) + ν (s ∩ f ⁻¹' {∞}) +
        ∑' n : ℤ, ν (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) :=
      measure_eq_measure_preimage_add_measure_tsum_Ico_zpow ν f_meas hs ht
    _ ≤
        ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' {0}) + ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' {∞}) +
          ∑' n : ℤ, ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' Ico (t ^ n) (t ^ (n + 1))) :=
      (add_le_add (add_le_add A B) (ENNReal.tsum_le_tsum C))
    _ = ((t : ℝ≥0∞) ^ 2 • ρ :) s :=
      (measure_eq_measure_preimage_add_measure_tsum_Ico_zpow ((t : ℝ≥0∞) ^ 2 • ρ) f_meas hs ht).symm

/-- As an intermediate step to show that `μ.withDensity (v.limRatioMeas hρ) = ρ`, we show here
that `ρ ≤ t μ.withDensity (v.limRatioMeas hρ)` for any `t > 1`. -/
theorem le_mul_withDensity {s : Set α} (hs : MeasurableSet s) {t : ℝ≥0} (ht : 1 < t) :
    ρ s ≤ t * μ.withDensity (v.limRatioMeas hρ) s := by
  /- We cut `s` into the sets where `v.limRatioMeas hρ = 0`, where `v.limRatioMeas hρ = ∞`, and
    where `v.limRatioMeas hρ ∈ [t^n, t^(n+1))` for `n : ℤ`. The first and second have measure `0`.
    For the latter, since `v.limRatioMeas hρ` fluctuates by at most `t` on this slice, we can use
    `measure_le_mul_of_subset_limRatioMeas_lt` and `mul_measure_le_of_subset_lt_limRatioMeas` to
    show that the two measures are comparable up to `t`. -/
  have t_ne_zero' : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have t_ne_zero : (t : ℝ≥0∞) ≠ 0 := by simpa only [ENNReal.coe_eq_zero, Ne] using t_ne_zero'
  let ν := μ.withDensity (v.limRatioMeas hρ)
  let f := v.limRatioMeas hρ
  have f_meas : Measurable f := v.limRatioMeas_measurable hρ
  have A : ρ (s ∩ f ⁻¹' {0}) ≤ (t • ν) (s ∩ f ⁻¹' {0}) := by
    refine le_trans (measure_mono inter_subset_right) (le_trans (le_of_eq ?_) (zero_le _))
    exact v.measure_limRatioMeas_zero hρ
  have B : ρ (s ∩ f ⁻¹' {∞}) ≤ (t • ν) (s ∩ f ⁻¹' {∞}) := by
    apply le_trans (le_of_eq _) (zero_le _)
    apply hρ
    rw [← nonpos_iff_eq_zero]
    exact (measure_mono inter_subset_right).trans (v.measure_limRatioMeas_top hρ).le
  have C :
    ∀ n : ℤ,
      ρ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) ≤
        (t • ν) (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
    intro n
    let I := Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))
    have M : MeasurableSet (s ∩ f ⁻¹' I) := hs.inter (f_meas measurableSet_Ico)
    simp only [ν, I, M, withDensity_apply, coe_nnreal_smul_apply]
    calc
      ρ (s ∩ f ⁻¹' I) ≤ (t : ℝ≥0∞) ^ (n + 1) * μ (s ∩ f ⁻¹' I) := by
        rw [← ENNReal.coe_zpow t_ne_zero']
        apply v.measure_le_mul_of_subset_limRatioMeas_lt hρ
        intro x hx
        apply hx.2.2.trans_le (le_of_eq _)
        rw [ENNReal.coe_zpow t_ne_zero']
      _ = ∫⁻ _ in s ∩ f ⁻¹' I, (t : ℝ≥0∞) ^ (n + 1) ∂μ := by
        simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
      _ ≤ ∫⁻ x in s ∩ f ⁻¹' I, t * f x ∂μ := by
        apply lintegral_mono_ae ((ae_restrict_iff' M).2 (Eventually.of_forall fun x hx => ?_))
        grw [add_comm, ENNReal.zpow_add t_ne_zero ENNReal.coe_ne_top, zpow_one, hx.2.1]
      _ = t * ∫⁻ x in s ∩ f ⁻¹' I, f x ∂μ := lintegral_const_mul _ f_meas
  calc
    ρ s =
      ρ (s ∩ f ⁻¹' {0}) + ρ (s ∩ f ⁻¹' {∞}) +
        ∑' n : ℤ, ρ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) :=
      measure_eq_measure_preimage_add_measure_tsum_Ico_zpow ρ f_meas hs ht
    _ ≤
        (t • ν) (s ∩ f ⁻¹' {0}) + (t • ν) (s ∩ f ⁻¹' {∞}) +
          ∑' n : ℤ, (t • ν) (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) :=
      (add_le_add (add_le_add A B) (ENNReal.tsum_le_tsum C))
    _ = (t • ν) s :=
      (measure_eq_measure_preimage_add_measure_tsum_Ico_zpow (t • ν) f_meas hs ht).symm

theorem withDensity_limRatioMeas_eq : μ.withDensity (v.limRatioMeas hρ) = ρ := by
  ext1 s hs
  refine le_antisymm ?_ ?_
  · have : Tendsto (fun t : ℝ≥0 =>
        ((t : ℝ≥0∞) ^ 2 * ρ s : ℝ≥0∞)) (𝓝[>] 1) (𝓝 ((1 : ℝ≥0∞) ^ 2 * ρ s)) := by
      refine ENNReal.Tendsto.mul ?_ ?_ tendsto_const_nhds ?_
      · exact ENNReal.Tendsto.pow (ENNReal.tendsto_coe.2 nhdsWithin_le_nhds)
      · simp only [one_pow, true_or, Ne, not_false_iff, one_ne_zero]
      · simp only [one_pow, Ne, or_true, ENNReal.one_ne_top, not_false_iff]
    simp only [one_pow, one_mul] at this
    refine ge_of_tendsto this ?_
    filter_upwards [self_mem_nhdsWithin] with _ ht
    exact v.withDensity_le_mul hρ hs ht
  · have :
      Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞) * μ.withDensity (v.limRatioMeas hρ) s) (𝓝[>] 1)
        (𝓝 ((1 : ℝ≥0∞) * μ.withDensity (v.limRatioMeas hρ) s)) := by
      refine ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 nhdsWithin_le_nhds) ?_
      simp only [true_or, Ne, not_false_iff, one_ne_zero]
    simp only [one_mul] at this
    refine ge_of_tendsto this ?_
    filter_upwards [self_mem_nhdsWithin] with _ ht
    exact v.le_mul_withDensity hρ hs ht

/-- Weak version of the main theorem on differentiation of measures: given a Vitali family `v`
for a locally finite measure `μ`, and another locally finite measure `ρ`, then for `μ`-almost
every `x` the ratio `ρ a / μ a` converges, when `a` shrinks to `x` along the Vitali family,
towards the Radon-Nikodym derivative of `ρ` with respect to `μ`.

This version assumes that `ρ` is absolutely continuous with respect to `μ`. The general version
without this superfluous assumption is `VitaliFamily.ae_tendsto_rnDeriv`.
-/
theorem ae_tendsto_rnDeriv_of_absolutelyContinuous :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (ρ.rnDeriv μ x)) := by
  have A : (μ.withDensity (v.limRatioMeas hρ)).rnDeriv μ =ᵐ[μ] v.limRatioMeas hρ :=
    rnDeriv_withDensity μ (v.limRatioMeas_measurable hρ)
  rw [v.withDensity_limRatioMeas_eq hρ] at A
  filter_upwards [v.ae_tendsto_limRatioMeas hρ, A] with _ _ h'x
  rwa [h'x]

end AbsolutelyContinuous

variable (ρ)

/-- Main theorem on differentiation of measures: given a Vitali family `v` for a locally finite
measure `μ`, and another locally finite measure `ρ`, then for `μ`-almost every `x` the
ratio `ρ a / μ a` converges, when `a` shrinks to `x` along the Vitali family, towards the
Radon-Nikodym derivative of `ρ` with respect to `μ`. -/
theorem ae_tendsto_rnDeriv :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (ρ.rnDeriv μ x)) := by
  let t := μ.withDensity (ρ.rnDeriv μ)
  have eq_add : ρ = ρ.singularPart μ + t := haveLebesgueDecomposition_add _ _
  have A : ∀ᵐ x ∂μ, Tendsto (fun a => ρ.singularPart μ a / μ a) (v.filterAt x) (𝓝 0) :=
    v.ae_eventually_measure_zero_of_singular (mutuallySingular_singularPart ρ μ)
  have B : ∀ᵐ x ∂μ, t.rnDeriv μ x = ρ.rnDeriv μ x :=
    rnDeriv_withDensity μ (measurable_rnDeriv ρ μ)
  have C : ∀ᵐ x ∂μ, Tendsto (fun a => t a / μ a) (v.filterAt x) (𝓝 (t.rnDeriv μ x)) :=
    v.ae_tendsto_rnDeriv_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)
  filter_upwards [A, B, C] with _ Ax Bx Cx
  convert Ax.add Cx using 1
  · ext1 a
    conv_lhs => rw [eq_add]
    simp only [Pi.add_apply, coe_add, ENNReal.add_div]
  · simp only [Bx, zero_add]

/-! ### Lebesgue density points -/


/-- Given a measurable set `s`, then `μ (s ∩ a) / μ a` converges when `a` shrinks to a typical
point `x` along a Vitali family. The limit is `1` for `x ∈ s` and `0` for `x ∉ s`. This shows that
almost every point of `s` is a Lebesgue density point for `s`. A version for non-measurable sets
holds, but it only gives the first conclusion, see `ae_tendsto_measure_inter_div`. -/
theorem ae_tendsto_measure_inter_div_of_measurableSet {s : Set α} (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, Tendsto (fun a => μ (s ∩ a) / μ a) (v.filterAt x) (𝓝 (s.indicator 1 x)) := by
  haveI : IsLocallyFiniteMeasure (μ.restrict s) :=
    isLocallyFiniteMeasure_of_le restrict_le_self
  filter_upwards [ae_tendsto_rnDeriv v (μ.restrict s), rnDeriv_restrict_self μ hs]
  intro x hx h'x
  simpa only [h'x, restrict_apply' hs, inter_comm] using hx

/-- Given an arbitrary set `s`, then `μ (s ∩ a) / μ a` converges to `1` when `a` shrinks to a
typical point of `s` along a Vitali family. This shows that almost every point of `s` is a
Lebesgue density point for `s`. A stronger version for measurable sets is given
in `ae_tendsto_measure_inter_div_of_measurableSet`. -/
theorem ae_tendsto_measure_inter_div (s : Set α) :
    ∀ᵐ x ∂μ.restrict s, Tendsto (fun a => μ (s ∩ a) / μ a) (v.filterAt x) (𝓝 1) := by
  let t := toMeasurable μ s
  have A :
    ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun a => μ (t ∩ a) / μ a) (v.filterAt x) (𝓝 (t.indicator 1 x)) := by
    apply ae_mono restrict_le_self
    apply ae_tendsto_measure_inter_div_of_measurableSet
    exact measurableSet_toMeasurable _ _
  have B : ∀ᵐ x ∂μ.restrict s, t.indicator 1 x = (1 : ℝ≥0∞) := by
    refine ae_restrict_of_ae_restrict_of_subset (subset_toMeasurable μ s) ?_
    filter_upwards [ae_restrict_mem (measurableSet_toMeasurable μ s)] with _ hx
    simp only [t, hx, Pi.one_apply, indicator_of_mem]
  filter_upwards [A, B] with x hx h'x
  rw [h'x] at hx
  apply hx.congr' _
  filter_upwards [v.eventually_filterAt_measurableSet x] with _ ha
  congr 1
  exact measure_toMeasurable_inter_of_sFinite ha _

/-! ### Lebesgue differentiation theorem -/

theorem ae_tendsto_lintegral_div' {f : α → ℝ≥0∞} (hf : Measurable f) (h'f : (∫⁻ y, f y ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ a) (v.filterAt x) (𝓝 (f x)) := by
  let ρ := μ.withDensity f
  have : IsFiniteMeasure ρ := isFiniteMeasure_withDensity h'f
  filter_upwards [ae_tendsto_rnDeriv v ρ, rnDeriv_withDensity μ hf] with x hx h'x
  rw [← h'x]
  apply hx.congr' _
  filter_upwards [v.eventually_filterAt_measurableSet x] with a ha
  rw [← withDensity_apply f ha]

theorem ae_tendsto_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h'f : (∫⁻ y, f y ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ a) (v.filterAt x) (𝓝 (f x)) := by
  have A : (∫⁻ y, hf.mk f y ∂μ) ≠ ∞ := by
    convert h'f using 1
    apply lintegral_congr_ae
    exact hf.ae_eq_mk.symm
  filter_upwards [v.ae_tendsto_lintegral_div' hf.measurable_mk A, hf.ae_eq_mk] with x hx h'x
  rw [h'x]
  convert hx using 1
  ext1 a
  congr 1
  apply lintegral_congr_ae
  exact ae_restrict_of_ae hf.ae_eq_mk

theorem ae_tendsto_lintegral_enorm_sub_div'_of_integrable {f : α → E} (hf : Integrable f μ)
    (h'f : StronglyMeasurable f) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) / μ a) (v.filterAt x) (𝓝 0) := by
  /- For every `c`, then `(∫⁻ y in a, ‖f y - c‖ₑ ∂μ) / μ a` tends almost everywhere to `‖f x - c‖`.
    We apply this to a countable set of `c` which is dense in the range of `f`, to deduce the
    desired convergence.
    A minor technical inconvenience is that constants are not integrable, so to apply previous
    lemmas we need to replace `c` with the restriction of `c` to a finite measure set `A n` in the
    above sketch. -/
  let A := MeasureTheory.Measure.finiteSpanningSetsInOpen' μ
  rcases h'f.isSeparable_range with ⟨t, t_count, ht⟩
  have main :
    ∀ᵐ x ∂μ,
      ∀ᵉ (n : ℕ) (c ∈ t),
        Tendsto (fun a => (∫⁻ y in a, ‖f y - (A.set n).indicator (fun _ => c) y‖ₑ ∂μ) / μ a)
          (v.filterAt x) (𝓝 ‖f x - (A.set n).indicator (fun _ => c) x‖ₑ) := by
    simp_rw [ae_all_iff, ae_ball_iff t_count]
    intro n c _
    apply ae_tendsto_lintegral_div'
    · refine (h'f.sub ?_).enorm
      exact stronglyMeasurable_const.indicator (IsOpen.measurableSet (A.set_mem n))
    · apply ne_of_lt
      calc
        ∫⁻ y, ‖f y - (A.set n).indicator (fun _ : α => c) y‖ₑ ∂μ
          ≤ ∫⁻ y, ‖f y‖ₑ + ‖(A.set n).indicator (fun _ : α => c) y‖ₑ ∂μ :=
          lintegral_mono fun x ↦ enorm_sub_le
        _ = ∫⁻ y, ‖f y‖ₑ ∂μ + ∫⁻ y, ‖(A.set n).indicator (fun _ : α => c) y‖ₑ ∂μ :=
          lintegral_add_left h'f.enorm _
        _ < ∞ + ∞ :=
          haveI I : Integrable ((A.set n).indicator fun _ : α => c) μ := by
            simp only [integrable_indicator_iff (IsOpen.measurableSet (A.set_mem n)),
              integrableOn_const_iff (C := c), A.finite n, or_true]
          ENNReal.add_lt_add hf.2 I.2
  filter_upwards [main, v.ae_eventually_measure_pos] with x hx h'x
  have M c (hc : c ∈ t) :
      Tendsto (fun a => (∫⁻ y in a, ‖f y - c‖ₑ ∂μ) / μ a) (v.filterAt x) (𝓝 ‖f x - c‖ₑ) := by
    obtain ⟨n, xn⟩ : ∃ n, x ∈ A.set n := by simpa [← A.spanning] using mem_univ x
    specialize hx n c hc
    simp only [xn, indicator_of_mem] at hx
    apply hx.congr' _
    filter_upwards [v.eventually_filterAt_subset_of_nhds (IsOpen.mem_nhds (A.set_mem n) xn),
      v.eventually_filterAt_measurableSet x] with a ha h'a
    congr 1
    apply setLIntegral_congr_fun h'a (fun y hy ↦ ?_)
    simp only [ha hy, indicator_of_mem]
  apply ENNReal.tendsto_nhds_zero.2 fun ε εpos => ?_
  obtain ⟨c, ct, xc⟩ : ∃ c ∈ t, ‖f x - c‖ₑ < ε / 2 := by
    simp_rw [← edist_eq_enorm_sub]
    have : f x ∈ closure t := ht (mem_range_self _)
    exact EMetric.mem_closure_iff.1 this (ε / 2) (ENNReal.half_pos (ne_of_gt εpos))
  filter_upwards [(tendsto_order.1 (M c ct)).2 (ε / 2) xc, h'x, v.eventually_measure_lt_top x] with
    a ha h'a h''a
  apply ENNReal.div_le_of_le_mul
  calc
    (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) ≤ ∫⁻ y in a, ‖f y - c‖ₑ + ‖f x - c‖ₑ ∂μ := by
      apply lintegral_mono fun x => ?_
      simpa only [← edist_eq_enorm_sub] using edist_triangle_right _ _ _
    _ = (∫⁻ y in a, ‖f y - c‖ₑ ∂μ) + ∫⁻ _ in a, ‖f x - c‖ₑ ∂μ :=
      (lintegral_add_right _ measurable_const)
    _ ≤ ε / 2 * μ a + ε / 2 * μ a := by
      gcongr
      · rw [ENNReal.div_lt_iff (Or.inl h'a.ne') (Or.inl h''a.ne)] at ha
        exact ha.le
      · simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
        gcongr
    _ = ε * μ a := by rw [← add_mul, ENNReal.add_halves]

theorem ae_tendsto_lintegral_enorm_sub_div_of_integrable {f : α → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) / μ a) (v.filterAt x) (𝓝 0) := by
  have I : Integrable (hf.1.mk f) μ := hf.congr hf.1.ae_eq_mk
  filter_upwards [v.ae_tendsto_lintegral_enorm_sub_div'_of_integrable I hf.1.stronglyMeasurable_mk,
    hf.1.ae_eq_mk] with x hx h'x
  apply hx.congr _
  intro a
  congr 1
  apply lintegral_congr_ae
  apply ae_restrict_of_ae
  filter_upwards [hf.1.ae_eq_mk] with y hy
  rw [hy, h'x]

theorem ae_tendsto_lintegral_enorm_sub_div {f : α → E} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) / μ a) (v.filterAt x) (𝓝 0) := by
  rcases hf.exists_nat_integrableOn with ⟨u, u_open, u_univ, hu⟩
  have : ∀ n, ∀ᵐ x ∂μ,
      Tendsto (fun a => (∫⁻ y in a, ‖(u n).indicator f y - (u n).indicator f x‖ₑ ∂μ) / μ a)
      (v.filterAt x) (𝓝 0) := by
    intro n
    apply ae_tendsto_lintegral_enorm_sub_div_of_integrable
    exact (integrable_indicator_iff (u_open n).measurableSet).2 (hu n)
  filter_upwards [ae_all_iff.2 this] with x hx
  obtain ⟨n, hn⟩ : ∃ n, x ∈ u n := by simpa only [← u_univ, mem_iUnion] using mem_univ x
  apply Tendsto.congr' _ (hx n)
  filter_upwards [v.eventually_filterAt_subset_of_nhds ((u_open n).mem_nhds hn),
    v.eventually_filterAt_measurableSet x] with a ha h'a
  congr 1
  refine setLIntegral_congr_fun h'a (fun y hy ↦ ?_)
  rw [indicator_of_mem (ha hy) f, indicator_of_mem hn f]

/-- *Lebesgue differentiation theorem*: for almost every point `x`, the
average of `‖f y - f x‖` on `a` tends to `0` as `a` shrinks to `x` along a Vitali family. -/
theorem ae_tendsto_average_norm_sub {f : α → E} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => ⨍ y in a, ‖f y - f x‖ ∂μ) (v.filterAt x) (𝓝 0) := by
  filter_upwards [v.ae_tendsto_lintegral_enorm_sub_div hf] with x hx
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hx
  simp only [ENNReal.toReal_zero] at this
  apply Tendsto.congr' _ this
  filter_upwards [v.eventually_measure_lt_top x, v.eventually_filterAt_integrableOn x hf]
    with a h'a h''a
  simp only [Function.comp_apply, ENNReal.toReal_div, setAverage_eq, div_eq_inv_mul]
  have A : IntegrableOn (fun y => (‖f y - f x‖₊ : ℝ)) a μ := by
    simp_rw [coe_nnnorm]
    exact (h''a.sub (integrableOn_const h'a.ne)).norm
  dsimp [enorm]
  rw [lintegral_coe_eq_integral _ A, ENNReal.toReal_ofReal (by positivity)]
  simp only [coe_nnnorm, measureReal_def]

/-- *Lebesgue differentiation theorem*: for almost every point `x`, the
average of `f` on `a` tends to `f x` as `a` shrinks to `x` along a Vitali family. -/
theorem ae_tendsto_average [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}
    (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => ⨍ y in a, f y ∂μ) (v.filterAt x) (𝓝 (f x)) := by
  filter_upwards [v.ae_tendsto_average_norm_sub hf, v.ae_eventually_measure_pos] with x hx h'x
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hx
  filter_upwards [h'x, v.eventually_measure_lt_top x, v.eventually_filterAt_integrableOn x hf]
    with a ha h'a h''a
  nth_rw 1 [← setAverage_const ha.ne' h'a.ne (f x)]
  simp_rw [setAverage_eq']
  rw [← integral_sub]
  · exact norm_integral_le_integral_norm _
  · exact (integrable_inv_smul_measure ha.ne' h'a.ne).2 h''a
  · exact (integrable_inv_smul_measure ha.ne' h'a.ne).2 (integrableOn_const h'a.ne)

end

end VitaliFamily
