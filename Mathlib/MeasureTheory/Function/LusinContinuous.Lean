/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Michał Świętek
-/
module

public import Mathlib.MeasureTheory.Measure.Tight

/-!
# Lusin's theorem

There are many different versions of Lusin's theorem. All of them roughly say that a measurable
function is continuous on nearly all its domain. Different ways of proving Lusin's theorem can be
classified into roughly two types. The first type considers measures that can be approximated
(from inside) by closed/compact sets and relies on Egoroff's theorem. The second type considers
measures that can be approximated by open sets and the proof does not rely on Egoroff's theorem.
The second type yields more general results as it proves Lusin's theorem for functions taking values
in an arbitrary second countable space. In order to prove them, we introduce the concept of smooth
measures, which in particular are satisfied by every outer regular σ-finite measures and every
finite measures defined on a perfectly normal space.

## Main results

### Global versions (`∃ s, p s ∧ μ sᶜ ≤ ε ∧ ContinuousOn f s`)
* `Measurable.exists_continuous_restrict`: measurable `s`, requires `Smooth μ`.
* `AEMeasurable.exists_continuous_restrict`: null-measurable `s`, for a.e. measurable functions.
* `Measurable.exists_isClosed_restrict`: closed `s`, requires `InternallySmoothClosed μ`.
* `Measurable.exists_isCompact_restrict`: compact `s`, requires `InternallySmoothCompact μ` and
  `T2Space`.

### Localized versions (`∃ K ⊆ A, p K ∧ ContinuousOn f K ∧ μ (A \ K) < ε`)
* `Measurable.exists_isClosed_continuousOn`: closed `K`, requires `InternallySmoothClosed μ`.
* `Measurable.exists_isCompact_continuousOn`: compact `K`, requires `InternallySmoothCompact μ`
  and `T2Space`.

## TODO

In some literatures, it is also mentioned that Lusin's theorem holds for functions taking values
in a arbitrary metric space (without the second countability condition). Prove this version.

## References
*
*
* On the continuity of measurable functions in Neighborhood Spaces by HM Schaerf

## Tags

Lusin's theorem

-/

@[expose] public section


noncomputable section

open scoped symmDiff

open MeasureTheory NNReal ENNReal Topology Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : Set α → Prop}

section prereq

variable [TopologicalSpace α] [TopologicalSpace β]

theorem _root_.Set.iInter_eq_empty_of_eq_empty {i : ι} {f : ι → Set β} (h : f i = ∅) :
    ⋂ j, f j = ∅ :=
  subset_eq_empty (iInter_subset _ i) h

theorem _root_.Set.iUnion_symmDiff_iUnion_subset {f g : ι → Set β} :
    (⋃ n, f n) ∆ ⋃ n, g n ⊆ ⋃ n, f n ∆ g n := by
  intro
  simp_all [symmDiff]
  grind

end prereq

namespace MeasureTheory

namespace Measure

/-- A measure is internally smooth with respect to a predicate `p : Set α → Prop` if measurable sets
can be approximated from inside by sets that satisfy `p`. -/
def InternallySmooth (p : Set α → Prop) (μ : Measure α) : Prop :=
  ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r, 0 < r → ∃ K ⊆ A, p K ∧ μ (A \ K) < r

/-- Using nonstrict inequality results in an equivalent definition. -/
theorem internallySmooth_iff :
    μ.InternallySmooth p ↔
      ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r, 0 < r → ∃ K ⊆ A, p K ∧ μ (A \ K) ≤ r where
  mp hi := by
    intro A hA r hr
    obtain ⟨K, hsub, hp, hlt⟩ := hi hA r hr
    exact ⟨K, hsub, hp, hlt.le⟩
  mpr hi := by
    intro A hA r hr
    by_cases! htop : r ≠ ∞
    · obtain ⟨K, hsub, hp, hlt⟩ := hi hA (r / 2) (ENNReal.half_pos hr.ne.symm)
      exact ⟨K, hsub, hp, hlt.trans_lt (ENNReal.half_lt_self hr.ne.symm htop)⟩
    · obtain ⟨K, hsub, hp, hlt⟩ := hi hA 1 zero_lt_one
      exact ⟨K, hsub, hp, htop ▸ hlt.trans_lt one_lt_top⟩

theorem InternallySmooth.innerRegularWRT (hp : μ.InternallySmooth p) :
    μ.InnerRegularWRT p MeasurableSet := by
  intro A hA r hr
  obtain ⟨K, hsub, hc, hK⟩ := hp hA (μ A - r) (tsub_pos_of_lt hr)
  refine ⟨K, hsub, hc, ?_⟩
  by_contra! hp
  have : μ A < μ A := calc
    _ ≤ μ (A \ K) + μ K := by
      nth_rw 1 [← diff_union_of_subset hsub]
      apply measure_union_le
    _ < μ A - r + r := by
      apply ENNReal.add_lt_add_of_lt_of_le _ hK hp
      exact ne_top_of_lt (hp.trans_lt hr)
    _ = μ A := by
      rw [ENNReal.sub_add_eq_add_sub hr.le, ENNReal.add_sub_cancel_right]
      <;> exact ne_top_of_lt hr
  exact this.false

/-- For a finite measure, `InnerRegularWRT` is equivalent with `InternallySmooth`. -/
theorem InnerRegularWRT.internallySmooth [IsFiniteMeasure μ] (hp : p ∅)
    (hpm : ∀ s, p s → MeasurableSet s) (hm : μ.InnerRegularWRT p MeasurableSet) :
    μ.InternallySmooth p := by
  refine internallySmooth_iff.2 fun A hA r hr => ?_
  by_cases! hrr : μ A ≤ r
  · exact ⟨∅, empty_subset _, hp, by simp [hrr]⟩
  · obtain ⟨K, hsub, hp, hlt⟩ := hm hA (μ A - r)
      (ENNReal.sub_lt_self (by finiteness) (hr.trans hrr).ne.symm hr.ne.symm)
    refine ⟨K, hsub, hp, ?_⟩
    calc
    _ = μ A - μ K := measure_diff hsub (hpm K hp).nullMeasurableSet (by finiteness)
    _ ≤ _ := (ENNReal.sub_lt_of_sub_lt (measure_mono hsub) (Or.inl (by finiteness)) hlt).le

variable [TopologicalSpace α] [TopologicalSpace β]

/-- A measure is internally smooth with respect to closed sets if measurable sets can be
approximated from inside by closed sets. -/
class InternallySmoothClosed (μ : Measure α) : Prop where
  internally_smooth_closed : μ.InternallySmooth IsClosed

theorem InternallySmoothClosed.innerRegularWRT [μ.InternallySmoothClosed] :
    μ.InnerRegularWRT IsClosed MeasurableSet :=
  InternallySmooth.innerRegularWRT internally_smooth_closed

theorem InnerRegularWRT.internallySmoothClosed [IsFiniteMeasure μ] [OpensMeasurableSpace α]
    (hm : μ.InnerRegularWRT IsClosed MeasurableSet) :
    μ.InternallySmoothClosed where
  internally_smooth_closed := hm.internallySmooth isClosed_empty (fun _ => IsClosed.measurableSet)

/-- A measure is internally smooth with respect to compact sets if measurable sets can be
approximated from inside by compact sets. -/
class InternallySmoothCompact (μ : Measure α) : Prop where
  internally_smooth_compact : μ.InternallySmooth IsCompact

instance InternallySmoothCompact.innerRegular [μ.InternallySmoothCompact] :
    μ.InnerRegular where
  innerRegular := InternallySmooth.innerRegularWRT internally_smooth_compact

instance InnerRegular.internallySmoothCompact [IsFiniteMeasure μ] [μ.InnerRegular]
    [OpensMeasurableSpace α] [T2Space α] :
    μ.InternallySmoothCompact where
  internally_smooth_compact :=
    InnerRegular.innerRegular.internallySmooth isCompact_empty (fun _ => IsCompact.measurableSet)

theorem InternallySmoothCompact.isTightMeasureSet [μ.InternallySmoothCompact] :
    IsTightMeasureSet {μ} := by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun r hr => ?_
  obtain ⟨K, _, hc, hlt⟩ := internally_smooth_compact (μ := μ) MeasurableSet.univ r hr
  refine ⟨K, hc, fun _ _ => ?_⟩
  simp_all [Set.compl_eq_univ_diff, hlt.le]

instance InternallySmoothCompact.internallySmoothClosed [T2Space α] [μ.InternallySmoothCompact] :
    μ.InternallySmoothClosed where
  internally_smooth_closed A hA r hr := by
    obtain ⟨K, hsub, hc, hlt⟩ := internally_smooth_compact (μ := μ) hA r hr
    exact ⟨K, hsub, hc.isClosed, hlt⟩

lemma isTightMeasureSet_iff_exists_isCompact_measure_compl_lt {𝓧} [MeasurableSpace 𝓧]
    {S : Set (Measure 𝓧)} [TopologicalSpace 𝓧] :
    IsTightMeasureSet S ↔ ∀ ε, 0 < ε → ∃ K : Set 𝓧, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ < ε := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  refine ⟨fun h r hr => ?_, fun h r hr => ?_⟩
  · by_cases! htop : r ≠ ∞
    · obtain ⟨K, hc, hlt⟩ := h (r / 2) (ENNReal.half_pos hr.ne.symm)
      exact ⟨K, hc, fun μ hμ => (hlt μ hμ).trans_lt (ENNReal.half_lt_self hr.ne.symm htop)⟩
    · obtain ⟨K, hc, hlt⟩ := h 1 zero_lt_one
      exact ⟨K, hc, htop ▸ fun μ hμ => (hlt μ hμ).trans_lt one_lt_top⟩
  · obtain ⟨K, hc, hlt⟩ := h r hr
    exact ⟨K, hc, fun μ hμ => (hlt μ hμ).le⟩

theorem InternallySmoothClosed.internallySmoothCompact_of_isTightMeasureSet
    [μ.InternallySmoothClosed] (ht : IsTightMeasureSet {μ}) :
    μ.InternallySmoothCompact where
  internally_smooth_compact A hA r hr := by
    obtain ⟨K, hcp, hk⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_lt.1 ht)
      (r / 2) (ENNReal.half_pos hr.ne.symm)
    obtain ⟨C, hsub, hc, hl⟩ := internally_smooth_closed (μ := μ) hA (r / 2)
      (ENNReal.half_pos hr.ne.symm)
    refine ⟨K ∩ C, inter_subset_right.trans hsub, hcp.inter_right hc, ?_⟩
    calc
    _ ≤ μ (A \ K) + μ (A \ C) := by grw [diff_inter, measure_union_le]
    _ < r / 2 + r / 2 := by
      have : μ (A \ K) < r / 2 := (measure_mono <| diff_subset_compl _ _).trans_lt <|
        hk μ (mem_singleton _)
      exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_lt this) this.le hl
    _ = _ := by norm_num

instance [PerfectlyNormalSpace α] [IsFiniteMeasure μ] [BorelSpace α] :
    μ.InternallySmoothClosed := by
  refine ⟨internallySmooth_iff.2 fun A hA r hr => ?_⟩
  have hm : m = borel α := BorelSpace.measurable_eq (α := α)
  have hApprox :
      ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r, 0 < r →
        ∃ F U, IsClosed F ∧ IsOpen U ∧ F ⊆ A ∧ A ⊆ U ∧ μ (U \ F) < r := by
    apply MeasurableSpace.induction_on_inter
      (C := fun A _ ↦ ∀ r, 0 < r →
        ∃ F U, IsClosed F ∧ IsOpen U ∧ F ⊆ A ∧ A ⊆ U ∧ μ (U \ F) < r)
    · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_isClosed (α := α))
    · exact isPiSystem_isClosed
    · intro r hr
      refine ⟨∅, ∅, isClosed_empty, isOpen_empty, empty_subset _, empty_subset _, ?_⟩
      simp [hr]
    · intro A hA r hr
      have hA : IsClosed A := by simpa using hA
      by_cases htop : r = ∞
      · refine ⟨A, univ, hA, isOpen_univ, subset_rfl, subset_univ _, ?_⟩
        simpa [htop] using measure_lt_top μ (univ \ A)
      · obtain ⟨f, ho, hf⟩ := hA.isGδ.eq_iInter_nat
        rw [← iInter_dissipate] at hf
        have hμ : μ A = ⨅ n, μ (dissipate f n) := by
          rw [hf]
          refine Antitone.measure_iInter antitone_dissipate (fun n => ?_) ⟨0, by finiteness⟩
          refine (MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk => ?_).nullMeasurableSet
          simpa [hm] using (ho k).measurableSet
        obtain ⟨n, hn⟩ : ∃ n, μ (dissipate f n) < μ A + r := by
          rw [hμ]
          refine iInf_lt_iff.1 (ENNReal.lt_add_right (lt_top_iff_ne_top.1 ?_) hr.ne')
          apply (iInf_le _ 0).trans_lt
          finiteness
        have hsub : A ⊆ dissipate f n := by
          grw [hf, iInter_subset]
        refine ⟨A, dissipate f n, hA, ?_, subset_rfl, hsub, ?_⟩
        · have := biInter_eq_iInter {y | y ≤ n} (fun y hy => f y)
          simp_all only [dissipate, mem_setOf_eq]
          exact isOpen_iInter_of_finite fun x => ho x.1
        · calc
            μ (dissipate f n \ A) = μ (dissipate f n) - μ A := by
              rw [measure_diff hsub hA.measurableSet.nullMeasurableSet (by finiteness)]
            _ < r := (ENNReal.sub_lt_iff_lt_right (by finiteness) (measure_mono hsub)).2 <|
              by simpa [add_comm] using hn
    · intro A hA hA' r hr
      by_cases htop : r = ∞
      · refine ⟨∅, univ, isClosed_empty, isOpen_univ, empty_subset _, subset_univ _, ?_⟩
        simpa [htop] using measure_lt_top μ univ
      obtain ⟨F, U, hF, hU, hFA, hAU, hμ⟩ := hA' r hr
      refine ⟨Uᶜ, Fᶜ, hU.isClosed_compl, hF.isOpen_compl, ?_, ?_, ?_⟩
      · exact compl_subset_compl.mpr hAU
      · exact compl_subset_compl.mpr hFA
      · simpa [diff_eq, inter_assoc, inter_left_comm, inter_comm] using hμ
    · intro f hf hfm hA r hr
      by_cases htop : r = ∞
      · refine ⟨∅, univ, isClosed_empty, isOpen_univ, empty_subset _, subset_univ _, ?_⟩
        simpa [htop] using measure_lt_top μ univ
      choose F U hF hU hFA hAU hμ using fun n =>
        hA n (r * 2 ^ (-1 - n : ℤ))
          (ENNReal.mul_pos hr.ne' (ENNReal.zpow_pos (by simp) (by simp) (-1 - n)).ne')
      have hFacc : ∀ n, IsClosed (Set.accumulate F n) := by
        intro n
        induction n with
        | zero =>
            simpa [Set.accumulate_zero_nat] using hF 0
        | succ n ih =>
            simpa [Set.accumulate_succ] using ih.union (hF (n + 1))
      have hlt :
          μ ((⋃ n, U n) \ ⋃ n, F n) < r := by
        have hsum_eq : (∑' (n : ℕ), r * 2 ^ (-1 - n : ℤ)) = r := by
          simp [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one]
        have hsum_lt :
            (∑' n, μ (U n \ F n)) < ∑' (n : ℕ), r * 2 ^ (-1 - n : ℤ) := by
          have hg_ne_top : (∑' (n : ℕ), r * 2 ^ (-1 - n : ℤ)) ≠ ∞ := by
            simpa [hsum_eq] using htop
          apply ENNReal.tsum_lt_tsum
          · exact ne_top_of_le_ne_top hg_ne_top <| ENNReal.tsum_le_tsum fun n => (hμ n).le
          · exact fun n => (hμ n).le
          · exact hμ 0
        calc
          μ ((⋃ n, U n) \ ⋃ n, F n) ≤ μ (⋃ n, U n \ F n) := by
            apply measure_mono
            intro x hx
            rcases mem_iUnion.1 hx.1 with ⟨n, hn⟩
            exact mem_iUnion.2 ⟨n, ⟨hn, fun hxF => hx.2 <| mem_iUnion.2 ⟨n, hxF⟩⟩⟩
          _ ≤ ∑' n, μ (U n \ F n) := measure_iUnion_le _
          _ < ∑' (n : ℕ), r * 2 ^ (-1 - n : ℤ) := hsum_lt
          _ = r := hsum_eq
      have hInter :
          (⋂ i, (⋃ n, U n) \ F i) = (⋃ n, U n) \ ⋃ n, F n := by
        ext x
        simp only [mem_iInter, mem_diff, mem_iUnion]
        constructor
        · intro h
          refine ⟨(h 0).1, ?_⟩
          rintro ⟨i, hxi⟩
          exact (h i).2 hxi
        · intro h i
          exact ⟨h.1, fun hxi => h.2 ⟨i, hxi⟩⟩
      have hlt' : μ (⋂ i, (⋃ n, U n) \ F i) < r := by simpa [hInter] using hlt
      have hlim :
          Tendsto (fun n ↦ μ (⋂ j ≤ n, (⋃ i, U i) \ F j)) atTop
            (𝓝 (μ (⋂ i, (⋃ n, U n) \ F i))) :=
        tendsto_measure_iInter_le
          (f := fun n => (⋃ i, U i) \ F n)
          (fun n => ((isOpen_iUnion hU).measurableSet.diff (hF n).measurableSet).nullMeasurableSet)
          ⟨0, by finiteness⟩
      have h_event : ∀ᶠ n in atTop, μ ((⋃ i, U i) \ Set.accumulate F n) < r :=
        by
          have hIntern (n : ℕ) :
              (⋂ j ≤ n, (⋃ i, U i) \ F j) = (⋃ i, U i) \ Set.accumulate F n := by
            ext x
            simp only [Set.accumulate, mem_iInter, mem_diff, mem_iUnion, exists_prop]
            constructor
            · intro h
              refine ⟨(h 0 (Nat.zero_le _)).1, ?_⟩
              rintro ⟨i, hi, hxi⟩
              exact (h i hi).2 hxi
            · intro h i hi
              exact ⟨h.1, fun hxi => h.2 ⟨i, hi, hxi⟩⟩
          have h_event' : ∀ᶠ n in atTop, μ (⋂ j ≤ n, (⋃ i, U i) \ F j) < r :=
            hlim (Iio_mem_nhds hlt')
          filter_upwards [h_event'] with n hn
          simpa [hIntern n] using hn
      obtain ⟨n, hn⟩ := h_event.exists
      refine ⟨Set.accumulate F n, ⋃ i, U i, hFacc n, isOpen_iUnion hU, ?_, ?_, hn⟩
      · intro x hx
        simp only [Set.accumulate, mem_iUnion, exists_prop] at hx
        rcases hx with ⟨i, hi, hx⟩
        exact mem_iUnion.2 ⟨i, hFA i hx⟩
      · exact iUnion_mono hAU
  by_cases htop : r = ∞
  · obtain ⟨F, U, hF, hU, hFA, hAU, hμ⟩ := hApprox hA 1 zero_lt_one
    exact ⟨F, hFA, hF, by simpa [htop] using (le_top : μ (A \ F) ≤ ∞)⟩
  · obtain ⟨F, U, hF, hU, hFA, hAU, hμ⟩ := hApprox hA r hr
    exact ⟨F, hFA, hF, ((measure_mono <| diff_subset_diff_left hAU).trans_lt hμ).le⟩

instance [IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α] [BorelSpace α]
    [IsFiniteMeasure μ] :
    μ.InternallySmoothCompact :=
  InternallySmoothClosed.internallySmoothCompact_of_isTightMeasureSet
    isTightMeasureSet_singleton

/-- A measure is smooth if measurable sets can be approximated by open sets. -/
class Smooth (μ : Measure α) : Prop where
  smooth : ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r, 0 < r → ∃ U, IsOpen U ∧ μ (U ∆ A) ≤ r

theorem smooth_iff_isClosed :
    μ.Smooth ↔ ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r, 0 < r → ∃ U, IsClosed U ∧ μ (U ∆ A) ≤ r where
  mp h A hA r hr := by
    obtain ⟨U, ho, hu⟩ := h.smooth hA.compl r hr
    refine ⟨Uᶜ, ho.isClosed_compl, ?_⟩
    rwa [← compl_compl A, compl_symmDiff_compl]
  mpr h := by
    constructor
    intro A hA r hr
    obtain ⟨U, ho, hu⟩ := h hA.compl r hr
    refine ⟨Uᶜ, ho.isOpen_compl, ?_⟩
    rwa [← compl_compl A, compl_symmDiff_compl]

instance InternallySmoothClosed.Smooth [μ.InternallySmoothClosed] : μ.Smooth := by
  refine smooth_iff_isClosed.2 fun A hA r hr => ?_
  obtain ⟨C, hsub, hc, hlt⟩ := internally_smooth_closed (μ := μ) hA r hr
  refine ⟨C, hc, ?_⟩
  calc
  _ = μ (A \ C) := by congr; ext; grind
  _ ≤ _ := hlt.le

instance [μ.OuterRegular] [SigmaFinite μ] : μ.Smooth where
  smooth A hA r hr := by
    have (n : ℕ) : ∃ U ⊇ spanningSets μ n ∩ A, IsOpen U ∧
        μ (U \ ((spanningSets μ n) ∩ A)) ≤ r * 2 ^ (-1 - n : ℤ) := by
      have hp : μ ((spanningSets μ n) ∩ A) ≠ ⊤ :=
        measure_ne_top_of_subset inter_subset_left (measure_spanningSets_lt_top μ n).ne
      have hq : r * 2 ^ (-1 - n : ℤ) ≠ 0 :=
        (ENNReal.mul_pos hr.ne.symm (ENNReal.zpow_pos (by simp) (by simp) (-1 - n)).ne.symm).ne.symm
      have hm := (measurableSet_spanningSets μ n).inter hA
      obtain ⟨U, hU⟩ := hm.exists_isOpen_diff_lt hp hq
      exact ⟨U, hU.1, hU.2.1, hU.2.2.2.le⟩
    choose U hsub ho hle using this
    refine ⟨⋃ n, U n, isOpen_iUnion ho, ?_⟩
    calc
    _ = μ ((⋃ n, U n) \ A) := by
      suffices ⋃ i, (spanningSets μ i) ∩ A ⊆ ⋃ i, U i from by simp_all [← iUnion_inter, symmDiff]
      exact iUnion_mono'' hsub
    _ ≤ ∑' n, μ (U n \ A) := by simp [iUnion_diff, measure_iUnion_le]
    _ ≤ ∑' n, μ (U n \ (((spanningSets μ n) ∩ A))) := by gcongr; exact inter_subset_right
    _ ≤ ∑' (n : ℕ), r * 2 ^ (-1 - n : ℤ) := by gcongr; apply hle
    _ = _ := by simp [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one]

end Measure

/-! ### Lusin's Theorem for Smooth Measures -/

variable [TopologicalSpace α] [TopologicalSpace β]

/-- A finite borel measure on a perfectly normal space is always smooth. -/
instance [PerfectlyNormalSpace α] [IsFiniteMeasure μ] [BorelSpace α] : μ.Smooth where
  smooth := by
    have (A : Set α) (hA : IsClosed A) (r : ℝ≥0∞) (hr : 0 < r) : ∃ U, IsOpen U ∧ μ (U ∆ A) ≤ r := by
      -- Gδ is the intersection of a decreasing sequence of open sets
      obtain ⟨f, ho, hf⟩ := hA.isGδ.eq_iInter_nat
      rw [← iInter_dissipate] at hf
      have : μ A = ⨅ n, μ (dissipate f n) := by
        rw [hf]
        refine Antitone.measure_iInter antitone_dissipate (fun n => ?_) ⟨0, by finiteness⟩
        refine (MeasurableSet.iInter fun m => MeasurableSet.iInter fun h => ?_).nullMeasurableSet
        exact (ho m).measurableSet
      obtain ⟨n, hn⟩ : ∃ n, μ (dissipate f n) < μ A + r := by
        rw [this]
        refine iInf_lt_iff.1 (ENNReal.lt_add_right (lt_top_iff_ne_top.1 ?_) hr.ne.symm)
        apply (iInf_le _ 0).trans_lt
        finiteness
      -- dissipate open lemma
      refine ⟨dissipate f n, ?_, ?_⟩
      · have := biInter_eq_iInter {y | y ≤ n} (fun y hy => f y)
        simp_all only [dissipate, mem_setOf_eq]
        exact isOpen_iInter_of_finite fun x => ho x.1
      · have : A ⊆ dissipate f n := by grw [hf, iInter_subset]
        calc
        _ = μ (dissipate f n \ A) := by
          congr
          -- turn this into a lemma
          simpa [symmDiff] using subset_union_of_subset_left this _
        _ = μ (dissipate f n) - μ A :=
          measure_diff this hA.measurableSet.nullMeasurableSet (by finiteness)
        _ ≤ r := ((ENNReal.sub_lt_iff_lt_left (by finiteness) (measure_mono this)).2 hn).le
    apply MeasurableSpace.induction_on_inter
    · exact isPiSystem_isClosed
    · exact fun r hr => ⟨∅, by simp⟩
    · exact this
    · intro A hA h r hr
      obtain ⟨U, ho, _⟩ := h (r / 2) (ENNReal.div_pos hr.ne.symm (by simp))
      obtain ⟨V, ho, _⟩ := this Uᶜ ho.isClosed_compl (r / 2) (ENNReal.div_pos hr.ne.symm (by simp))
      refine ⟨V, ho, ?_⟩
      calc
      _ ≤ μ (V ∆ Uᶜ ∪ Uᶜ ∆ Aᶜ) := measure_mono (by grind)
      _ ≤ μ (V ∆ Uᶜ) + μ (Uᶜ ∆ Aᶜ) := measure_union_le _ _
      _ ≤ r / 2 + r / 2 := by rw [compl_symmDiff_compl]; gcongr
      _ = _ := by norm_num
    · intro f hf hfm hp r hr
      choose U ho hl using fun n => hp n (r * 2 ^ (-1 - n : ℤ))
        (ENNReal.mul_pos hr.ne.symm (ENNReal.zpow_pos (by simp) (by simp) _).ne.symm)
      refine ⟨⋃ n, U n, isOpen_iUnion ho, ?_⟩
      calc
      _ ≤ μ (⋃ n, U n ∆ f n) := measure_mono iUnion_symmDiff_iUnion_subset
      _ ≤ ∑' n, μ (U n ∆ f n) := measure_iUnion_le _
      _ ≤ ∑' (n : ℕ), r * 2 ^ (-1 - n : ℤ) := by gcongr; exact hl _
      _ = _ := by simp [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one]
    · simp [BorelSpace.measurable_eq, borel_eq_generateFrom_isClosed]

theorem _root_.PerfectlyNormalSpace.smooth_of_finiteSpanningSetsInOpen [PerfectlyNormalSpace α]
    [BorelSpace α] (hs : μ.FiniteSpanningSetsIn IsOpen) :
    μ.Smooth where
  smooth := by
    intro A hA r hr
    have (n : ℕ) : ∃ U, IsOpen U ∧ μ (U ∆ ((hs.set n) ∩ A)) ≤ r * 2 ^ (-1 - n : ℤ) := by
      have hfm : IsFiniteMeasure (μ.comap Subtype.val : Measure (hs.set n)) := by
        constructor
        rw [(MeasurableEmbedding.subtype_coe (hs.set_mem n).measurableSet).comap_apply,
          Subtype.coe_image_univ]
        exact hs.finite n
      have hrs : (μ.comap Subtype.val : Measure (hs.set n)).Smooth := inferInstance
      have hq : 0 < r * 2 ^ (-1 - n : ℤ) :=
        ENNReal.mul_pos hr.ne.symm (ENNReal.zpow_pos (by simp) (by simp) (-1 - n)).ne.symm
      obtain ⟨U, ho, hl⟩ := hrs.smooth (hA.preimage measurable_subtype_coe)
        (r * 2 ^ (-1 - n : ℤ)) hq
      refine ⟨U, (hs.set_mem n).isOpenMap_subtype_val U ho, ?_⟩
      rwa [(MeasurableEmbedding.subtype_coe (hs.set_mem n).measurableSet).comap_apply,
        image_symmDiff Subtype.val_injective, Subtype.image_preimage_val] at hl
    choose U ho hle using this
    refine ⟨⋃ n, U n, isOpen_iUnion ho, ?_⟩
    calc
    _ = μ ((⋃ n, U n) ∆ ⋃ n, hs.set n ∩ A) := by congr; simp [← iUnion_inter, hs.spanning]
    _ ≤ ∑' n, μ (U n ∆ (hs.set n ∩ A)):= by grw [iUnion_symmDiff_iUnion_subset, measure_iUnion_le]
    _ ≤ ∑' (n : ℕ), r * 2 ^ (-1 - n : ℤ) := by gcongr; apply hle
    _ = _ := by simp [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one]

@[simp]
lemma isTopologicalBasis_empty : IsTopologicalBasis {(∅ : Set α)} ↔ IsEmpty α where
  mp h := by simpa using h.diff_empty
  mpr h := ⟨by simp, by simp [Set.univ_eq_empty_iff.2], Subsingleton.elim ..⟩

theorem _root_.TopologicalSpace.exists_seq_basis (β) [TopologicalSpace β]
    [SecondCountableTopology β] :
    ∃ b : ℕ → Set β, IsTopologicalBasis (range b) := by
  obtain ⟨t, ht⟩ :=  TopologicalSpace.exists_countable_basis β
  by_cases! hn : t.Nonempty
  · obtain ⟨b, rfl⟩ := ht.1.exists_eq_range hn
    exact ⟨b, ht.2.2⟩
  · exact ⟨fun n => ∅, by simp_all⟩

theorem _root_.TopologicalSpace.IsTopologicalBasis.continuousOn_iff {b : Set (Set β)}
    (hb : IsTopologicalBasis b) (f : α → β) (s : Set α) :
    ContinuousOn f s ↔ ∀ t ∈ b, ∃ u, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
  rw [continuousOn_iff']
  refine ⟨fun h t ht => h t (hb.isOpen ht), fun h t ht => ?_⟩
  obtain ⟨ι, g, rfl, hg⟩ := hb.open_eq_iUnion ht
  choose v hv he using (fun i => h (g i) (hg i))
  exact ⟨⋃ i, v i, isOpen_iUnion hv, by simp_all [iUnion_inter]⟩

/-- **Lusin's theorem**: if `f : α → β` is a measurable function, `μ` is smooth, and `β` is second
countable, then for all `ε > 0`, there exists a measurable set `s` such that `μ sᶜ ≤ ε` and the
restriction of `f` onto `s` is continuous. -/
theorem Measurable.exists_continuous_restrict (μ : Measure α) [μ.Smooth]
    {f : α → β} [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : Measurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s, MeasurableSet s ∧ (μ sᶜ ≤ ε) ∧ ContinuousOn f s := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis β
  have hm (n : ℕ) := (hb.isOpen (mem_range_self n)).measurableSet.preimage hf
  have (n : ℕ) : ∃ U, IsOpen U ∧
    μ (U ∆ (f ⁻¹' (b n))) ≤ ε * 2 ^ (-1 - n : ℤ) := by
    refine Measure.Smooth.smooth (hm n) _ ?_
    exact ENNReal.mul_pos hε.ne.symm (ENNReal.zpow_pos (by simp) (by simp) (-1 - n)).ne.symm
  choose g ho hg using this
  refine ⟨(⋃ n, (g n ∆ (f ⁻¹' (b n))))ᶜ, (MeasurableSet.iUnion fun n => ?_).compl, ?_, ?_⟩
  · exact (ho n).measurableSet.symmDiff (hm n)
  · rw [compl_compl]
    calc
    _ ≤ ∑' n, μ (g n ∆ (f ⁻¹' (b n))) := measure_iUnion_le _
    _ ≤ ∑' (n : ℕ), ε * 2 ^ (-1 - n : ℤ) := ENNReal.tsum_le_tsum fun n => hg n
    _ = _ := by simp [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one]
  · rw [hb.continuousOn_iff]
    rintro - ⟨n, rfl⟩
    refine ⟨g n, ho n, subset_antisymm ?_ ?_⟩
    <;> rw [← diff_eq_empty, ← inter_diff_distrib_right, compl_iUnion, inter_iInter]
    <;> apply iInter_eq_empty_of_eq_empty (i := n)
    · simp [symmDiff, ← inter_left_comm]
    · simp [symmDiff, ← inter_assoc]

/-- **Lusin's theorem**: if `f : α → β` is a.e. measurable with respect to `μ`, `μ` is smooth, and
`β` is second countable, then for all `ε > 0`, there exists a null measurable set `s` such that
`μ sᶜ ≤ ε` and the restriction of `f` onto `s` is continuous. -/
theorem AEMeasurable.exists_continuous_restrict [μ.Smooth] {f : α → β}
    [SecondCountableTopology β] [MeasurableSpace β] [MeasurableEq β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s, NullMeasurableSet s μ ∧ (μ sᶜ ≤ ε) ∧ ContinuousOn f s := by
  have := hf
  obtain ⟨g, hg⟩ := hf
  obtain ⟨s, hs, hle, hc⟩ := hg.1.exists_continuous_restrict μ hε
  refine ⟨s ∩ {x | f x = g x}, ?_, ?_, ?_⟩
  · exact hs.nullMeasurableSet.inter (nullMeasurableSet_eq_fun this hg.1.aemeasurable)
  · calc
    _ ≤ μ sᶜ + μ {x | f x = g x}ᶜ := by grw [compl_inter, measure_union_le]
    _ ≤ ε := by
      suffices μ {x | f x = g x}ᶜ = 0 from by simp_all
      simpa [EventuallyEq, ae_iff, ← compl_setOf] using hg.2
  · exact (hc.mono inter_subset_left).congr fun x hx => hx.2

/-! ### Lusin's theorem: closed and compact versions

We provide both **global** versions (matching the shape of `exists_continuous_restrict`:
`∃ s, p s ∧ μ sᶜ ≤ ε ∧ ContinuousOn f s`) and **localized** versions (restricting to a measurable
set `A` of finite measure: `∃ K ⊆ A, p K ∧ ContinuousOn f K ∧ μ (A \ K) < ε`). -/

/-- Helper for global closed/compact Lusin: combines `exists_continuous_restrict` with inner
approximation by sets satisfying `p`. -/
private theorem Measurable.exists_restrict_of_approx (μ : Measure α) [μ.Smooth]
    {f : α → β} [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : Measurable f) {ε : ℝ≥0∞} (hε : 0 < ε)
    {p : Set α → Prop} (h_approx : μ.InternallySmooth p) :
    ∃ s, p s ∧ μ sᶜ ≤ ε ∧ ContinuousOn f s := by
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨s, hs, hsμ, hsc⟩ := hf.exists_continuous_restrict μ hε2
  obtain ⟨K, hK, hpK, hKμ⟩ := h_approx hs (ε / 2) hε2
  refine ⟨K, hpK, ?_, hsc.mono hK⟩
  calc μ Kᶜ
      ≤ μ sᶜ + μ (s \ K) := by
        simp only [compl_eq_univ_diff]
        exact (measure_mono (sdiff_triangle _ s K)).trans (measure_union_le _ _)
    _ ≤ ε / 2 + ε / 2 := add_le_add hsμ hKμ.le
    _ = ε := ENNReal.add_halves ε

/-- **Lusin's theorem** (global, closed): if `f : α → β` is a measurable function, `μ` is
internally smooth with respect to closed sets, and `β` is second countable, then for all `ε > 0`,
there exists a closed set `s` such that `μ sᶜ ≤ ε` and the restriction of `f` onto `s` is
continuous. -/
theorem Measurable.exists_isClosed_restrict (μ : Measure α) [μ.InternallySmoothClosed]
    {f : α → β} [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : Measurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s, IsClosed s ∧ μ sᶜ ≤ ε ∧ ContinuousOn f s :=
  hf.exists_restrict_of_approx μ hε Measure.InternallySmoothClosed.internally_smooth_closed

/-- **Lusin's theorem** (global, compact): if `f : α → β` is a measurable function, `μ` is
internally smooth with respect to compact sets, `α` is T₂, and `β` is second countable, then for
all `ε > 0`, there exists a compact set `s` such that `μ sᶜ ≤ ε` and the restriction of `f` onto
`s` is continuous. -/
theorem Measurable.exists_isCompact_restrict (μ : Measure α) [T2Space α] [μ.InternallySmoothCompact]
    {f : α → β} [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : Measurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s, IsCompact s ∧ μ sᶜ ≤ ε ∧ ContinuousOn f s :=
  hf.exists_restrict_of_approx μ hε Measure.InternallySmoothCompact.internally_smooth_compact

/-- Helper for localized closed/compact Lusin: combines `exists_continuous_restrict` with inner
approximation on a finite-measure set. -/
private theorem Measurable.exists_continuousOn_of_approx[μ.Smooth]
    {f : α → β} [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : Measurable f)
    {A : Set α} (hA : MeasurableSet A) (hAμ : μ A ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε)
    {p : Set α → Prop} (h_approx : μ.InternallySmooth p) :
    ∃ K ⊆ A, p K ∧ ContinuousOn f K ∧ μ (A \ K) < ε := by
  rcases eq_or_ne ε ⊤ with rfl | hε_fin
  · obtain ⟨s, hs, _, hsc⟩ := hf.exists_continuous_restrict μ one_pos
    obtain ⟨K, hK, hpK, _⟩ := h_approx (hA.inter hs) 1 one_pos
    exact ⟨K, hK.trans inter_subset_left, hpK, hsc.mono (hK.trans inter_subset_right),
      (measure_mono diff_subset).trans_lt hAμ.lt_top⟩
  · have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨s, hs, hsμ, hsc⟩ := hf.exists_continuous_restrict μ hε2
    obtain ⟨K, hK, hpK, hKμ⟩ := h_approx (hA.inter hs) (ε / 2) hε2
    refine ⟨K, hK.trans inter_subset_left, hpK, hsc.mono (hK.trans inter_subset_right), ?_⟩
    calc μ (A \ K)
        ≤ μ (A \ (A ∩ s)) + μ ((A ∩ s) \ K) :=
          (measure_mono (sdiff_triangle A (A ∩ s) K)).trans (measure_union_le _ _)
      _ ≤ μ sᶜ + μ ((A ∩ s) \ K) := by
          gcongr; intro x ⟨_, hx⟩; exact fun h ↦ hx ⟨‹_›, h⟩
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add_of_le_of_lt
          (ne_top_of_le_ne_top (ENNReal.div_ne_top hε_fin (by positivity)) hsμ) hsμ hKμ
      _ = ε := ENNReal.add_halves ε

/-- **Lusin's theorem** (localized, closed): if `f : α → β` is a measurable function, `μ` is
internally smooth with respect to closed sets, and `β` is second countable, then for any measurable
set `A` of finite measure and all `ε > 0`, there exists a closed set `K ⊆ A` such that
`μ (A \ K) < ε` and the restriction of `f` onto `K` is continuous. -/
theorem Measurable.exists_isClosed_continuousOn (μ : Measure α) [μ.InternallySmoothClosed]
    {f : α → β} [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : Measurable f)
    {A : Set α} (hA : MeasurableSet A) (hAμ : μ A ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K ⊆ A, IsClosed K ∧ ContinuousOn f K ∧ μ (A \ K) < ε :=
  hf.exists_continuousOn_of_approx hA hAμ hε
    Measure.InternallySmoothClosed.internally_smooth_closed

/-- **Lusin's theorem** (localized, compact): if `f : α → β` is a measurable function, `μ` is
internally smooth with respect to compact sets, `α` is T₂, and `β` is second countable, then for
any measurable set `A` of finite measure and all `ε > 0`, there exists a compact set `K ⊆ A` such
that `μ (A \ K) < ε` and the restriction of `f` onto `K` is continuous. -/
theorem Measurable.exists_isCompact_continuousOn (μ : Measure α) [T2Space α]
    [μ.InternallySmoothCompact]
    {f : α → β} [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : Measurable f)
    {A : Set α} (hA : MeasurableSet A) (hAμ : μ A ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K ⊆ A, IsCompact K ∧ ContinuousOn f K ∧ μ (A \ K) < ε :=
  hf.exists_continuousOn_of_approx hA hAμ hε
    Measure.InternallySmoothCompact.internally_smooth_compact

end MeasureTheory

#lint
#min_imports
