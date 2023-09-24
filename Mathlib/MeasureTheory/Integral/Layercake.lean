/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

#align_import measure_theory.integral.layercake from "leanprover-community/mathlib"@"08a4542bec7242a5c60f179e4e49de8c0d677b1b"

/-!
# The layer cake formula / Cavalieri's principle / tail probability formula

In this file we prove the following layer cake formula.

Consider a non-negative measurable function `f` on a smeasure space. Apply pointwise
to it an increasing absolutely continuous function `G : ℝ≥0 → ℝ≥0` vanishing at the origin, with
derivative `G' = g` on the positive real line (in other words, `G` a primitive of a non-negative
locally integrable function `g` on the positive real line). Then the integral of the result,
`∫ G ∘ f`, can be written as the integral over the positive real line of the "tail measures" of `f`
(i.e., a function giving the measures of the sets on which `f` exceeds different positive real
values) weighted by `g`. In probability theory contexts, the "tail measures" could be referred to
as "tail probabilities" of the random variable `f`, or as values of the "complementary cumulative
distribution function" of the random variable `f`. The terminology "tail probability formula" is
therefore occasionally used for the layer cake formula (or a standard application of it).

The essence of the (mathematical) proof is Fubini's theorem.

We also give the two most common applications of the layer cake formula
 * a representation of the integral of a nonnegative function f:
   ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) ≥ t} dt
 * a representation of the integral of the p:th power of a nonnegative function f:
   ∫ f(ω)^p ∂μ(ω) = p * ∫ t^(p-1) * μ {ω | f(ω) ≥ t} dt .

Variants of the formulas with measures of sets of the form {ω | f(ω) > t} instead of {ω | f(ω) ≥ t}
are also included.

## Main results

 * `lintegral_comp_eq_lintegral_meas_le_mul` and `lintegral_comp_eq_lintegral_meas_lt_mul`:
   The general layer cake formulas with Lebesgue integrals, written in terms of measures of
   sets of the forms {ω | t ≤ f(ω)} and {ω | t < f(ω)}, respectively.
 * `lintegral_eq_lintegral_meas_le` and `lintegral_eq_lintegral_meas_lt`:
   The most common special cases of the layer cake formulas, stating that for a nonnegative
   function f we have ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) ≥ t} dt and
   ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) > t} dt, respectively.
 * `lintegral_rpow_eq_lintegral_meas_le_mul` and `lintegral_rpow_eq_lintegral_meas_lt_mul`:
   Other common special cases of the layer cake formulas, stating that for a nonnegative function f
   and p > 0, we have ∫ f(ω)^p ∂μ(ω) = p * ∫ μ {ω | f(ω) ≥ t} * t^(p-1) dt and
   ∫ f(ω)^p ∂μ(ω) = p * ∫ μ {ω | f(ω) > t} * t^(p-1) dt, respectively.
 * `integral_eq_integral_meas_lt`:
   A Bochner integral version of the most common special case of the layer cake formulas, stating
   that for an integrable and a.e.-nonnegative function f we have
   ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) > t} dt .

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/


noncomputable section

open scoped ENNReal MeasureTheory

open Set MeasureTheory Filter Measure

/-! ### Layercake formula -/


section Layercake

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} {g : ℝ → ℝ} {s : Set α}

/-- An auxiliary version of the layer cake formula (Cavalieri's principle, tail probability
formula), with a measurability assumption that would also essentially follow from the
integrability assumptions.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` and
`lintegral_comp_eq_lintegral_meas_lt_mul` for the main formulations of the layer
cake formula. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable (μ : Measure α) [SigmaFinite μ]
    (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ)
    (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t) (g_mble : Measurable g)
    (g_nn : ∀ t > 0, 0 ≤ g t) :
    (∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ) =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  have g_intble' : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable g volume 0 t := by
    intro t ht
    cases' eq_or_lt_of_le ht with h h
    · simp [← h]
    · exact g_intble t h
  have integrand_eq : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (∫ t in (0)..f ω, g t) = (∫⁻ t in Ioc 0 (f ω), ENNReal.ofReal (g t)) := by
    filter_upwards [f_nn] with ω fω_nn
    have g_ae_nn : 0 ≤ᵐ[volume.restrict (Ioc 0 (f ω))] g := by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc : MeasurableSet (Ioc 0 (f ω)))]
        with x hx using g_nn x hx.1
    rw [← ofReal_integral_eq_lintegral_ofReal (g_intble' (f ω) fω_nn).1 g_ae_nn]
    congr
    exact intervalIntegral.integral_of_le fω_nn
  rw [lintegral_congr_ae integrand_eq]
  simp_rw [← lintegral_indicator (fun t => ENNReal.ofReal (g t)) measurableSet_Ioc]
  -- Porting note: was part of `simp_rw` on the previous line, but didn't trigger.
  rw [← lintegral_indicator _ measurableSet_Ioi, lintegral_lintegral_swap]
  · apply congr_arg
    funext s
    have aux₁ :
      (fun x => (Ioc 0 (f x)).indicator (fun t : ℝ => ENNReal.ofReal (g t)) s) = fun x =>
        ENNReal.ofReal (g s) * (Ioi (0 : ℝ)).indicator (fun _ => 1) s *
          (Ici s).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (f x) := by
      funext a
      by_cases s ∈ Ioc (0 : ℝ) (f a)
      · simp only [h, show s ∈ Ioi (0 : ℝ) from h.1, show f a ∈ Ici s from h.2, indicator_of_mem,
          mul_one]
      · have h_copy := h
        simp only [mem_Ioc, not_and, not_le] at h
        by_cases h' : 0 < s
        · simp only [h_copy, h h', indicator_of_not_mem, not_false_iff, mem_Ici, not_le, mul_zero]
        · have : s ∉ Ioi (0 : ℝ) := h'
          simp only [this, h', indicator_of_not_mem, not_false_iff, mul_zero,
            zero_mul, mem_Ioc, false_and_iff]
    simp_rw [aux₁]
    rw [lintegral_const_mul']
    swap;
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      by_cases h : (0 : ℝ) < s <;> · simp [h]
    simp_rw [show
        (fun a => (Ici s).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (f a)) = fun a =>
          {a : α | s ≤ f a}.indicator (fun _ => 1) a
        by funext a; by_cases s ≤ f a <;> simp [h]]
    rw [lintegral_indicator₀]
    swap; · exact f_mble.nullMeasurable measurableSet_Ici
    rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter, indicator_mul_left,
      mul_assoc,
      show
        (Ioi 0).indicator (fun _x : ℝ => (1 : ℝ≥0∞)) s * μ {a : α | s ≤ f a} =
          (Ioi 0).indicator (fun _x : ℝ => 1 * μ {a : α | s ≤ f a}) s
        by by_cases 0 < s <;> simp [h]]
    simp_rw [mul_comm _ (ENNReal.ofReal _), one_mul]
    rfl
  have aux₂ :
    (Function.uncurry fun (x : α) (y : ℝ) =>
        (Ioc 0 (f x)).indicator (fun t : ℝ => ENNReal.ofReal (g t)) y) =
      {p : α × ℝ | p.2 ∈ Ioc 0 (f p.1)}.indicator fun p => ENNReal.ofReal (g p.2) := by
    funext p
    cases p with | mk p_fst p_snd => ?_
    rw [Function.uncurry_apply_pair]
    by_cases p_snd ∈ Ioc 0 (f p_fst)
    · have h' : (p_fst, p_snd) ∈ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
    · have h' : (p_fst, p_snd) ∉ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := h
      rw [Set.indicator_of_not_mem h', Set.indicator_of_not_mem h]
  rw [aux₂]
  have mble₀ : NullMeasurableSet {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} (μ.prod volume) := by
    simpa only [mem_univ, Pi.zero_apply, gt_iff_lt, not_lt, ge_iff_le, true_and] using
      nullMeasurableSet_region_between_oc μ measurable_zero.aemeasurable f_mble MeasurableSet.univ
  exact (ENNReal.measurable_ofReal.comp (g_mble.comp measurable_snd)).aemeasurable.indicator₀ mble₀
#align measure_theory.lintegral_comp_eq_lintegral_meas_le_mul_of_measurable MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul_of_measurable

theorem Ioc_disjoint_Ioi {α : Type*} [Preorder α] (a : α) {b c : α} (h : b ≤ c) :
    Disjoint (Ioc a b) (Ioi c) :=
  disjoint_left.mpr (fun _ hx hy ↦ (hx.2.trans h).not_lt hy)

open scoped Topology


theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable' (μ : Measure α)
    (f_nn : 0 ≤ f) (f_mble : Measurable f)
    (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t) (g_mble : Measurable g)
    (g_nn : ∀ t > 0, 0 ≤ g t) :
    (∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ) =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  have f_nonneg : ∀ ω, 0 ≤ f ω := fun ω ↦ f_nn ω
  -- trivial case where `g` is ae zero. Then both integrals vanish.
  by_cases H1 : g =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0
  · have A : ∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ = 0 := by
      have : ∀ ω, ∫ t in (0)..f ω, g t = ∫ t in (0)..f ω, 0 := by
        intro ω
        simp_rw [intervalIntegral.integral_of_le (f_nonneg ω)]
        apply integral_congr_ae
        exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self H1
      simp [this]
    have B : ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) = 0 := by
      have : (fun t ↦ μ {a : α | t ≤ f a} * ENNReal.ofReal (g t))
        =ᵐ[volume.restrict (Ioi (0:ℝ))] 0 := by
          filter_upwards [H1] with t ht using by simp [ht]
      simp [lintegral_congr_ae this]
    rw [A, B]
  -- easy case where both sides are obviously infinite: for some `s`, one has
  -- `μ {a : α | s < f a} = ∞` and moreover `g` is not ae zero on `[0, s]`.
  by_cases H2 : ∃ s > 0, 0 < ∫ t in (0)..s, g t ∧ μ {a : α | s < f a} = ∞
  · rcases H2 with ⟨s, s_pos, hs, h's⟩
    rw [intervalIntegral.integral_of_le s_pos.le] at hs
    /- The first integral is infinite, as for `t ∈ [0, s]` one has `μ {a : α | t ≤ f a} = ∞`,
    and moreover the additional integral `g` is not uniformly zero. -/
    have A : ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) = ∞ := by
      rw [eq_top_iff]
      calc
      ∞ = ∫⁻ t in Ioc 0 s, ∞ * ENNReal.ofReal (g t) := by
          have I_pos : ∫⁻ (a : ℝ) in Ioc 0 s, ENNReal.ofReal (g a) ≠ 0 := by
            rw [← ofReal_integral_eq_lintegral_ofReal (g_intble s s_pos).1]
            · simpa only [not_lt, ge_iff_le, ne_eq, ENNReal.ofReal_eq_zero, not_le] using hs
            · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using g_nn _ ht.1
          rw [lintegral_const_mul, ENNReal.top_mul I_pos]
          exact ENNReal.measurable_ofReal.comp g_mble
      _ ≤ ∫⁻ t in Ioc 0 s, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
          apply set_lintegral_mono' measurableSet_Ioc (fun x hx ↦ ?_)
          rw [← h's]
          gcongr
          exact measure_mono (fun a ha ↦ hx.2.trans (le_of_lt ha))
      _ ≤ ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) :=
          lintegral_mono_set Ioc_subset_Ioi_self
    /- The second integral is infinite, as one integrate on those `ω` where `f ω > s`: this is
    an infinite measure set, and on it the integrand is bounded below by `∫ t in 0..s, g t`
    which is positive. -/
    have B : ∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ = ∞ := by
      rw [eq_top_iff]
      calc
      ∞ = ∫⁻ ω in {a | s < f a}, ENNReal.ofReal (∫ t in (0)..s, g t) ∂μ := by
          simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
            h's, ne_eq, ENNReal.ofReal_eq_zero, not_le]
          rw [ENNReal.mul_top]
          simpa [intervalIntegral.integral_of_le s_pos.le] using hs
      _ ≤ ∫⁻ ω in {a | s < f a}, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ := by
          apply set_lintegral_mono' (measurableSet_lt measurable_const f_mble) (fun a ha ↦ ?_)
          apply ENNReal.ofReal_le_ofReal
          apply intervalIntegral.integral_mono_interval le_rfl s_pos.le (le_of_lt ha)
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using g_nn _ ht.1
          · exact g_intble _ (s_pos.trans ha)
      _ ≤ ∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ := set_lintegral_le_lintegral _ _ _
    rw [A, B]
  /- It remains to handle the interesting case, where `g` is not zero, but both integrals are
  not obviously infinite. Let `M` be the largest number such that `g = 0` on `[0, M]`. Then we
  may restrict `μ` to the points where `f ω > M` (as the other ones do not contribute to the
  integral). The restricted measure `ν` is sigma-finite, as `μ` gives finite measure to
  `{ω | f ω > a}` for any `a > M` (otherwise, we would be in the easy case above). Therefore,
  this case follows from the case where the measure is sigma-finite, applied to `ν`. -/
  push_neg at H2
  have M_bdd : BddAbove {s : ℝ | g =ᵐ[volume.restrict (Ioc (0 : ℝ) s)] 0} := by
    contrapose! H1
    have : ∀ (n : ℕ), g =ᵐ[volume.restrict (Ioc (0 : ℝ) n)] 0 := by
      intro n
      rcases not_bddAbove_iff.1 H1 n with ⟨s, hs, ns⟩
      exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ns.le) hs
    have Hg : g =ᵐ[volume.restrict (⋃ (n : ℕ), (Ioc (0 : ℝ) n))] 0 :=
      (ae_restrict_iUnion_iff _ _).2 this
    have : (⋃ (n : ℕ), (Ioc (0 : ℝ) n)) = Ioi 0 :=
      iUnion_Ioc_eq_Ioi_self_iff.2 (fun x hx ↦ exists_nat_ge x)
    rwa [this] at Hg
  let M : ℝ := sSup {s : ℝ | g =ᵐ[volume.restrict (Ioc (0 : ℝ) s)] 0}
  have M_nonneg : 0 ≤ M := le_csSup M_bdd (by simpa using trivial)
  have hgM : g =ᵐ[volume.restrict (Ioc (0 : ℝ) M)] 0 := sorry
  sorry

#exit


  let ν := μ.restrict {a : α | M < f a}
  have : SigmaFinite ν := by
    obtain ⟨u, -, uM, ulim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), M < u n) ∧ Tendsto u atTop (𝓝 M) :=
      exists_seq_strictAnti_tendsto M
    let s : ν.FiniteSpanningSetsIn univ :=
    { set := fun n ↦ {a | f a ≤ M} ∪ {a | u n < f a}
      set_mem := fun n ↦ trivial
      finite := by
        intro n
        have I : ν {a | f a ≤ M} = 0 := by
          rw [Measure.restrict_apply (measurableSet_le f_mble measurable_const)]
          convert measure_empty
          rw [← disjoint_iff_inter_eq_empty]
          exact disjoint_left.mpr (fun a ha ↦ by simpa using ha)
        have J : μ {a | u n < f a} < ∞ := by
          rw [lt_top_iff_ne_top]
          apply H2
          by_contra H3
          rw [not_lt, intervalIntegral.integral_of_le (M_nonneg.trans (uM n).le)] at H3
          have g_nn_ae : ∀ᵐ t ∂(volume.restrict (Ioc 0 (u n))), 0 ≤ g t := by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using g_nn _ hs.1
          have Ig : ∫ (t : ℝ) in Ioc 0 (u n), g t = 0 :=
            le_antisymm H3 (integral_nonneg_of_ae g_nn_ae)
          have J : ∀ᵐ t ∂(volume.restrict (Ioc 0 (u n))), g t = 0 :=
            (integral_eq_zero_iff_of_nonneg_ae g_nn_ae
              (g_intble (u n) (M_nonneg.trans_lt (uM n))).1).1 Ig
          have : u n ≤ M := le_csSup M_bdd J
          exact lt_irrefl _ (this.trans_lt (uM n))
        refine lt_of_le_of_lt (measure_union_le _ _) ?_
        rw [I, zero_add]
        apply lt_of_le_of_lt _ J
        exact restrict_le_self _ (measurableSet_lt measurable_const f_mble)
      spanning := by
        apply eq_univ_iff_forall.2 (fun a ↦ ?_)
        rcases le_or_lt (f a) M with ha|ha
        · exact mem_iUnion.2 ⟨0, Or.inl ha⟩
        · obtain ⟨n, hn⟩ : ∃ n, u n < f a := ((tendsto_order.1 ulim).2 _ ha).exists
          exact mem_iUnion.2 ⟨n, Or.inr hn⟩ }
    exact ⟨⟨s⟩⟩
  have A : ∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ
         = ∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂ν := by
    have meas : MeasurableSet {a | M < f a} := measurableSet_lt measurable_const f_mble
    have I : ∫⁻ (x : α) in {a | M < f a}ᶜ, ENNReal.ofReal (∫ t in (0).. f x, g t) ∂μ
             = ∫⁻ (x : α) in {a | M < f a}ᶜ, 0 ∂μ := by
      apply set_lintegral_congr_fun meas.compl (eventually_of_forall (fun s hs ↦ ?_))
      have : ∫ (t : ℝ) in (0)..f s, g t = ∫ (t : ℝ) in (0)..f s, 0 := by
        simp_rw [intervalIntegral.integral_of_le (f_nonneg s)]
        apply integral_congr_ae
        apply ae_mono (restrict_mono ?_ le_rfl) hgM
        apply Ioc_subset_Ioc_right
        simpa using hs
      simp [this]
    simp only [lintegral_const, zero_mul] at I
    rw [← lintegral_add_compl _ meas, I, add_zero]
  have B : ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t)
           = ∫⁻ t in Ioi 0, ν {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
    have B1 : ∫⁻ t in Ioc 0 M, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t)
         = ∫⁻ t in Ioc 0 M, ν {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
      apply lintegral_congr_ae
      filter_upwards [hgM] with t ht
      simp [ht]
    have B2 : ∫⁻ t in Ioi M, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t)
              = ∫⁻ t in Ioi M, ν {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
      apply set_lintegral_congr_fun measurableSet_Ioi (eventually_of_forall (fun t ht ↦ ?_))
      rw [Measure.restrict_apply (measurableSet_le measurable_const f_mble)]
      congr 3
      exact (inter_eq_left_iff_subset.2 (fun a ha ↦ (mem_Ioi.1 ht).trans_le ha)).symm
    have I : Ioi (0 : ℝ) = Ioc (0 : ℝ) M ∪ Ioi M := (Ioc_union_Ioi_eq_Ioi M_nonneg).symm
    have J : Disjoint (Ioc 0 M) (Ioi M) := Ioc_disjoint_Ioi _ le_rfl
    rw [I, lintegral_union measurableSet_Ioi J, lintegral_union measurableSet_Ioi J, B1, B2]
  rw [A, B]
  exact lintegral_comp_eq_lintegral_meas_le_mul_of_measurable ν
    (ae_mono restrict_le_self f_nn) (f_mble.mono_measure restrict_le_self) g_intble g_mble g_nn





#exit

/-- The layer cake formula / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a sigma-finite measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) ≥ t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0..∞, g(t) * μ {ω | f(ω) ≥ t}`.

See `lintegral_comp_eq_lintegral_meas_lt_mul` for a version with sets of the form `{ω | f(ω) > t}`
instead. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    (∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ) =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  have ex_G : ∃ G : ℝ → ℝ, Measurable G ∧ 0 ≤ G ∧ g =ᵐ[volume.restrict (Ioi 0)] G := by
    refine' AEMeasurable.exists_measurable_nonneg _ g_nn
    exact aemeasurable_Ioi_of_forall_Ioc fun t ht => (g_intble t ht).1.1.aemeasurable
  rcases ex_G with ⟨G, G_mble, G_nn, g_eq_G⟩
  have g_eq_G_on : ∀ t, g =ᵐ[volume.restrict (Ioc 0 t)] G := fun t =>
    ae_mono (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl) g_eq_G
  have G_intble : ∀ t > 0, IntervalIntegrable G volume 0 t := by
    refine' fun t t_pos => ⟨(g_intble t t_pos).1.congr_fun_ae (g_eq_G_on t), _⟩
    rw [Ioc_eq_empty_of_le t_pos.lt.le]
    exact integrableOn_empty
  have eq₁ :
    (∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t)) =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (G t) := by
    apply lintegral_congr_ae
    filter_upwards [g_eq_G] with a ha
    rw [ha]
  have eq₂ : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (∫ t in (0)..f ω, g t) = ENNReal.ofReal (∫ t in (0)..f ω, G t) := by
    filter_upwards [f_nn] with ω fω_nn
    congr 1
    refine' intervalIntegral.integral_congr_ae _
    have fω_nn : 0 ≤ f ω := fω_nn
    rw [uIoc_of_le fω_nn, ←
      ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (f ω)))]
    exact g_eq_G_on (f ω)
  simp_rw [lintegral_congr_ae eq₂, eq₁]
  exact lintegral_comp_eq_lintegral_meas_le_mul_of_measurable μ f_nn f_mble
          G_intble G_mble (fun t _ => G_nn t)
#align measure_theory.lintegral_comp_eq_lintegral_meas_le_mul MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0..∞, μ {ω | f(ω) ≥ t}`.

See `lintegral_eq_lintegral_meas_lt` for a version with sets of the form `{ω | f(ω) > t}`
instead. -/
theorem lintegral_eq_lintegral_meas_le (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) = ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} := by
  set cst := fun _ : ℝ => (1 : ℝ)
  have cst_intble : ∀ t > 0, IntervalIntegrable cst volume 0 t := fun _ _ =>
    intervalIntegrable_const
  have key :=
    lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble cst_intble
      (eventually_of_forall fun _ => zero_le_one)
  simp_rw [ENNReal.ofReal_one, mul_one] at key
  rw [← key]
  congr with ω
  simp only [intervalIntegral.integral_const, sub_zero, Algebra.id.smul_eq_mul, mul_one]
#align measure_theory.lintegral_eq_lintegral_meas_le MeasureTheory.lintegral_eq_lintegral_meas_le



theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable' (μ : Measure α) --[SigmaFinite μ]
    (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) = ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} := by
  by_cases H : ∃ t > 0, μ {a : α | t ≤ f a} = ∞
  ·


#exit


/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0..∞, t^(p-1) * μ {ω | f(ω) ≥ t}`.

See `lintegral_rpow_eq_lintegral_meas_lt_mul` for a version with sets of the form `{ω | f(ω) > t}`
instead. -/
theorem lintegral_rpow_eq_lintegral_meas_le_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) {p : ℝ} (p_pos : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  have one_lt_p : -1 < p - 1 := by linarith
  have obs : ∀ x : ℝ, (∫ t : ℝ in (0)..x, t ^ (p - 1)) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [Real.zero_rpow p_pos.ne.symm]
  set g := fun t : ℝ => t ^ (p - 1)
  have g_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    intro t t_pos
    exact Real.rpow_nonneg_of_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t := fun _ _ =>
    intervalIntegral.intervalIntegrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  rw [← key, ← lintegral_const_mul'' (ENNReal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← ENNReal.ofReal_mul p_pos.le, mul_div_cancel' (f ω ^ p) p_pos.ne.symm]
  · have aux := (@measurable_const ℝ α (by infer_instance) (by infer_instance) p).aemeasurable
                  (μ := μ)
    exact (Measurable.ennreal_ofReal (hf := measurable_id)).comp_aemeasurable
      ((f_mble.pow aux).div_const p)
#align measure_theory.lintegral_rpow_eq_lintegral_meas_le_mul MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul

end MeasureTheory

end Layercake

section LayercakeLT

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

variable {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]

namespace Measure

theorem meas_eq_pos_of_meas_le_ne_meas_lt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {R : Type*} [LinearOrder R]
    {g : α → R} {t : R} (ht : μ {a : α | t ≤ g a} ≠ μ {a : α | t < g a}) :
    0 < μ {a : α | g a = t} := by
  by_contra con
  rw [not_lt, nonpos_iff_eq_zero] at con
  apply ht
  refine le_antisymm ?_ (measure_mono (fun a ha ↦ le_of_lt ha))
  have uni : {a : α | t ≤ g a} = {a : α | t < g a} ∪ {a : α | t = g a} := by
    ext a
    simpa only [mem_setOf, mem_union] using le_iff_lt_or_eq
  rw [show {a : α | t = g a} = {a : α | g a = t} by simp_rw [eq_comm]] at uni
  have μ_le_add := measure_union_le (μ := μ) {a : α | t < g a} {a : α | g a = t}
  rwa [con, add_zero, ← uni] at μ_le_add
#align measure.meas_le_ne_meas_lt_subset_meas_pos Measure.meas_eq_pos_of_meas_le_ne_meas_lt

theorem countable_meas_le_ne_meas_lt₀ [SigmaFinite μ] {R : Type*} [LinearOrder R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {g : α → R} (g_mble : NullMeasurable g μ) :
    {t : R | μ {a : α | t ≤ g a} ≠ μ {a : α | t < g a}}.Countable :=
  Countable.mono (fun _ h ↦ meas_eq_pos_of_meas_le_ne_meas_lt h)
    (Measure.countable_meas_level_set_pos₀ g_mble)

theorem countable_meas_le_ne_meas_lt [SigmaFinite μ] {R : Type*} [LinearOrder R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {g : α → R} (g_mble : Measurable g) :
    {t : R | μ {a : α | t ≤ g a} ≠ μ {a : α | t < g a}}.Countable :=
  countable_meas_le_ne_meas_lt₀ (μ := μ) g_mble.nullMeasurable
#align measure.countable_meas_le_ne_meas_lt Measure.countable_meas_le_ne_meas_lt

theorem meas_le_ae_eq_meas_lt₀ [SigmaFinite μ] {R : Type*} [LinearOrder R] [MeasurableSpace R]
    [MeasurableSingletonClass R] (ν : Measure R) [NoAtoms ν] {g : α → R}
    (g_mble : NullMeasurable g μ) :
    (fun t => μ {a : α | t ≤ g a}) =ᵐ[ν] fun t => μ {a : α | t < g a} :=
  Set.Countable.measure_zero (Measure.countable_meas_le_ne_meas_lt₀ μ g_mble) _

theorem meas_le_ae_eq_meas_lt [SigmaFinite μ] {R : Type*} [LinearOrder R] [MeasurableSpace R]
    [MeasurableSingletonClass R] (ν : Measure R) [NoAtoms ν] {g : α → R} (g_mble : Measurable g) :
    (fun t => μ {a : α | t ≤ g a}) =ᵐ[ν] fun t => μ {a : α | t < g a} :=
  Set.Countable.measure_zero (Measure.countable_meas_le_ne_meas_lt μ g_mble) _
#align measure.meas_le_ae_eq_meas_lt Measure.meas_le_ae_eq_meas_lt

end Measure

variable {f : α → ℝ} {g : ℝ → ℝ} {s : Set α}

/-- The layer cake formula / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a sigma-finite measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) > t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0..∞, g(t) * μ {ω | f(ω) > t}`.

See `lintegral_comp_eq_lintegral_meas_le_mul` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
theorem lintegral_comp_eq_lintegral_meas_lt_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    (∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ) =
      ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (g t) := by
  rw [lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn]
  apply lintegral_congr_ae
  filter_upwards [Measure.meas_le_ae_eq_meas_lt₀ μ (volume.restrict (Ioi 0)) f_mble.nullMeasurable]
    with t ht
  rw [ht]
#align lintegral_comp_eq_lintegral_meas_lt_mul lintegral_comp_eq_lintegral_meas_lt_mul

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0..∞, μ {ω | f(ω) > t}`.

See `lintegral_eq_lintegral_meas_le` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
theorem lintegral_eq_lintegral_meas_lt (μ : Measure α) [SigmaFinite μ]
    (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) = ∫⁻ t in Ioi 0, μ {a : α | t < f a} := by
  rw [lintegral_eq_lintegral_meas_le μ f_nn f_mble]
  apply lintegral_congr_ae
  filter_upwards [Measure.meas_le_ae_eq_meas_lt₀ μ (volume.restrict (Ioi 0)) f_mble.nullMeasurable]
    with t ht
  rw [ht]
#align lintegral_eq_lintegral_meas_lt lintegral_eq_lintegral_meas_lt

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0..∞, t^(p-1) * μ {ω | f(ω) > t}`.

See `lintegral_rpow_eq_lintegral_meas_le_mul` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
theorem lintegral_rpow_eq_lintegral_meas_lt_mul (μ : Measure α) [SigmaFinite μ]
    (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) {p : ℝ} (p_pos : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ f_nn f_mble p_pos]
  apply congr_arg fun z => ENNReal.ofReal p * z
  apply lintegral_congr_ae
  filter_upwards [Measure.meas_le_ae_eq_meas_lt₀ μ (volume.restrict (Ioi 0)) f_mble.nullMeasurable]
    with t ht
  rw [ht]
#align lintegral_rpow_eq_lintegral_meas_lt_mul lintegral_rpow_eq_lintegral_meas_lt_mul

end LayercakeLT

section LayercakeIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If `f` is integrable, then for any `c > 0` the set `{x | ‖f x‖ ≥ c}` has finite measure. -/
lemma Integrable.measure_const_le_norm_lt_top {E : Type*} [NormedAddCommGroup E]
    {f : α → E} (f_intble : Integrable f μ) {c : ℝ} (c_pos : 0 < c) :
    μ {a : α | c ≤ ‖f a‖} < ∞ := by
  borelize E
  have norm_f_aemble : AEMeasurable (fun a ↦ ENNReal.ofReal ‖f a‖) μ :=
    (ENNReal.measurable_ofReal.comp measurable_norm).comp_aemeasurable f_intble.1.aemeasurable
  have markov := mul_meas_ge_le_lintegral₀ (μ := μ) norm_f_aemble (ENNReal.ofReal c)
  have obs : ∫⁻ (a : α), ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ (a : α), ‖f a‖₊ ∂μ :=
    lintegral_congr (fun x ↦ ofReal_norm_eq_coe_nnnorm (f x))
  simp_rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _), obs] at markov
  have c_inv_ne_top : (ENNReal.ofReal c)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr c_pos).ne.symm
  simpa [← mul_assoc,
         ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr c_pos).ne.symm ENNReal.ofReal_ne_top]
    using ENNReal.mul_lt_top c_inv_ne_top (lt_of_le_of_lt markov f_intble.2).ne

/-- If `f` is integrable, then for any `c > 0` the set `{x | ‖f x‖ > c}` has finite measure. -/
lemma Integrable.measure_const_lt_norm_lt_top {E : Type*} [NormedAddCommGroup E]
    {f : α → E} (f_intble : Integrable f μ) {c : ℝ} (c_pos : 0 < c) :
    μ {a : α | c < ‖f a‖} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ h ↦ (Set.mem_setOf_eq ▸ h).le))
    (Integrable.measure_const_le_norm_lt_top f_intble c_pos)

variable {f : α → ℝ}

/-- If `f` is `ℝ`-valued and integrable, then for any `c > 0` the set `{x | f x ≥ c}` has finite
measure. -/
lemma Integrable.measure_const_le_lt_top (f_intble : Integrable f μ) {c : ℝ} (c_pos : 0 < c) :
    μ {a : α | c ≤ f a} < ∞ := by
  refine lt_of_le_of_lt (measure_mono ?_) (Integrable.measure_const_le_norm_lt_top f_intble c_pos)
  intro x hx
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq] at hx ⊢
  exact hx.trans (le_abs_self _)

/-- If `f` is `ℝ`-valued and integrable, then for any `c < 0` the set `{x | f x ≤ c}` has finite
measure. -/
lemma Integrable.measure_le_const_lt_top (f_intble : Integrable f μ) {c : ℝ} (c_neg : c < 0) :
    μ {a : α | f a ≤ c} < ∞ := by
  refine lt_of_le_of_lt (measure_mono ?_)
          (Integrable.measure_const_le_norm_lt_top f_intble (show 0 < -c by linarith))
  intro x hx
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq] at hx ⊢
  exact (show -c ≤ - f x by linarith).trans (neg_le_abs_self _)

/-- If `f` is `ℝ`-valued and integrable, then for any `t > 0` the set `{x | f x > t}` has finite
measure. -/
lemma Integrable.measure_const_lt_lt_top (f_intble : Integrable f μ) {c : ℝ} (c_pos : 0 < c) :
    μ {a : α | c < f a} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx ↦ (Set.mem_setOf_eq ▸ hx).le))
    (Integrable.measure_const_le_lt_top f_intble c_pos)

/-- If `f` is `ℝ`-valued and integrable, then for any `t < 0` the set `{x | f x < t}` has finite
measure. -/
lemma Integrable.measure_lt_const_lt_top (f_intble : Integrable f μ) {c : ℝ} (c_neg : c < 0) :
    μ {a : α | f a < c} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx ↦ (Set.mem_setOf_eq ▸ hx).le))
    (Integrable.measure_le_const_lt_top f_intble c_neg)

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For an integrable a.e.-nonnegative real-valued function `f` on a sigma-finite measure space,
the Bochner integral of `f` can be written (roughly speaking) as:
`∫ f ∂μ = ∫ t in 0..∞, μ {ω | f(ω) > t}`.

See `lintegral_eq_lintegral_meas_lt` for a version with Lebesgue integral `∫⁻` instead. -/
theorem Integrable.integral_eq_integral_meas_lt
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    (∫ ω, f ω ∂μ) = ∫ t in Set.Ioi 0, ENNReal.toReal (μ {a : α | t < f a}) := by
  obtain ⟨s, ⟨_, f_ae_zero_outside, s_sigmafin⟩⟩ :=
    f_intble.aefinStronglyMeasurable.exists_set_sigmaFinite
  have f_nn' : 0 ≤ᵐ[μ.restrict s] f := ae_restrict_of_ae f_nn
  have f_intble' : Integrable f (μ.restrict s) := f_intble.restrict
  have f_aemble' : AEMeasurable f (μ.restrict s) := f_intble.aemeasurable.restrict
  have obs : ∫ ω, f ω ∂μ = ∫ ω, f ω ∂(μ.restrict s) := by
    -- The proof of this observation should be trivial. :(
    refine (set_integral_eq_integral_of_ae_compl_eq_zero ?_).symm
    simp only [EventuallyEq, Filter.Eventually, Pi.zero_apply, Measure.ae,
                 MeasurableSet.compl_iff, Filter.mem_mk, mem_setOf_eq] at f_ae_zero_outside
    simp only [Filter.Eventually, mem_ae_iff]
    rw [Measure.restrict_apply₀] at f_ae_zero_outside
    · apply le_antisymm _ (zero_le _)
      rw [← f_ae_zero_outside]
      apply measure_mono
      intro x hx
      aesop
    · exact NullMeasurableSet.of_null f_ae_zero_outside
  rw [obs]
  have obs' : ∀ t ∈ Ioi (0 : ℝ), (μ {a : α | t < f a}) = ((μ.restrict s) {a : α | t < f a}) := by
    -- The proof of this observation should be trivial. :(
    intro t ht
    rw [Measure.restrict_apply₀]
    · simp only [EventuallyEq, Filter.Eventually, Pi.zero_apply, Measure.ae,
                 MeasurableSet.compl_iff, Filter.mem_mk, mem_setOf_eq] at f_ae_zero_outside
      rw [Measure.restrict_apply₀] at f_ae_zero_outside
      · apply le_antisymm _ (measure_mono (inter_subset_left _ _))
        apply (measure_mono (Eq.symm (inter_union_compl {x | t < f x} s)).le).trans
        apply (measure_union_le _ _).trans
        have wow : μ ({x | t < f x} ∩ sᶜ) = 0 := by
          apply le_antisymm _ (zero_le _)
          rw [← f_ae_zero_outside]
          apply measure_mono
          gcongr
          intro x hx
          simp only [mem_setOf_eq, mem_compl_iff] at hx ⊢
          have : 0 < f x := lt_trans ht hx
          exact this.ne.symm
        simp only [wow, add_zero, le_refl]
      · exact NullMeasurableSet.of_null f_ae_zero_outside
    · exact f_aemble'.nullMeasurable measurableSet_Ioi
  have obs'' := @set_integral_congr ℝ ℝ _ _ (fun t ↦ ENNReal.toReal (μ {a : α | t < f a}))
          (fun t ↦ ENNReal.toReal ((μ.restrict s) {a : α | t < f a})) _ (volume : Measure ℝ) _
          (measurableSet_Ioi (a := (0 : ℝ)))
          (fun x x_in_Ioi ↦ congrArg ENNReal.toReal (obs' x x_in_Ioi))
  rw [obs'']
  have key := lintegral_eq_lintegral_meas_lt (μ.restrict s) f_nn' f_aemble'
  have lhs_finite : ∫⁻ (ω : α), ENNReal.ofReal (f ω) ∂(μ.restrict s) < ∞ :=
    Integrable.lintegral_lt_top f_intble'
  have rhs_finite : ∫⁻ (t : ℝ) in Set.Ioi 0, (μ.restrict s) {a | t < f a} < ∞ :=
    by simp only [← key, lhs_finite]
  have rhs_integrand_finite : ∀ (t : ℝ), t > 0 → (μ.restrict s) {a | t < f a} < ∞ :=
    fun t ht ↦ Integrable.measure_const_lt_lt_top f_intble' ht
  convert (ENNReal.toReal_eq_toReal lhs_finite.ne rhs_finite.ne).mpr key
  · exact integral_eq_lintegral_of_nonneg_ae f_nn' f_intble'.aestronglyMeasurable
  · have aux := @integral_eq_lintegral_of_nonneg_ae _ _ ((volume : Measure ℝ).restrict (Set.Ioi 0))
      (fun t ↦ ENNReal.toReal ((μ.restrict s) {a : α | t < f a})) ?_ ?_
    · rw [aux]
      congr 1
      apply set_lintegral_congr_fun measurableSet_Ioi (eventually_of_forall _)
      exact fun t t_pos ↦ ENNReal.ofReal_toReal (rhs_integrand_finite t t_pos).ne
    · exact eventually_of_forall (fun x ↦ by simp only [Pi.zero_apply, ENNReal.toReal_nonneg])
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      exact Antitone.measurable (fun _ _ hst ↦ measure_mono (fun _ h ↦ lt_of_le_of_lt hst h))

end LayercakeIntegral
