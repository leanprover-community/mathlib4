/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Count

/-!
# Lebesgue integral over finite and countable types, sets and measures

The lemmas in this file require at least one of the following of the Lebesgue integral:
* The type of the set of integration is finite or countable
* The set of integration is finite or countable
* The measure is finite, s-finite or sigma-finite
-/

namespace MeasureTheory

open Set ENNReal NNReal Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section FiniteMeasure

theorem setLIntegral_const_lt_top [IsFiniteMeasure μ] (s : Set α) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∫⁻ _ in s, c ∂μ < ∞ := by
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top (μ.restrict s) univ)

theorem lintegral_const_lt_top [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : ∫⁻ _, c ∂μ < ∞ := by
  simpa only [Measure.restrict_univ] using setLIntegral_const_lt_top (univ : Set α) hc

lemma lintegral_eq_const [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x = c) : ∫⁻ x, f x ∂μ = c := by simp [lintegral_congr_ae hf]

lemma lintegral_le_const [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x ≤ c) : ∫⁻ x, f x ∂μ ≤ c :=
  (lintegral_mono_ae hf).trans_eq (by simp)

lemma iInf_le_lintegral [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) : ⨅ x, f x ≤ ∫⁻ x, f x ∂μ :=
  le_trans (by simp) (iInf_mul_le_lintegral f)

lemma lintegral_le_iSup [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ ≤ ⨆ x, f x :=
  le_trans (lintegral_le_iSup_mul f) (by simp)

variable (μ) in
theorem _root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
    [IsFiniteMeasure μ] {f : α → ℝ≥0∞} (f_bdd : ∃ c : ℝ≥0, ∀ x, f x ≤ c) : ∫⁻ x, f x ∂μ < ∞ := by
  rw [← μ.restrict_univ]
  refine setLIntegral_lt_top_of_le_nnreal (measure_ne_top _ _) ?_
  simpa using f_bdd

end FiniteMeasure

section DiracAndCount

theorem lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a := by
  simp [lintegral_congr_ae (ae_eq_dirac' hf)]

@[simp]
theorem lintegral_dirac [MeasurableSingletonClass α] (a : α) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂dirac a = f a := by simp [lintegral_congr_ae (ae_eq_dirac f)]

theorem setLIntegral_dirac' {a : α} {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫⁻ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact lintegral_dirac' _ hf
  · exact lintegral_zero_measure _

theorem setLIntegral_dirac {a : α} (f : α → ℝ≥0∞) (s : Set α) [MeasurableSingletonClass α]
    [Decidable (a ∈ s)] : ∫⁻ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact lintegral_dirac _ _
  · exact lintegral_zero_measure _

theorem lintegral_count' {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count, lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac' a hf

theorem lintegral_count [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count, lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac a f

/-- Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥0∞`. -/
theorem _root_.ENNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0∞}
    (a_mble : Measurable a) {c : ℝ≥0∞} (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0)
    (ε_ne_top : ε ≠ ∞) : Measure.count { i : α | ε ≤ a i } ≤ c / ε := by
  rw [← lintegral_count] at tsum_le_c
  apply (MeasureTheory.meas_ge_le_lintegral_div a_mble.aemeasurable ε_ne_zero ε_ne_top).trans
  exact ENNReal.div_le_div tsum_le_c rfl.le

/-- Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥0`. -/
theorem _root_.NNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0}
    (a_mble : Measurable a) (a_summable : Summable a) {c : ℝ≥0} (tsum_le_c : ∑' i, a i ≤ c)
    {ε : ℝ≥0} (ε_ne_zero : ε ≠ 0) : Measure.count { i : α | ε ≤ a i } ≤ c / ε := by
  rw [show (fun i => ε ≤ a i) = fun i => (ε : ℝ≥0∞) ≤ ((↑) ∘ a) i by
      simp only [ENNReal.coe_le_coe, Function.comp]]
  apply
    ENNReal.count_const_le_le_of_tsum_le (measurable_coe_nnreal_ennreal.comp a_mble) _
      (mod_cast ε_ne_zero) (@ENNReal.coe_ne_top ε)
  convert ENNReal.coe_le_coe.mpr tsum_le_c
  simp_rw [Function.comp_apply]
  rw [ENNReal.tsum_coe_eq a_summable.hasSum]

end DiracAndCount

section Countable

theorem lintegral_countable' [Countable α] [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ = ∑' a, f a * μ {a} := by
  conv_lhs => rw [← sum_smul_dirac μ, lintegral_sum_measure]
  congr 1 with a : 1
  simp [mul_comm]

theorem lintegral_singleton' {f : α → ℝ≥0∞} (hf : Measurable f) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp [lintegral_dirac' _ hf, mul_comm]

theorem lintegral_singleton [MeasurableSingletonClass α] (f : α → ℝ≥0∞) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp [mul_comm]

theorem lintegral_countable [MeasurableSingletonClass α] (f : α → ℝ≥0∞) {s : Set α}
    (hs : s.Countable) : ∫⁻ a in s, f a ∂μ = ∑' a : s, f a * μ {(a : α)} :=
  calc
    ∫⁻ a in s, f a ∂μ = ∫⁻ a in ⋃ x ∈ s, {x}, f a ∂μ := by rw [biUnion_of_singleton]
    _ = ∑' a : s, ∫⁻ x in {(a : α)}, f x ∂μ :=
      (lintegral_biUnion hs (fun _ _ => measurableSet_singleton _) (pairwiseDisjoint_fiber id s) _)
    _ = ∑' a : s, f a * μ {(a : α)} := by simp only [lintegral_singleton]

theorem lintegral_insert [MeasurableSingletonClass α] {a : α} {s : Set α} (h : a ∉ s)
    (f : α → ℝ≥0∞) : ∫⁻ x in insert a s, f x ∂μ = f a * μ {a} + ∫⁻ x in s, f x ∂μ := by
  rw [← union_singleton, lintegral_union (measurableSet_singleton a), lintegral_singleton,
    add_comm]
  rwa [disjoint_singleton_right]

theorem lintegral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, f x * μ {x} := by
  simp only [lintegral_countable _ s.countable_toSet, ← Finset.tsum_subtype']

theorem lintegral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x} := by
  rw [← lintegral_finset, Finset.coe_univ, Measure.restrict_univ]

theorem lintegral_unique [Unique α] (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ = f default * μ univ :=
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ _, f default ∂μ := lintegral_congr <| Unique.forall_iff.2 rfl
    _ = f default * μ univ := lintegral_const _

end Countable

section SFinite

variable (μ) in
/-- If `μ` is an s-finite measure, then for any function `f`
there exists a measurable function `g ≤ f`
that has the same Lebesgue integral over every set.

For the integral over the whole space, the statement is true without extra assumptions,
see `exists_measurable_le_lintegral_eq`.
See also `MeasureTheory.Measure.restrict_toMeasurable_of_sFinite` for a similar result. -/
theorem exists_measurable_le_forall_setLIntegral_eq [SFinite μ] (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∀ s, ∫⁻ a in s, f a ∂μ = ∫⁻ a in s, g a ∂μ := by
  -- We only need to prove the `≤` inequality for the integrals, the other one follows from `g ≤ f`.
  rsuffices ⟨g, hgm, hgle, hleg⟩ :
      ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∀ s, ∫⁻ a in s, f a ∂μ ≤ ∫⁻ a in s, g a ∂μ
  · exact ⟨g, hgm, hgle, fun s ↦ (hleg s).antisymm (lintegral_mono hgle)⟩
  -- Without loss of generality, `μ` is a finite measure.
  wlog h : IsFiniteMeasure μ generalizing μ
  · choose g hgm hgle hgint using fun n ↦ @this (sfiniteSeq μ n) _ inferInstance
    refine ⟨fun x ↦ ⨆ n, g n x, .iSup hgm, fun x ↦ iSup_le (hgle · x), fun s ↦ ?_⟩
    rw [← sum_sfiniteSeq μ, Measure.restrict_sum_of_countable,
      lintegral_sum_measure, lintegral_sum_measure]
    exact ENNReal.tsum_le_tsum fun n ↦ (hgint n s).trans (lintegral_mono fun x ↦ le_iSup (g · x) _)
  -- According to `exists_measurable_le_lintegral_eq`, for any natural `n`
  -- we can choose a measurable function $g_{n}$
  -- such that $g_{n}(x) ≤ \min (f(x), n)$ for all $x$
  -- and both sides have the same integral over the whole space w.r.t. $μ$.
  have (n : ℕ): ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ g ≤ n ∧
      ∫⁻ a, min (f a) n ∂μ = ∫⁻ a, g a ∂μ := by
    simpa [and_assoc] using exists_measurable_le_lintegral_eq μ (f ⊓ n)
  choose g hgm hgf hgle hgint using this
  -- Let `φ` be the pointwise supremum of the functions $g_{n}$.
  -- Clearly, `φ` is a measurable function and `φ ≤ f`.
  set φ : α → ℝ≥0∞ := fun x ↦ ⨆ n, g n x
  have hφm : Measurable φ := by fun_prop
  have hφle : φ ≤ f := fun x ↦ iSup_le (hgf · x)
  refine ⟨φ, hφm, hφle, fun s ↦ ?_⟩
  -- Now we show the inequality between set integrals.
  -- Choose a simple function `ψ ≤ f` with values in `ℝ≥0` and prove for `ψ`.
  rw [lintegral_eq_nnreal]
  refine iSup₂_le fun ψ hψ ↦ ?_
  -- Choose `n` such that `ψ x ≤ n` for all `x`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ x, ψ x ≤ n := by
    rcases ψ.range.bddAbove with ⟨C, hC⟩
    exact ⟨⌈C⌉₊, fun x ↦ (hC <| ψ.mem_range_self x).trans (Nat.le_ceil _)⟩
  calc
    (ψ.map (↑)).lintegral (μ.restrict s) = ∫⁻ a in s, ψ a ∂μ :=
      SimpleFunc.lintegral_eq_lintegral .. |>.symm
    _ ≤ ∫⁻ a in s, min (f a) n ∂μ :=
      lintegral_mono fun a ↦ le_min (hψ _) (ENNReal.coe_le_coe.2 (hn a))
    _ ≤ ∫⁻ a in s, g n a ∂μ := by
      have : ∫⁻ a in (toMeasurable μ s)ᶜ, min (f a) n ∂μ ≠ ∞ :=
        IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _ ⟨n, fun _ ↦ min_le_right ..⟩ |>.ne
      have hsm : MeasurableSet (toMeasurable μ s) := measurableSet_toMeasurable ..
      apply ENNReal.le_of_add_le_add_right this
      rw [← μ.restrict_toMeasurable_of_sFinite, lintegral_add_compl _ hsm, hgint,
        ← lintegral_add_compl _ hsm]
      gcongr with x
      exact le_min (hgf n x) (hgle n x)
    _ ≤ _ := lintegral_mono fun x ↦ le_iSup (g · x) n

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
theorem exists_pos_lintegral_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε : ℝ≥0∞}
    (ε0 : ε ≠ 0) : ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ Measurable g ∧ ∫⁻ x, g x ∂μ < ε := by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : ℕ → Set α := disjointed (spanningSets μ)
  have : ∀ n, μ (s n) < ∞ := fun n =>
    (measure_mono <| disjointed_subset _ _).trans_lt (measure_spanningSets_lt_top μ n)
  obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, μ (s i) * δ i) < ε :=
    ENNReal.exists_pos_tsum_mul_lt_of_countable ε0 _ fun n => (this n).ne
  set N : α → ℕ := spanningSetsIndex μ
  have hN_meas : Measurable N := measurableSet_spanningSetsIndex μ
  have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanningSetsIndex_singleton μ
  refine ⟨δ ∘ N, fun x => δpos _, measurable_from_nat.comp hN_meas, ?_⟩
  erw [lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas]
  simpa [N, hNs, lintegral_countable', measurableSet_spanningSetsIndex, mul_comm] using δsum

omit [MeasurableSpace α]

variable {m m0 : MeasurableSpace α}

local infixr:25 " →ₛ " => SimpleFunc

theorem univ_le_of_forall_fin_meas_le {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : Set α → ℝ≥0∞} (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → f s ≤ C)
    (h_F_lim :
      ∀ S : ℕ → Set α, (∀ n, MeasurableSet[m] (S n)) → Monotone S → f (⋃ n, S n) ≤ ⨆ n, f (S n)) :
    f univ ≤ C := by
  let S := @spanningSets _ m (μ.trim hm) _
  have hS_mono : Monotone S := @monotone_spanningSets _ m (μ.trim hm) _
  have hS_meas : ∀ n, MeasurableSet[m] (S n) := @measurableSet_spanningSets _ m (μ.trim hm) _
  rw [← @iUnion_spanningSets _ m (μ.trim hm)]
  refine (h_F_lim S hS_meas hS_mono).trans ?_
  refine iSup_le fun n => hf (S n) (hS_meas n) ?_
  exact ((le_trim hm).trans_lt (@measure_spanningSets_lt_top _ m (μ.trim hm) _ n)).ne

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
theorem lintegral_le_of_forall_fin_meas_trim_le {μ : Measure α} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] (C : ℝ≥0∞) {f : α → ℝ≥0∞}
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C := by
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by simp only [Measure.restrict_univ]
  rw [← this]
  refine univ_le_of_forall_fin_meas_le hm C hf fun S _ hS_mono => ?_
  rw [setLIntegral_iUnion_of_directed]
  exact directed_of_isDirected_le hS_mono

alias lintegral_le_of_forall_fin_meas_le_of_measurable := lintegral_le_of_forall_fin_meas_trim_le

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
theorem lintegral_le_of_forall_fin_meas_le [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (C : ℝ≥0∞) {f : α → ℝ≥0∞}
    (hf : ∀ s, MeasurableSet s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C :=
  have : SigmaFinite (μ.trim le_rfl) := by rwa [trim_eq_self]
  lintegral_le_of_forall_fin_meas_trim_le _ C hf

theorem SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] {f : α →ₛ ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  induction f using MeasureTheory.SimpleFunc.induction generalizing L with
  | @const c s hs =>
    simp only [hs, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, Measure.restrict_apply',
      ENNReal.coe_indicator, Function.const_apply] at hL
    have c_ne_zero : c ≠ 0 := by
      intro hc
      simp only [hc, ENNReal.coe_zero, zero_mul, not_lt_zero] at hL
    have : L / c < μ s := by
      rwa [ENNReal.div_lt_iff, mul_comm]
      · simp only [c_ne_zero, Ne, ENNReal.coe_eq_zero, not_false_iff, true_or]
      · simp only [Ne, coe_ne_top, not_false_iff, true_or]
    obtain ⟨t, ht, ts, mlt, t_top⟩ :
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ L / ↑c < μ t ∧ μ t < ∞ :=
      Measure.exists_subset_measure_lt_top hs this
    refine ⟨piecewise t ht (const α c) (const α 0), fun x => ?_, ?_, ?_⟩
    · refine indicator_le_indicator_of_subset ts (fun x => ?_) x
      exact zero_le _
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', ENNReal.mul_lt_top ENNReal.coe_lt_top t_top]
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', univ_inter]
      rwa [mul_comm, ← ENNReal.div_lt_iff]
      · simp only [c_ne_zero, Ne, ENNReal.coe_eq_zero, not_false_iff, true_or]
      · simp only [Ne, coe_ne_top, not_false_iff, true_or]
  | @add f₁ f₂ _ h₁ h₂ =>
    replace hL : L < ∫⁻ x, f₁ x ∂μ + ∫⁻ x, f₂ x ∂μ := by
      rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    by_cases hf₁ : ∫⁻ x, f₁ x ∂μ = 0
    · simp only [hf₁, zero_add] at hL
      rcases h₂ hL with ⟨g, g_le, g_top, gL⟩
      refine ⟨g, fun x => (g_le x).trans ?_, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_left, zero_le']
    by_cases hf₂ : ∫⁻ x, f₂ x ∂μ = 0
    · simp only [hf₂, add_zero] at hL
      rcases h₁ hL with ⟨g, g_le, g_top, gL⟩
      refine ⟨g, fun x => (g_le x).trans ?_, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_right, zero_le']
    obtain ⟨L₁, hL₁, L₂, hL₂, hL⟩ : ∃ L₁ < ∫⁻ x, f₁ x ∂μ, ∃ L₂ < ∫⁻ x, f₂ x ∂μ, L < L₁ + L₂ :=
      ENNReal.exists_lt_add_of_lt_add hL hf₁ hf₂
    rcases h₁ hL₁ with ⟨g₁, g₁_le, g₁_top, hg₁⟩
    rcases h₂ hL₂ with ⟨g₂, g₂_le, g₂_top, hg₂⟩
    refine ⟨g₁ + g₂, fun x => add_le_add (g₁_le x) (g₂_le x), ?_, ?_⟩
    · apply lt_of_le_of_lt _ (add_lt_top.2 ⟨g₁_top, g₂_top⟩)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      exact le_rfl
    · apply hL.trans ((ENNReal.add_lt_add hg₁ hg₂).trans_le _)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      simp only [coe_add, Pi.add_apply, ENNReal.coe_add, le_rfl]

theorem exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {f : α → ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert g₀L
    rw [← SimpleFunc.lintegral_eq_lintegral, SimpleFunc.coe_map]
    simp only [Function.comp_apply]
  rcases SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral h'L with ⟨g, hg, gL, gtop⟩
  exact ⟨g, fun x => (hg x).trans (ENNReal.coe_le_coe.1 (hg₀ x)), gL, gtop⟩

end SFinite

end MeasureTheory
