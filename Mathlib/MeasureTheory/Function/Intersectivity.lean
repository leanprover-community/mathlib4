/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.MeasureTheory.Integral.Average

/-!
# Bergelson's intersectivity lemma

This file proves the Bergelson intersectivity lemma: In a finite measure space, a sequence of events
that have measure at least `r` has an infinite subset whose finite intersections all have positive
volume.

This is in some sense a finitary version of the second Borel-Cantelli lemma.

## References

[Bergelson, *Sets of recurrence of `ℤᵐ`-actions and properties of sets of differences in
`ℤᵐ`][bergelson1985]

## TODO

Restate the theorem using the upper density of a set of naturals, once we have it. This will make
`bergelson'` be actually strong (and please then rename it to `strong_bergelson`).

Use the ergodic theorem to deduce the refinement of the Poincaré recurrence theorem proved by
Bergelson.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

variable {ι α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {r : ℝ≥0∞}

/-- **Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of events that have
measure at least `r` has an infinite subset whose finite intersections all have positive volume.

TODO: The infinity of `t` should be strengthened to `t` having positive natural density. -/
lemma bergelson' {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n)) (hr₀ : r ≠ 0)
    (hr : ∀ n, r ≤ μ (s n)) :
    ∃ t : Set ℕ, t.Infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.Finite → 0 < μ (⋂ n ∈ u, s n) := by
  -- We let `M f` be the set on which the norm of `f` exceeds its essential supremum, and `N` be the
  -- union of `M` of the finite products of the indicators of the `s n`.
  let M (f : α → ℝ) : Set α := {x | eLpNormEssSup f μ < ‖f x‖₊}
  let N : Set α := ⋃ u : Finset ℕ, M (Set.indicator (⋂ n ∈ u, s n) 1)
  -- `N` is a null set since `M f` is a null set for each `f`.
  have hN₀ : μ N = 0 := measure_iUnion_null fun u ↦ meas_eLpNormEssSup_lt
  -- The important thing about `N` is that if we remove `N` from our space, then finite unions of
  -- the `s n` are null iff they are empty.
  have hN₁ (u : Finset ℕ) : ((⋂ n ∈ u, s n) \ N).Nonempty → 0 < μ (⋂ n ∈ u, s n) := by
    simp_rw [pos_iff_ne_zero]
    rintro ⟨x, hx⟩ hu
    refine hx.2 (mem_iUnion.2 ⟨u, ?_⟩)
    rw [mem_setOf, indicator_of_mem hx.1, eLpNormEssSup_eq_zero_iff.2]
    · simp
    · rwa [indicator_ae_eq_zero, Function.support_one, inter_univ]
  -- Define `f n` to be the average of the first `n + 1` indicators of the `s k`.
  let f (n : ℕ) : α → ℝ≥0∞ := (↑(n + 1) : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range (n + 1), (s k).indicator 1
  -- We gather a few simple properties of `f`.
  have hfapp : ∀ n a, f n a = (↑(n + 1))⁻¹ * ∑ k ∈ Finset.range (n + 1), (s k).indicator 1 a := by
    simp only [f, Pi.smul_apply, Finset.sum_apply,
    forall_const, imp_true_iff, smul_eq_mul]
  have hf n : Measurable (f n) := by fun_prop (disch := exact hs _)
  have hf₁ n : f n ≤ 1 := by
    rintro a
    rw [hfapp, ← ENNReal.div_eq_inv_mul]
    refine (ENNReal.div_le_iff_le_mul (Or.inl <| Nat.cast_ne_zero.2 n.succ_ne_zero) <|
      Or.inr one_ne_zero).2 ?_
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.card_range n.succ]
    exact Finset.sum_le_card_nsmul _ _ _ fun _ _ ↦ indicator_le (fun _ _ ↦ le_rfl) _
  -- By assumption, `f n` has integral at least `r`.
  have hrf n : r ≤ ∫⁻ a, f n a ∂μ := by
    simp_rw [hfapp]
    rw [lintegral_const_mul _ <| Finset.measurable_fun_sum _
        fun _ _ ↦ measurable_one.indicator <| hs _,
      lintegral_finset_sum _ fun _ _ ↦ measurable_one.indicator (hs _)]
    simp only [lintegral_indicator_one (hs _)]
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (by simp) (by simp), ← nsmul_eq_mul']
    simpa using Finset.card_nsmul_le_sum (Finset.range (n + 1)) _ _ fun _ _ ↦ hr _
  -- Collect some basic fact
  have hμ : μ ≠ 0 := by rintro rfl; exact hr₀ <| le_bot_iff.1 <| hr 0
  have : ∫⁻ x, limsup (f · x) atTop ∂μ ≤ μ univ := by
    rw [← lintegral_one]
    exact lintegral_mono fun a ↦ limsup_le_of_le ⟨0, fun R _ ↦ bot_le⟩ <|
      Eventually.of_forall fun n ↦ hf₁ _ _
  -- By the first moment method, there exists some `x ∉ N` such that `limsup f n x` is at least `r`.
  obtain ⟨x, hxN, hx⟩ := exists_notMem_null_laverage_le hμ
    (ne_top_of_le_ne_top (measure_ne_top μ univ) this) hN₀
  replace hx : r / μ univ ≤ limsup (f · x) atTop :=
    calc
      _ ≤ limsup (⨍⁻ x, f · x ∂μ) atTop := le_limsup_of_le ⟨1, eventually_map.2 ?_⟩ fun b hb ↦ ?_
      _ ≤ ⨍⁻ x, limsup (f · x) atTop ∂μ := limsup_lintegral_le 1 hf (ae_of_all _ <| hf₁ ·) (by simp)
      _ ≤ limsup (f · x) atTop := hx
  -- This exactly means that the `s n` containing `x` have all their finite intersection non-null.
  · refine ⟨{n | x ∈ s n}, fun hxs ↦ ?_, fun u hux hu ↦ ?_⟩
    -- This next block proves that a set of strictly positive natural density is infinite, mixed
    -- with the fact that `{n | x ∈ s n}` has strictly positive natural density.
    -- TODO: Separate it out to a lemma once we have a natural density API.
    · refine ENNReal.div_ne_zero.2 ⟨hr₀, measure_ne_top _ _⟩ <| eq_bot_mono hx <|
        Tendsto.limsup_eq <| tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (h := fun n ↦ (n.succ : ℝ≥0∞)⁻¹ * hxs.toFinset.card) ?_ bot_le fun n ↦ mul_le_mul_left' ?_ _
      · simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_inv_nat_nhds_zero.comp <|
          tendsto_add_atTop_nat 1) (.inr <| ENNReal.natCast_ne_top _)
      · classical
        simpa only [Finset.sum_apply, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_le]
          using Finset.card_le_card fun m hm ↦ hxs.mem_toFinset.2 (Finset.mem_filter.1 hm).2
    · simp_rw [← hu.mem_toFinset]
      exact hN₁ _ ⟨x, mem_iInter₂.2 fun n hn ↦ hux <| hu.mem_toFinset.1 hn, hxN⟩
  · refine Eventually.of_forall fun n ↦ ?_
    obtain rfl | _ := eq_zero_or_neZero μ
    · simp
    · rw [← laverage_const μ 1]
      exact lintegral_mono (hf₁ _)
  · obtain ⟨n, hn⟩ := hb.exists
    rw [laverage_eq] at hn
    exact (ENNReal.div_le_div_right (hrf _) _).trans hn

/-- **Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of events that have
measure at least `r` has an infinite subset whose finite intersections all have positive volume. -/
lemma bergelson [Infinite ι] {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i)) (hr₀ : r ≠ 0)
    (hr : ∀ i, r ≤ μ (s i)) :
    ∃ t : Set ι, t.Infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.Finite → 0 < μ (⋂ i ∈ u, s i) := by
  obtain ⟨t, ht, h⟩ := bergelson' (fun n ↦ hs <| Infinite.natEmbedding _ n) hr₀ (fun n ↦ hr _)
  refine ⟨_, ht.image <| (Infinite.natEmbedding _).injective.injOn, fun u hut hu ↦
    (h (preimage_subset_of_surjOn (Infinite.natEmbedding _).injective hut) <| hu.preimage
    (Embedding.injective _).injOn).trans_le <| measure_mono <| subset_iInter₂ fun i hi ↦ ?_⟩
  obtain ⟨n, -, rfl⟩ := hut hi
  exact iInter₂_subset n hi
