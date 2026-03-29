/-
Copyright (c) 2026 Huanyu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Discreteness of the zeros of the Riemann zeta function

We show that the zeros of the Riemann zeta function form a discrete subset of `ℂ`,
so that in particular any compact subset of `ℂ` contains only finitely many zeros.

## Main results

* `riemannZeta_zeroes_on_Compact_finite`: for any compact set `S : Set ℂ`, the intersection
  `S ∩ riemannZeta ⁻¹' {0}` is finite.
-/

@[expose] public section

/-- The complement of the zero set of `riemannZeta` is codiscrete within `{1}ᶜ`. -/
lemma riemannZeta_zeroes_codiscreteWithin_compl_one :
    (riemannZeta ⁻¹' {0})ᶜ ∈ Filter.codiscreteWithin {1}ᶜ := by
  refine analyticOn_riemannZeta.preimage_zero_mem_codiscreteWithin
    ?_ ?_ ?_ (x := 2)
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact Set.mem_compl_singleton_iff.2 (OfNat.one_ne_ofNat 2).symm
  · refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two

private lemma riemannZeta_zeroes_on_compact_finite' {S : Set ℂ} (hS1 : IsCompact S)
    (hS2 : 1 ∉ S) : (S ∩ riemannZeta ⁻¹' {0}).Finite := by
  have sub := Set.subset_compl_singleton_iff.mpr hS2
  refine IsCompact.finite (hS1.of_isClosed_subset ?_ Set.inter_subset_left) ?_
  · exact analyticOn_riemannZeta.continuousOn.mono sub
      |>.preimage_isClosed_of_isClosed hS1.isClosed isClosed_singleton
  · rw [Set.inter_comm]
    exact IsDiscrete.mono
      (isDiscrete_of_codiscreteWithin riemannZeta_zeroes_codiscreteWithin_compl_one)
      <| Set.inter_subset_inter_right _ sub

/-- Any compact subset of `ℂ` contains only finitely many zeros of the Riemann zeta function. -/
lemma riemannZeta_zeroes_on_compact_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZeta ⁻¹' {0}).Finite := by
  obtain ⟨ε, hε_pos, hball⟩ := Metric.eventually_nhds_iff.1 <|
      eventually_nhdsWithin_iff.1 riemannZeta_eventually_ne_zero
  have hball' : ∀ s ∈ Metric.ball 1 ε, riemannZeta s ≠ 0 := fun s hs hzero ↦ by
    by_cases h : s = 1
    · exact riemannZeta_one_ne_zero (h ▸ hzero)
    · exact hball (Metric.mem_ball.1 hs) (Set.mem_compl_singleton_iff.2 h) hzero
  have : S ∩ riemannZeta ⁻¹' {0} ⊆ (S ∩ (Metric.ball 1 ε)ᶜ) ∩ riemannZeta ⁻¹' {0} :=
    fun s ⟨hs, hz⟩ ↦ ⟨⟨hs, fun hmem ↦ hball' s hmem hz⟩, hz⟩
  refine Set.Finite.subset (riemannZeta_zeroes_on_compact_finite' ?_ ?_) this
  · exact hS.inter_right Metric.isOpen_ball.isClosed_compl
  · exact fun ⟨_, h⟩ ↦ h (Metric.mem_ball_self hε_pos)

end
