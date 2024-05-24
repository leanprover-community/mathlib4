/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/

import Mathlib.Topology.Perfect
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.CantorScheme

#align_import topology.perfect from "leanprover-community/mathlib"@"3905fa80e62c0898131285baab35559fbc4e5cda"

/-!
# Perfect Sets

In this file we define properties of `Perfect` subsets of a metric space,
including a version of the Cantor-Bendixson Theorem.

## Main Statements

* `Perfect.exists_nat_bool_injection`: A perfect nonempty set in a complete metric space
  admits an embedding from the Cantor space.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, cantor-bendixson.

--/

open Set Filter

section CantorInjMetric

open Function ENNReal

variable {α : Type*} [MetricSpace α] {C : Set α} (hC : Perfect C) {ε : ℝ≥0∞}

private theorem Perfect.small_diam_aux (ε_pos : 0 < ε) {x : α} (xC : x ∈ C) :
    let D := closure (EMetric.ball x (ε / 2) ∩ C)
    Perfect D ∧ D.Nonempty ∧ D ⊆ C ∧ EMetric.diam D ≤ ε := by
  have : x ∈ EMetric.ball x (ε / 2) := by
    apply EMetric.mem_ball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt ε_pos, by norm_num⟩
  have := hC.closure_nhds_inter x xC this EMetric.isOpen_ball
  refine ⟨this.1, this.2, ?_, ?_⟩
  · rw [IsClosed.closure_subset_iff hC.closed]
    apply inter_subset_right
  rw [EMetric.diam_closure]
  apply le_trans (EMetric.diam_mono (inter_subset_left _ _))
  convert EMetric.diam_ball (x := x)
  rw [mul_comm, ENNReal.div_mul_cancel] <;> norm_num

variable (hnonempty : C.Nonempty)

/-- A refinement of `Perfect.splitting` for metric spaces, where we also control
the diameter of the new perfect sets. -/
theorem Perfect.small_diam_splitting (ε_pos : 0 < ε) :
    ∃ C₀ C₁ : Set α, (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ C ∧ EMetric.diam C₀ ≤ ε) ∧
    (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ C ∧ EMetric.diam C₁ ≤ ε) ∧ Disjoint C₀ C₁ := by
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩
  cases' non0 with x₀ hx₀
  cases' non1 with x₁ hx₁
  rcases perf0.small_diam_aux ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩
  rcases perf1.small_diam_aux ε_pos hx₁ with ⟨perf1', non1', sub1', diam1⟩
  refine
    ⟨closure (EMetric.ball x₀ (ε / 2) ∩ D₀), closure (EMetric.ball x₁ (ε / 2) ∩ D₁),
      ⟨perf0', non0', sub0'.trans sub0, diam0⟩, ⟨perf1', non1', sub1'.trans sub1, diam1⟩, ?_⟩
  apply Disjoint.mono _ _ hdisj <;> assumption
#align perfect.small_diam_splitting Perfect.small_diam_splitting

open CantorScheme

/-- Any nonempty perfect set in a complete metric space admits a continuous injection
from the Cantor space, `ℕ → Bool`. -/
theorem Perfect.exists_nat_bool_injection [CompleteSpace α] :
    ∃ f : (ℕ → Bool) → α, range f ⊆ C ∧ Continuous f ∧ Injective f := by
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  have upos := fun n => (upos' n).1
  let P := Subtype fun E : Set α => Perfect E ∧ E.Nonempty
  choose C0 C1 h0 h1 hdisj using
    fun {C : Set α} (hC : Perfect C) (hnonempty : C.Nonempty) {ε : ℝ≥0∞} (hε : 0 < ε) =>
    hC.small_diam_splitting hnonempty hε
  let DP : List Bool → P := fun l => by
    induction' l with a l ih; · exact ⟨C, ⟨hC, hnonempty⟩⟩
    cases a
    · use C0 ih.property.1 ih.property.2 (upos (l.length + 1))
      exact ⟨(h0 _ _ _).1, (h0 _ _ _).2.1⟩
    use C1 ih.property.1 ih.property.2 (upos (l.length + 1))
    exact ⟨(h1 _ _ _).1, (h1 _ _ _).2.1⟩
  let D : List Bool → Set α := fun l => (DP l).val
  have hanti : ClosureAntitone D := by
    refine Antitone.closureAntitone ?_ fun l => (DP l).property.1.closed
    intro l a
    cases a
    · exact (h0 _ _ _).2.2.1
    exact (h1 _ _ _).2.2.1
  have hdiam : VanishingDiam D := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [eventually_atTop]
    refine ⟨1, fun m (hm : 1 ≤ m) => ?_⟩
    rw [Nat.one_le_iff_ne_zero] at hm
    rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩
    dsimp
    cases x n
    · convert (h0 _ _ _).2.2.2
      rw [PiNat.res_length]
    convert (h1 _ _ _).2.2.2
    rw [PiNat.res_length]
  have hdisj' : CantorScheme.Disjoint D := by
    rintro l (a | a) (b | b) hab <;> try contradiction
    · exact hdisj _ _ _
    exact (hdisj _ _ _).symm
  have hdom : ∀ {x : ℕ → Bool}, x ∈ (inducedMap D).1 := fun {x} => by
    rw [hanti.map_of_vanishingDiam hdiam fun l => (DP l).property.2]
    apply mem_univ
  refine ⟨fun x => (inducedMap D).2 ⟨x, hdom⟩, ?_, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact map_mem ⟨_, hdom⟩ 0
  · apply hdiam.map_continuous.comp
    continuity
  intro x y hxy
  simpa only [← Subtype.val_inj] using hdisj'.map_injective hxy
#align perfect.exists_nat_bool_injection Perfect.exists_nat_bool_injection

end CantorInjMetric

/-- Any closed uncountable subset of a Polish space admits a continuous injection
from the Cantor space `ℕ → Bool`. -/
theorem IsClosed.exists_nat_bool_injection_of_not_countable {α : Type*} [TopologicalSpace α]
    [PolishSpace α] {C : Set α} (hC : IsClosed C) (hunc : ¬C.Countable) :
    ∃ f : (ℕ → Bool) → α, range f ⊆ C ∧ Continuous f ∧ Function.Injective f := by
  letI := upgradePolishSpace α
  obtain ⟨D, hD, Dnonempty, hDC⟩ := exists_perfect_nonempty_of_isClosed_of_not_countable hC hunc
  obtain ⟨f, hfD, hf⟩ := hD.exists_nat_bool_injection Dnonempty
  exact ⟨f, hfD.trans hDC, hf⟩
#align is_closed.exists_nat_bool_injection_of_not_countable IsClosed.exists_nat_bool_injection_of_not_countable
