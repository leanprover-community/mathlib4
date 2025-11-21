/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Arc length

This file is file is devoted to the definition of the `arclength` of a function `f` between
`a` and `b`.

## Main results

## Tags

Topology, Metric space, Continuity
-/

open ENNReal

variable {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E] (f : α → E) (a b c : α)

/--
The length of the arc  of the curve `f : α → E` between two points `a` and `b`, is defined
as the variation of `f` on the closed interval `[a, b]`. Equals zero when `b ≤ a`.
-/
noncomputable def Arclength (a b : α) : ℝ≥0∞ :=
  eVariationOn f (Set.Icc a b)

-- TODO: is this useful?
@[simp]
theorem arclength_eq_supr₂ : Arclength f a b =
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ Set.Icc a b},
    ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by rfl

theorem wf : WellFounded ((· < ·) : ℕ → ℕ → Prop) := sorry

/--
`arclength f a b` is the supremum of finite sums of `edist (f $ u i) (f $ u $ i+1)` for `u`
satisfying the same conditions as for `evariation_on` with the addition of:
* `u 0` is `a`.
* `u 1` is **not** `a`.
-/
theorem arclength_eq_supr (hab : a ≤ b) : Arclength f a b =
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ (∀ i, u i ∈ Set.Icc a b) ∧ u 0 = a ∧ a < u 1},
    ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, hu, huab⟩
    by_cases h : ∀ m ≤ n, u m = a
    · have : ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        simp only [Finset.mem_range] at hi
        rw [h i (by linarith), h (i+1) (by linarith), edist_self]
      rw [this]; apply zero_le
    push_neg at h
    obtain ⟨m, ⟨hmn, hma⟩, hmin⟩ := WellFounded.has_min wf {m | m ≤ n ∧ u m ≠ a} h
    push_neg at hmin
    cases m with
    | zero =>
      refine le_iSup_of_le ⟨n + 1, Nat.rec a (fun k _ => u k), ⟨fun k => ?_,
        ⟨fun k => ?_, ⟨rfl, (huab 0).1.lt_of_ne' hma⟩⟩⟩⟩ ?_
      · apply monotone_nat_of_le_succ
        intro n; cases n;
        · exact (huab 0).1
        · exact hu (Nat.le_succ _)
      · cases k
        · exact Set.left_mem_Icc.mpr hab
        · exact huab _
      · rw [Finset.sum_range_succ']; exact self_le_add_right _ _
    | succ m =>
      have : ∀ k ≤ m, u k = a := by sorry
      refine le_iSup_of_le ?_ ?_
      · refine ⟨n - m, ⟨fun k => u (m + k), ⟨?_, ?_⟩⟩⟩
        · exact hu.comp (fun _ _ h => add_le_add_left h _)
        · exact ⟨fun k => huab _, this m le_rfl, (huab _).1.lt_of_ne' hma⟩
      · dsimp only [Subtype.coe_mk]
        conv =>
          lhs; rw [← Nat.sub_add_cancel (m.le_succ.trans hmn), add_comm, Finset.sum_range_add]
        simp_rw [add_assoc]
        have : ∑ x ∈ Finset.range m, edist (f (u (x + 1))) (f (u x)) = 0 := by
          apply Finset.sum_eq_zero; intro i hi
          simp only [Finset.mem_range] at hi
          rw [this i (by linarith), this (i+1) (by linarith), edist_self]
        rw [this, zero_add]
  · apply iSup_le
    intro p; rw [arclength_eq_supr₂]
    let p' : ℕ × { u // Monotone u ∧ ∀ i, u i ∈ Set.Icc a b } :=
      ⟨p.1, ⟨p.2.val, ⟨p.2.property.1, p.2.property.2.1⟩⟩⟩
    exact le_iSup (fun p => ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) p'
