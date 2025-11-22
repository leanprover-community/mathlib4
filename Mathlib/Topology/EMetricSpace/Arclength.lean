/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
-- import Mathlib.Order.Synonym

/-!
# Arc length

This file is file is devoted to the definition of the `arclength` of a function `f` between
`a` and `b`.

## Main results

## Tags

Topology, Metric space, Continuity
-/

open ENNReal

variable {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E] (f : α → E) {a b c : α}

/--
The length of the arc  of the curve `f : α → E` between two points `a` and `b`, is defined
as the variation of `f` on the closed interval `[a, b]`. Equals zero when `b ≤ a`.
-/
noncomputable def arclength (a b : α) : ℝ≥0∞ :=
  eVariationOn f (Set.Icc a b)

theorem wf : WellFounded ((· < ·) : ℕ → ℕ → Prop) := sorry

/--
`arclength f a b` is the supremum of finite sums of `edist (f $ u i) (f $ u $ i+1)` for `u`
satisfying the same conditions as for `evariation_on` with the addition of:
* `u 0` is `a`.
* `u 1` is **not** `a`.
-/
theorem arclength_eq_supr (hab : a ≤ b) : arclength f a b =
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
      have : ∀ k ≤ m, u k = a := by
        intro k hk; contrapose! hmin
        exact ⟨_, ⟨hk.trans (m.le_succ.trans hmn), hmin⟩, hk.trans_lt m.lt_succ_self⟩
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

theorem edist_le_arclength (hab : a ≤ b) : edist (f a) (f b) ≤ arclength f a b := by
  refine eVariationOn.edist_le f ?_ ?_ <;> simp [hab]

/-- The length of a function over a singleton is zero. -/
theorem arclength_eq_zero (hab : b ≤ a) : arclength f a b = 0 := by
  refine eVariationOn.subsingleton f ?_; simp [hab]

theorem arclength_self (a : α) : arclength f a a = 0 := arclength_eq_zero _ (le_rfl)

theorem arclength_anti (c : α) : Antitone (fun x => arclength f x c) := by
  refine fun a b hab => eVariationOn.mono _ ?_
  rintro x ⟨hbx, hxc⟩
  exact ⟨hab.trans hbx, hxc⟩

theorem arclength_mono (a : α) : Monotone (arclength f a) := by
  refine fun x y hxy => eVariationOn.mono _ ?_
  rintro z ⟨haz, hzx⟩
  exact ⟨haz, hzx.trans hxy⟩

theorem arclength_add (hab : a ≤ b) (hbc : b ≤ c) :
    arclength f a b + arclength f b c  = arclength f a c := by
  simp_rw [arclength]
  convert eVariationOn.Icc_add_Icc f (s := Set.univ) hab hbc (by simp) <;> simp

theorem arclength_sum {n : ℕ} {u : ℕ → α} (hu : Monotone u) :
    ∑ i ∈ Finset.range n, arclength f (u i) (u (i + 1)) = arclength f (u 0) (u n) := by
  induction n with
  | zero => rw [arclength_self, Finset.sum_range_zero]
  | succ k ih => rw [Finset.sum_range_succ, ih, arclength_add f (hu <| zero_le k) (hu k.le_succ)]

theorem arclength_sub₀ (hba : b ≤ a) : arclength f a b = arclength f a c - arclength f b c := by
  rw [arclength_eq_zero f hba, eq_comm]
  exact tsub_eq_zero_of_le (arclength_anti f c hba)

theorem arclength_sub' (hbc : b ≤ c) (hac : arclength f b c ≠ ∞) :
    arclength f a b =  arclength f a c - arclength f b c := by
  rcases le_total a b with (hab | hba)
  · exact ENNReal.eq_sub_of_add_eq hac (arclength_add f hab hbc)
  · exact arclength_sub₀ f hba

theorem arclength_sub (hbc : b ≤ c) (hac : arclength f a c ≠ ∞) :
    arclength f a b = arclength f a c - arclength f b c := by
  rcases le_total a b with (hab | hba)
  · exact arclength_sub' f hbc <| ne_top_of_le_ne_top hac <| arclength_anti f c hab
  · exact arclength_sub₀ f hba

open OrderDual

@[simp]
theorem arclength_comp_of_dual :
    arclength (f ∘ ofDual) (toDual b) (toDual a) = arclength f a b := by
  unfold arclength
  have : Set.Icc (toDual b) (toDual a) = ofDual ⁻¹' (Set.Icc a b) := by simp
  rw [this, eVariationOn.comp_ofDual]

theorem arclength'_eq (b : α) :
    (fun x => arclength f x b) = arclength (f ∘ ofDual) (toDual b) ∘ toDual := by
  ext x; simp
