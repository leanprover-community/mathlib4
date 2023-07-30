import Mathlib.Data.List.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.List
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.WLOG
import Mathlib.Order.WithBot
import Mathlib.Data.Greedoid.Basic

section rank

variable {s t : Finset α} {x y : α}

open Nat List Finset Greedoid

set_option linter.unusedVariables false in
protected def rank.toGreedoid' (r : Finset α → ℕ) (hr : greedoidRankAxioms r) : Finset (Finset α) :=
  univ.filter fun s => r s = s.card

theorem rank_toGreedoid'_greedoidRankAxioms_accessibleProperty
  {r : Finset α → ℕ} (hr : greedoidRankAxioms r) :
    _root_.accessibleProperty (rank.toGreedoid' r hr) := by
  simp only [_root_.accessibleProperty, rank.toGreedoid', mem_univ, Finset.mem_filter, true_and]
  intro s hs₁ hs₂
  sorry

theorem rank_toGreedoid'_greedoidRankAxioms_exchangeProperty
  {r : Finset α → ℕ} (hr : greedoidRankAxioms r) :
    _root_.exchangeProperty (rank.toGreedoid' r hr) := by
  simp only [_root_.exchangeProperty, rank.toGreedoid', mem_univ, Finset.mem_filter, true_and,
    mem_sdiff]
  intro s₁ hs₁ s₂ hs₂ hs
  sorry

/-- Rank function satisfying `greedoidRankAxioms` generates a unique greedoid. -/
protected def rank.toGreedoid (r : Finset α → ℕ) (hr : greedoidRankAxioms r) : Greedoid α :=
  ⟨univ.filter fun s => r s = s.card, by
    simp only [mem_univ, Finset.mem_filter, hr.1, card_empty], by
    have := @rank_toGreedoid'_greedoidRankAxioms_accessibleProperty _ _ _ _ hr
    simp only [rank.toGreedoid'] at this; simp only [this], by
    have := @rank_toGreedoid'_greedoidRankAxioms_exchangeProperty _ _ _ _ hr
    simp only [rank.toGreedoid'] at this; simp only [this]⟩

theorem greedoidRankAxioms_unique_greedoid {r : Finset α → ℕ} (hr : greedoidRankAxioms r) :
    ∃! G : Greedoid α, G.rank = r := by
  exists rank.toGreedoid r hr
  simp only [rank.toGreedoid, mem_univ, forall_true_left]
  constructor
  . ext s
    simp only [rank]
    apply Nat.le_antisymm
    . simp only [mem_univ, forall_true_left, Finset.mem_filter, true_and, WithBot.unbot_le_iff]
      apply Finset.max_le
      intro a ha
      rw [WithBot.coe_le_coe]
      simp only [mem_univ, forall_true_left, Finset.mem_filter, true_and, mem_image] at ha
      let ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩ := ha
      rw [← hb₃, ← hb₁]
      exact hr.2.2.1 hb₂
    . simp only [mem_univ, forall_true_left, Finset.mem_filter, true_and, WithBot.le_unbot_iff]
      apply Finset.le_max
      simp only [mem_univ, forall_true_left, Finset.mem_filter, true_and, mem_image]
      sorry
  . intro G' hG'
    apply Greedoid.eq_of_veq
    simp only [mem_univ, forall_true_left]
    ext x; constructor <;> intro h
    . simp [← hG', system_feasible_set_mem_mem.mp h]
    . simp only [system_feasible_set_mem_mem, Finset.mem_filter, mem_univ, true_and] at *
      rw [← hG', rank_eq_card_iff_feasible] at h
      exact h

-- /-- Rank function satisfying `greedoidRankAxioms` generates a unique greedoid. -/
-- protected def rank.toGreedoid (r : Finset α → ℕ) (hr : greedoidRankAxioms r) : Greedoid α :=
--   Fintype.choose (fun G => G.rank = r) (greedoidRankAxioms_unique_greedoid hr)

end rank
