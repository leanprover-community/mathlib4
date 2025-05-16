/-
Copyright (c) 2025 William Du. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Du
-/
import Mathlib.MeasureTheory.MeasureAlgebra.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
TODO: docstring
-/

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

namespace MeasureAlgebra

variable {m : MeasurableAlgebra α} {μ : MeasureAlgebraMeasure α} {a b : α}

lemma prop321Ba (hd : a ⊓ b = ⊥) : μ (a ⊔ b) = (μ a) + (μ b) := by
  let s (n : ℕ) : α :=
    match n with
    | 0 => a
    | 1 => b
    | _ => ⊥
  have hsup : μ (a ⊔ b) = μ (⨆i s) := by
    apply congrArg
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact le_nSup s 0
      · exact le_nSup s 1
    · rw [nSup_le_iff]
      rintro ( _ | _ | i )
      · exact le_sup_left
      · rw [zero_add]; exact le_sup_right
      · exact bot_le
  have hpd : Pairwise (Disjoint on s) := by
    unfold Pairwise; unfold Disjoint
    intro i j hi_ne_j x hx_le_si hx_le_sj
    rcases i with _ | _ | i
    repeat {
      rcases j with _ | _ | j
      repeat {
        try { exfalso; exact hi_ne_j rfl }
        try { rw [←hd]; exact le_inf hx_le_si hx_le_sj }
        try { rw [←hd]; exact le_inf hx_le_sj hx_le_si }
        try { exact hx_le_si }
        try { exact hx_le_sj }
      }
    }
  have hsum : ∑' i, μ (s i) = (μ a) + (μ b) := by
    let d : Finset ℕ := {0, 1}
    have hf : ∀ x ∉ d, μ (s x) = 0 := by
      intro x hx_not_mem_d
      simp only [d] at hx_not_mem_d
      rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx_not_mem_d
      obtain ⟨hx_ne_0, hx_ne_1⟩ := hx_not_mem_d
      unfold s
      simp only
      exact μ.zero
    rw [tsum_eq_sum hf]
    have h0_not_mem_1 : 0 ∉ ({1} : Finset ℕ) := by
      rw [Finset.mem_singleton]; exact zero_ne_one
    rw [Finset.sum_insert h0_not_mem_1, Finset.sum_singleton]
  rw [hsup, MeasureAlgebraMeasure.disjoint hpd, hsum]

lemma prop321Bb (hab : a ≤ b) : μ a ≤ μ b := by
  rw [(le_iff_eq_sup_sdiff hab hab).mp (le_refl a)]
  rw [prop321Ba inf_sdiff_self_right]
  exact self_le_add_right (μ a) (μ (b \ a))

lemma prop321Bc : μ (a ⊔ b) ≤ μ a + μ b := by
  rw [←sdiff_sup_self]
  rw [prop321Ba inf_sdiff_self_left]
  apply add_le_add_right
  exact prop321Bb sdiff_le

lemma prop321Bd {a : ℕ → α} : μ (⨆i a) ≤ ∑' i, μ (a i) := by
  let up_to_n (s : ℕ → α) (n : ℕ) := fun i ↦ if i ≤ n then s i else ⊥
  let b (i : ℕ) : α :=
    match i with
    | 0 => a 0
    | i => (a i) \ ⨆i (up_to_n a (i - 1))
  have hi_le_n_si_eq_s'ni (s : ℕ → α) {n i : ℕ} (hi_le_n : i ≤ n) : s i = up_to_n s n i := by
    unfold up_to_n
    have hcond_true : (i ≤ n) = True := by
      rw [Lean.Grind.eq_true_eq]
      exact hi_le_n
    rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
  have hsn_eq_s'nn (s : ℕ → α) {n : ℕ} : s n = up_to_n s n n := by
    exact hi_le_n_si_eq_s'ni s (le_refl n)
  have hs'_le_s {s : ℕ → α} {n : ℕ} : ⨆i (up_to_n s n) ≤ ⨆i s := by
    apply nSup_mono
    intro i; use i
    unfold up_to_n
    by_cases hi_n : i ≤ n
    · have hcond_true : (i ≤ n) = True := by
        rw [Lean.Grind.eq_true_eq]
        exact hi_n
      rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
    · have hcond_false : (i ≤ n) = False := by
        rw [Lean.Grind.eq_false_eq]
        exact hi_n
      rw [ite_congr hcond_false (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
      exact bot_le
  have hf_sup {s : ℕ → α} {n : ℕ} : ⨆i (up_to_n s (n + 1)) = s (n + 1) ⊔ ⨆i (up_to_n s n) := by
    apply le_antisymm
    · apply nSup_le
      intro i
      by_cases hi_n1 : i ≤ n + 1
      by_cases hi_n : i ≤ n
      · rw [←hi_le_n_si_eq_s'ni s hi_n1, hi_le_n_si_eq_s'ni s hi_n]
        -- maybe extract this
        exact le_sup_of_le_right (le_nSup (up_to_n s n) i)
      · rw [le_antisymm hi_n1 (Nat.add_one_le_iff.mpr (not_le.mp hi_n)), ←hsn_eq_s'nn s]
        exact le_sup_left
      · unfold up_to_n
        have hcond_false : (i ≤ n + 1) = False := by
          rw [Lean.Grind.eq_false_eq]
          exact hi_n1
        rw [ite_congr hcond_false (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
        exact bot_le
    · apply sup_le
      · rw [hsn_eq_s'nn s]
        exact le_nSup (up_to_n s (n + 1)) (n + 1)
      · apply nSup_mono
        intro i; use i
        by_cases hi_n : i ≤ n
        · rw [←hi_le_n_si_eq_s'ni s hi_n]
          rw [←hi_le_n_si_eq_s'ni s (le_trans hi_n (Nat.le_add_right n 1))]
        · unfold up_to_n
          have hcond_false : (i ≤ n) = False := by
            rw [Lean.Grind.eq_false_eq]
            exact hi_n
          rw [ite_congr hcond_false (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
          exact bot_le
  have hsup_a'_eq_sup_b' {n : ℕ} : ⨆i (up_to_n a n) = ⨆i (up_to_n b n) := by
    induction' n with n hn
    · apply congrArg
      funext i
      unfold up_to_n
      have hthen_congr (hi : i ≤ 0) : a i = b i := by
        rw [Nat.le_zero.mp hi]
      rw [ite_congr rfl hthen_congr (fun _ ↦ rfl)]
    · rw [hf_sup, hf_sup, ←hn]
      unfold b
      simp only
      rw [add_tsub_cancel_right, sdiff_sup_self]
  have hb_le_a {i : ℕ} : b i ≤ a i := by
    by_cases hi : i = 0
    · rw [hi]
    · unfold b
      simp only
      exact sdiff_le
  have hsup_a_eq_sup_b : ⨆i a = ⨆i b := by
    apply le_antisymm
    · apply nSup_le
      intro i
      have hai_le_nSup_b'i : a i ≤ ⨆i (up_to_n b i) := by
        rw [←hsup_a'_eq_sup_b', hsn_eq_s'nn a]
        exact le_nSup (up_to_n a i) i
      exact le_trans hai_le_nSup_b'i hs'_le_s
    · apply nSup_mono
      intro i; use i
      exact hb_le_a
  have hi_j_disjoint {x : α} {i j : ℕ} (hi_ne_j : i ≠ j)
  (hx_le_bi : x ≤ b i) (hx_le_bj : x ≤ b j)
  (hi_lt_j : i < j)
  : x ≤ ⊥ := by
    induction' i with i _
    · unfold b at hx_le_bj
      -- lean is stupid here
      replace hi_ne_j := Ne.symm hi_ne_j
      simp only [hi_ne_j] at hx_le_bj
      -- this should really be done in equational reasoning mode
      have hle_diff_inf : x ≤ a j \ ⨆i (up_to_n a (j - 1)) ⊓ ⨆i (up_to_n a (j - 1)) := by
        apply le_inf
        · exact hx_le_bj
        · apply m.le_trans x (up_to_n a (j - 1) 0) (⨆i up_to_n a (j - 1))
          · exact le_trans hx_le_bi (le_of_eq (hi_le_n_si_eq_s'ni a (zero_le (j - 1))))
          · exact le_nSup (up_to_n a (j - 1)) 0
      rw [inf_sdiff_self_left] at hle_diff_inf
      exact hle_diff_inf
    · unfold b at hx_le_bi
      simp only at hx_le_bi
      have hj : j ≠ 0 := by
        intro hj
        rw [hj] at hi_lt_j
        exact (Nat.not_lt_zero (i + 1)) hi_lt_j
      unfold b at hx_le_bj
      simp only [hj] at hx_le_bj
      -- and this as well
      have hle_diff_inf : x ≤ a j \ ⨆i (up_to_n a (j - 1)) ⊓ ⨆i (up_to_n a (j - 1)) := by
        apply le_inf
        · exact hx_le_bj
        · apply m.le_trans x (up_to_n a (j - 1) (i + 1)) (⨆i up_to_n a (j - 1))
          · apply m.le_trans x (a (i + 1)) (up_to_n a (j - 1) (i + 1))
            · exact le_trans hx_le_bi sdiff_le
            · exact le_of_eq (hi_le_n_si_eq_s'ni a (Nat.le_sub_one_of_lt hi_lt_j))
          · exact le_nSup (up_to_n a (j - 1)) (i + 1)
      rw [inf_sdiff_self_left] at hle_diff_inf
      exact hle_diff_inf
  have hbpd : Pairwise (Disjoint on b) := by
    intro i j hi_ne_j x hx_le_bi hx_le_bj
    by_cases hi_j : i ≤ j
    · have hi_lt_j := lt_of_le_of_ne hi_j hi_ne_j
      exact hi_j_disjoint hi_ne_j hx_le_bi hx_le_bj hi_lt_j
    · rw [not_le] at hi_j
      rw [ne_comm] at hi_ne_j
      exact hi_j_disjoint hi_ne_j hx_le_bj hx_le_bi hi_j
  rw [hsup_a_eq_sup_b, MeasureAlgebraMeasure.disjoint hbpd]
  apply ENNReal.tsum_le_tsum
  intro i
  apply prop321Bb
  exact hb_le_a

end MeasureAlgebra
