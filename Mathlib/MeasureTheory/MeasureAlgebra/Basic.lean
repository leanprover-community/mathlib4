/-
Copyright (c) 2025 William Du. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Du
-/
import Mathlib.MeasureTheory.MeasureAlgebra.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Init.SimpLemmas

/-!
TODO: docstring
-/

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

variable {m : MeasurableAlgebra α} {μ : MeasureAlgebraMeasure α} {a b : α}

lemma prop321Ba (hd : a ⊓ b = ⊥) : μ (a ⊔ b) = (μ a) + (μ b) := by
  let s (n : ℕ) : α :=
    if n = 0 then a
    else if n = 1 then b
    else ⊥
  have hsup : μ (a ⊔ b) = μ (⨆i s) := by
    have hsup_le : a ⊔ b ≤ ⨆i s := by
      rw [sup_le_iff]
      constructor
      · exact le_nSup s 0
      · exact le_nSup s 1
    have hle_sup : ⨆i s ≤ a ⊔ b := by
      rw [nSup_le_iff]
      rintro (_ | _ | i )
      · exact le_sup_left
      · rw [zero_add]; exact le_sup_right
      · exact bot_le -- lean is smart enough apparently
    rw [le_antisymm hle_sup hsup_le]
  have hpd : Pairwise (Disjoint on s) := by
    intro i j hi_ne_j x hx_le_si hx_le_sj
    rcases i with _ | _ | i
    repeat {
      rcases j with _ | _ | j
      repeat {
        try { exfalso; exact hi_ne_j rfl }
        try { rw [← hd]; exact le_inf hx_le_si hx_le_sj }
        try { rw [← hd]; exact le_inf hx_le_sj hx_le_si }
        try { exact hx_le_sj }
      }
    }
    exact hx_le_si
  have ne_0_ne_1_eq_bot {x : ℕ} (hcond0 : x ≠ 0) (hcond1 : x ≠ 1) : s x = ⊥ := by
    unfold s
    -- how?
    rw [ne_eq, ←Lean.Grind.eq_false_eq] at hcond0
    rw [ite_congr hcond0 (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
    rw [ne_eq, ←Lean.Grind.eq_false_eq] at hcond1
    rw [ite_congr hcond1 (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
  have hsum : ∑' i, μ (s i) = (μ a) + (μ b) := by
    let d : Finset ℕ := {0, 1}
    have hf : ∀ x ∉ d, μ (s x) = 0 := by
      intro x hx_not_mem_d
      have h0_in_d : 0 ∈ d := by
        rw [Finset.mem_insert]
        left
        rfl
      have h1_in_d : 1 ∈ d := by
        rw [Finset.mem_insert]
        right
        exact Finset.mem_singleton.mpr rfl
      have hmem_d_not_eq := (Finset.forall_mem_not_eq.mpr hx_not_mem_d)
      rw [ne_0_ne_1_eq_bot ((hmem_d_not_eq 0) h0_in_d) ((hmem_d_not_eq 1) h1_in_d)]
      exact μ.zero
    rw [tsum_eq_sum hf]
    have h0_not_mem_1 : 0 ∉ ({1} : Finset ℕ) := by
      rw [Finset.mem_singleton]; exact zero_ne_one
    rw [Finset.sum_insert h0_not_mem_1, Finset.sum_singleton]
    rfl
  rw [hsup, MeasureAlgebraMeasure.disjoint hpd, hsum]

lemma prop321Bb (hab : a ≤ b) : μ a ≤ μ b := by
  rw [←sup_inf_sdiff b a]
  rw [prop321Ba (inf_inf_sdiff b a)]
  rw [inf_of_le_right hab]
  apply self_le_add_right

lemma prop321Bc : μ (a ⊔ b) ≤ μ a + μ b := by
  rw [←sdiff_sup_self]
  rw [prop321Ba inf_sdiff_self_left]
  apply add_le_add_right
  apply prop321Bb sdiff_le

lemma prop321Bd {a : ℕ → α} : μ (⨆i a) ≤ ∑' i, μ (a i) := by
  -- maybe generalize a' and b'?
  let up_to_n (s : ℕ → α) :=
    fun n ↦ fun i ↦ if i ≤ n then s i else ⊥
  let a' (n : ℕ) : ℕ → α :=
    up_to_n a n
  let b (i : ℕ) : α :=
    if i = 0 then a 0
    else (a i) \ ⨆i (a' (i - 1))
  let b' (n : ℕ) : ℕ → α :=
    up_to_n b n
  have hsup_a'n_eq_sup_b'n {n : ℕ} : ⨆i (a' n) = ⨆i (b' n) := by
    induction' n with n hn
    · unfold a'; unfold b'; unfold up_to_n
      -- fix simp
      simp_all only [nonpos_iff_eq_zero, ↓reduceIte, b, a']
    · have hf_sup (s : ℕ → α) : ⨆i (up_to_n s) (n + 1) = s (n + 1) ⊔ ⨆i (up_to_n s) n := by
        have : s (n + 1) = up_to_n s (n + 1) (n + 1) := by
          unfold up_to_n
          have hcond_true : (n + 1 ≤ n + 1) = True := by
            rw [Lean.Grind.eq_true_eq]
          rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
        rw [this]
        -- unfold up_to_n
        apply le_antisymm
        · apply nSup_le
          intro i
          by_cases temp : i ≤ n + 1
          by_cases temp2 : i ≤ n
          · unfold up_to_n
            have hcond_true : (i ≤ n + 1) = True := by
              rw [Lean.Grind.eq_true_eq]
              exact temp
            rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
            apply le_sup_of_le_right
            have temp3 : s i = (fun i ↦ if i ≤ n then s i else ⊥) i := by
              simp
              have hcond_true' : (i ≤ n) = True := by
                rw [Lean.Grind.eq_true_eq]
                exact temp2
              rw [ite_congr hcond_true' (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
            rw [temp3]
            exact le_nSup (fun i ↦ if i ≤ n then s i else ⊥) i
          · have temp3 : i = n + 1 := by
              apply le_antisymm
              · exact temp
              · apply not_le.mp at temp2
                exact Nat.add_one_le_iff.mpr temp2
            rw [temp3]
            exact le_sup_left
          · unfold up_to_n
            have hcond_false : (i ≤ n + 1) = False := by
              rw [Lean.Grind.eq_false_eq]
              exact temp
            rw [ite_congr hcond_false (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
            exact bot_le
        · apply sup_le
          · apply le_nSup
          · apply nSup_le
            intro i
            unfold up_to_n
            by_cases temp : i ≤ n
            · have hcond_true : (i ≤ n) = True := by
                rw [Lean.Grind.eq_true_eq]
                exact temp
              rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
              have temp2 : s i = (fun i ↦ if i ≤ n + 1 then s i else ⊥) i := by
                simp
                have hcond_true' : (i ≤ n + 1) = True := by
                  rw [Lean.Grind.eq_true_eq]
                  exact Nat.le_add_right_of_le temp
                rw [ite_congr hcond_true' (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
              rw [temp2]
              exact le_nSup (fun i ↦ if i ≤ n + 1 then s i else ⊥) i
            · have hcond_false : (i ≤ n) = False := by
                rw [Lean.Grind.eq_false_eq]
                exact temp
              rw [ite_congr hcond_false (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
              exact bot_le
      rw [hf_sup a, hf_sup b, ←hn]
      unfold b
      have hcond_false : (n + 1 = 0) = False := by
        rw [Lean.Grind.eq_false_eq, Nat.add_eq_zero]
        intro ⟨_, h1_eq_0⟩
        exact one_ne_zero h1_eq_0
      rw [ite_congr hcond_false (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false, add_tsub_cancel_right]
      rw [sdiff_sup_self]
  have hsup_a_eq_sup_b : ⨆i a = ⨆i b := by
    apply le_antisymm
    · apply nSup_le
      intro i
      unfold b
      have hai_le_nSup_b'i : a i ≤ ⨆i (up_to_n b i) := by
        rw [←hsup_a'n_eq_sup_b'n]
        -- unfold a'
        have : a i = a' i i := by
          unfold a' up_to_n
          have hcond_true : (i ≤ i) = True := by
            rw [Lean.Grind.eq_true_eq]
          rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
        rw [this]
        exact le_nSup (up_to_n a i) i
      have hb'i_le_b : ⨆i (up_to_n b i) ≤ ⨆i b := by
        apply nSup_le
        intro j
        unfold up_to_n
        by_cases hji : j ≤ i
        · have hcond_true : (j ≤ i) = True := by
            rw [Lean.Grind.eq_true_eq]
            exact hji
          rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
          exact le_nSup b j
        · have hcond_false : (j ≤ i) = False := by
            rw [Lean.Grind.eq_false_eq]
            exact hji
          rw [ite_congr hcond_false (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
          exact bot_le
      apply le_trans hai_le_nSup_b'i hb'i_le_b
    · apply nSup_le
      intro i
      have b_le_a: b i ≤ a i := by
        unfold b
        by_cases hi : i = 0
        · have hcond_true : (i = 0) = True := by
            rw [Lean.Grind.eq_true_eq]
            exact hi
          rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true, hi]
        · have hcond_false : (i = 0) = False := by
            rw [Lean.Grind.eq_false_eq]
            exact hi
          rw [ite_congr hcond_false (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
          exact sdiff_le
      exact le_trans b_le_a (le_nSup a i)
    -- a = lim a' n
    -- b = lim b' n
    -- therefore eq
  have hbpd : Pairwise (Disjoint on b) := by
    intro i j hi_ne_j x hx_le_bi hx_le_bj
    have nameme {i j : ℕ} (hi_ne_j : i ≠ j)
        (hx_le_bi : x ≤ b i) (hx_le_bj : x ≤ b j)
        (hi_lt_j : i < j)
        : x ≤ ⊥ := by
      unfold b at *
      by_cases hi : i = 0
      · -- fix all simp
        simp [hi] at hx_le_bi
        have hj : ¬j = 0 := by
          intro hj
          rw [hi, hj] at hi_ne_j
          apply hi_ne_j
          rfl
        simp [hj] at hx_le_bj
        have ha0_le_a'j : a 0 ≤ ⨆i a' (j - 1) := by
          have ha0_le_a'0 : a 0 ≤ (a' (j - 1)) 0 := by
            unfold a'; unfold up_to_n
            have hcond_true : (0 ≤ j - 1) = True := by
              rw [Lean.Grind.eq_true_eq]
              rw [hi] at hi_lt_j
              exact Nat.le_sub_one_of_lt hi_lt_j
            rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
          have ha'0_le_a'j : (a' (j - 1)) 0 ≤ ⨆i a' (j - 1) := by
            exact le_nSup (a' (j - 1)) 0
          exact le_trans ha0_le_a'0 ha'0_le_a'j
        have hx_le_a'j : x ≤ ⨆i a' (j - 1) := by
          exact le_trans hx_le_bi ha0_le_a'j
        have hle_diff_inf := le_inf hx_le_bj hx_le_a'j
        rw [inf_sdiff_self_left] at hle_diff_inf
        exact hle_diff_inf
      · simp [hi] at hx_le_bi
        have hj : ¬j = 0 := by
          intro hj
          rw [hj] at hi_lt_j
          exact (Nat.not_lt_zero i) hi_lt_j
        simp [hj] at hx_le_bj
        have hai_le_a'j : a i ≤ ⨆i a' (j - 1) := by
          have hai_eq_a'i : a i = a' (j - 1) i := by
            unfold a'; unfold up_to_n
            have hcond_true : (i ≤ j - 1) = True := by
              rw [Lean.Grind.eq_true_eq]
              apply Nat.le_sub_one_of_lt hi_lt_j
            rw [ite_congr hcond_true (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
          rw [hai_eq_a'i]
          exact le_nSup (a' (j - 1)) i
        have hx_le_a'j : x ≤ ⨆i a' (j - 1) := by
          exact le_trans (le_trans hx_le_bi sdiff_le) hai_le_a'j
        have hle_diff_inf := le_inf hx_le_bj hx_le_a'j
        rw [inf_sdiff_self_left] at hle_diff_inf
        exact hle_diff_inf
    by_cases hi_j : i ≤ j
    · have hi_lt_j := lt_of_le_of_ne hi_j hi_ne_j
      exact nameme hi_ne_j hx_le_bi hx_le_bj hi_lt_j
    · rw [not_le] at hi_j
      rw [ne_comm] at hi_ne_j
      exact nameme hi_ne_j hx_le_bj hx_le_bi hi_j
  rw [hsup_a_eq_sup_b, MeasureAlgebraMeasure.disjoint hbpd]
  apply ENNReal.tsum_le_tsum
  intro i
  apply prop321Bb
  unfold b
  by_cases hcond : i = 0
  · nth_rw 5 [hcond]
    rw [←Lean.Grind.eq_true_eq (i = 0)] at hcond
    rw [ite_congr hcond (fun _ ↦ rfl) (fun _ ↦ rfl), ite_true]
  · rw [←Lean.Grind.eq_false_eq (i = 0)] at hcond
    rw [ite_congr hcond (fun _ ↦ rfl) (fun _ ↦ rfl), ite_false]
    exact sdiff_le
