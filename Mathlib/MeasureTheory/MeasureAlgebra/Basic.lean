import Mathlib.MeasureTheory.MeasureAlgebra.Defs

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
      apply (SigmaOrderCompleteLattice.le_nSup s 0)
      apply (SigmaOrderCompleteLattice.le_nSup s 1)
    have hle_sup : ⨆i s ≤ a ⊔ b := by
      rw [nSup_le_iff]
      rintro (_ | _ | i )
      · apply le_sup_left
      · rw [zero_add]; apply le_sup_right
      · exact bot_le -- lean is smart enough apparently
    rw [le_antisymm hle_sup hsup_le]
  have hpd : Pairwise (Disjoint on s) := by
    unfold Pairwise Disjoint
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
  -- how to coerce
  have hdisjoint : μ (⨆i s) = ∑' (i : ℕ), μ (s i) := by
    exact MeasureAlgebraMeasure.disjoint μ s hpd
  have ne_0_ne_1_eq_bot {x : ℕ} (h0 : x ≠ 0) (h1 : x ≠ 1) : s x = ⊥ := by
    unfold s
    -- how?
    simp_all [↓reduceIte]
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
  rw [hsup, hdisjoint, hsum]

lemma prop321Bb (hab : a ≤ b) : μ a ≤ μ b := by
  rw [←sup_inf_sdiff b a]
  rw [prop321Ba (inf_inf_sdiff b a)]
  rw [inf_of_le_right hab]
  apply self_le_add_right
