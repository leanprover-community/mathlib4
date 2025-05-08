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
    · rcases j with _ | _ | j
      · exfalso
        exact hi_ne_j rfl
      · rw [← hd]
        exact le_inf hx_le_si hx_le_sj
      · exact hx_le_sj
    · rcases j with _ | _ | j
      · rw [← hd]
        exact le_inf hx_le_sj hx_le_si
      · exfalso
        exact hi_ne_j rfl
      · exact hx_le_sj
    · exact hx_le_si
  have hdisjoint : μ (⨆i s) = ∑' (i : ℕ), μ (s i) := by
    exact MeasureAlgebraMeasure.disjoint μ s hpd
  have hsum : ∑' i, μ (s i) = (μ a) + (μ b) := by
    let d : Finset ℕ := ({0, 1} : Set ℕ).toFinset
    have hf : ∀ x ∉ d, μ (s x) = 0 := by
      intro x hx_not_mem_d
      have temp := Finset.forall_mem_not_eq.mpr hx_not_mem_d
      have temp2 := (temp 0)
      -- what does this do?
      simp_all [↓reduceIte, s, d]
      exact μ.zero
    rw [tsum_eq_sum hf]
    -- what
    simp_all only [Set.toFinset_insert, Set.toFinset_singleton, Finset.mem_insert, Finset.mem_singleton, not_or, ↓reduceIte, and_imp, zero_ne_one, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, one_ne_zero, d, s]
  rw [hsup, hdisjoint, hsum]

lemma prop321Bb (hab : a ≤ b) : μ a ≤ μ b := by
  rw [←sup_inf_sdiff b a]
  rw [prop321Ba (inf_inf_sdiff b a)]
  rw [inf_of_le_right hab]
  apply self_le_add_right
