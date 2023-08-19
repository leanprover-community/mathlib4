import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Card

lemma wierd0 (m : Type)[Fintype m](p: m → Prop)[DecidablePred p] :
    Fintype.card m = Fintype.card {i // p i} + Fintype.card {i // ¬ p i} := by
  rw [Fintype.card_subtype_compl, ← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
  exact Fintype.card_subtype_le _

lemma wierdm1 (m : ℕ) (h : 1 ≤ m) : 0 < m := h

/-- A sorted nonnegative list with m elements and exactly r ≤ m non-zero elemnts has the first
(m - r) elemnts as zero -/
lemma wierd1 (m r : ℕ) (hrm : r ≤ m) (f : Fin m → ℝ)
    (h_nonneg : ∀ (i : Fin m), 0 ≤  f i)
    (h_nz_cnt : Fintype.card { i // f i =  0} = r)
    (h_sorted : Monotone f)
    (j : Fin m):
    ( j < r) → f j = 0 := by
  intro hjm
  have hj := eq_or_lt_of_le ( h_nonneg j)
  cases' hj with hj hj
  · exact hj.symm
  · exfalso
    unfold Monotone at h_sorted
    have : ∃ q : Fin m, (r) ≤ q ∧ f q = 0 := by
      by_contra h
      push_neg at h
      have h1 : m - r < Fintype.card {i // f i ≠ 0} := by
        have h2 : Fintype.card {i // f i ≠ 0} = Fintype.card {j : {i // f i ≠ 0} // j < r} +
          Fintype.card {j : {i // f i ≠ 0} // ¬ (j < r)} := wierd0 _ _
        rw [h2]
        have h3 : 1 ≤ Fintype.card {j : {i // f i ≠ 0} // j < r} := by
          apply Fintype.card_pos_iff.2
          refine' Nonempty.intro ?_
          refine' ⟨ ⟨ j, ne_of_gt hj⟩, hjm ⟩
        have h4 : (m - r) ≤ Fintype.card {j : {i // f i ≠ 0} // ¬ (j < r)} := by
          simp only [not_lt, tsub_le_iff_right]
          sorry
        have h5 : m - r < m - r + 1 := by exact Nat.lt.base (m - r)
        apply lt_of_lt_of_le h5 _
        rw [Nat.add_comm]
        exact (Nat.add_le_add h3 h4)
      simp only [Fintype.card_subtype_compl, Fintype.card_fin] at h1
      rw [h_nz_cnt] at h1
      apply (lt_irrefl _) h1
    obtain ⟨q , hq⟩ := this
    have hjq : j < q := by exact_mod_cast lt_of_lt_of_le hjm hq.left
    have h1 : (f q < f j) := by
      rw [hq.2]
      exact hj
    have h2 := h_sorted (le_of_lt hjq)
    apply (not_lt.2 h2) h1
