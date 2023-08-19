import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic

/-- A sorted nonnegative list with m elements and exactly r ≤ m non-zero elemnts has the first
(m - r) elemnts as zero -/
lemma wierd (m r : ℕ) (hrm : r ≤ m) (f : Fin m → ℝ)
    (h_nonneg : ∀ (i : Fin m), 0 ≤  f i)
    (h_nz_cnt : Fintype.card { i // f i =  0} = (m -r))
    (h_sorted : Monotone f)
    (j : Fin m):
    ( j < (m - r) ) → f j = 0 := by
  intro hjm
  have hj := eq_or_lt_of_le ( h_nonneg j)
  cases' hj with hj hj
  exact hj.symm
  exfalso
  unfold Monotone at h_sorted
  have : ∃ q : Fin m, (m - r) ≤ q ∧ f q = 0 := by
    by_contra h
    push_neg at h
    sorry

  obtain ⟨q , hq⟩ := this
  have hjq : j < q := by exact_mod_cast lt_of_lt_of_le hjm hq.left
  have h1 : (f q < f j) := by
    rw [hq.2]
    exact hj
  have h2 := h_sorted (le_of_lt hjq)
  apply (not_lt.2 h2) h1
