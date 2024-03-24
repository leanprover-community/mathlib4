/-
Copyright (c) 2024 Jiecheng Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiecheng Zhao
-/

/-!
# lemmas about Array.extract

Some useful lemmas about Array.extract
-/
set_option autoImplicit true



namespace Array

theorem extract_len_aux {a : Array α} :
    ∀ i s e,
   (s + i ≤ a.size) →
   List.length (Array.extract.loop a i s e).data = i + e.size:= by
  intro i
  induction i
  intro x h
  simp only [Nat.zero_eq, Nat.add_zero, Nat.zero_add]
  unfold Array.extract.loop
  simp only [dite_eq_ite, ite_self, implies_true]
  intro x e h
  rename_i n n_ih
  unfold Array.extract.loop
  simp only [get_eq_getElem]
  have : x < Array.size a := by
    rw [Nat.add_succ] at h
    have := Nat.lt_of_succ_le h
    apply Nat.lt_of_le_of_lt _ this
    exact Nat.le_add_right x n
  simp only [this, ↓reduceDite]
  rw [show x + Nat.succ n = x + 1 + n by simp_arith] at h
  rw [n_ih (x + 1) (Array.push e a[x]) h]
  simp_arith

theorem extract_loop_len {a : Array α} :
    ∀ i s e,
   (s + i ≤ a.size) →
   (Array.extract.loop a i s e).size = i + e.size:= by
  intro i s e h
  rw [Array.size]
  apply Array.extract_len_aux _ _ _ h

theorem extract_loop_0 {array: Array α }: Array.extract.loop array 0 i e = e := by
  unfold Array.extract.loop
  simp

theorem extract_end_le_start_eq_empty {a: Array α } :
    (j ≤ i) → a.extract i j = #[] := by
  intro h
  simp only [extract, Nat.min_def, Nat.sub_eq, mkEmpty_eq]
  split <;> rename_i h1
  simp only [show j - i = 0 by exact Nat.sub_eq_zero_of_le h, extract_loop_0]
  simp only [show a.size - i = 0 by
      apply Nat.sub_eq_zero_of_le
      apply Nat.le_trans _ h
      simp at h1
      exact Nat.le_of_succ_le h1,
    extract_loop_0]

theorem extract_end_le_start_size_zero {a : Array α } (h: s ≥ e) : (a.extract s e).size = 0 := by
  rw [extract_end_le_start_eq_empty h]
  simp

theorem extract_size {a: Array α} : (e ≤ a.size) → (a.extract s e).size = e - s := by
  intro h
  by_cases h2: s ≤ e
  simp [extract, Nat.min_def, h]
  rw [Array.extract_loop_len]
  simp?
  rw [Nat.add_comm, Nat.sub_add_cancel]
  exact h
  exact h2
  simp at h2
  rw [extract_end_le_start_size_zero]
  rw [Nat.sub_eq_zero_of_le]
  exact Nat.le_of_lt h2
  exact Nat.le_of_lt h2

@[simp]
theorem size_of_append {a b : Array α }: (a ++ b).size = a.size + b.size := by
  simp [size]

theorem get_eq_list_get {a : Array α } {i : Nat} : (h: i < a.size) → (a[i]'h = a.data[i]'h) := by
  intro h
  exact rfl

theorem get_append_only_frist_aux {a b: Array α } (h : i < a.size) : i < (a ++ b).size := by
  simp only [size_of_append]
  apply Nat.lt_of_lt_of_le h
  exact Nat.le_add_right (size a) (size b)

theorem get_append_only_first {a b: Array α } (h : i < a.size):
    (a ++ b)[i]'(get_append_only_frist_aux h) = a[i] := by
  simp only [get_eq_list_get, append_data]
  exact List.get_append i h

/- The lemma below is still incomplete, not rearranged and fixed yet. -/

theorem get_append_only_second {a b: Array α} (h : i ≥ a.size) (h2: i < a.size + b.size) :
    (a ++ b)[i]'(sorry) = b[i - a.size]'(sorry) := by sorry

theorem extract_append_only_first {a b: Array α} {i j : Nat}:
    (j ≤ a.size) →
    (a ++ b).extract i j = a.extract i j :=  by
  intro h
  by_cases h1: i ≤ j
  let m := j - i
  have : j = i + m := by
    exact (Nat.sub_eq_iff_eq_add' h1).mp rfl
  rw [this, extract_append_only_first_aux]
  rw [←this]
  exact h
  simp at h1
  rw [extract_end_le_start_eq_empty, extract_end_le_start_eq_empty]
  apply le_of_lt h1
  apply le_of_lt h1

theorem extract_append_only_second {a b: Array α} {i j : Nat}:
    (i ≥ a.size) →
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := sorry



theorem extract_mid_split {a: Array α} :
    i ≤ j → j ≤ k → a.extract i k = a.extract i j ++ a.extract j k := by sorry

theorem extract_start_overflow_eq_empty {a: Array α} (h: s ≥ a.size) :
    a.extract s e = #[] := by sorry

theorem extract_extract {a : Array α } : (s1 + s2 ≤ a.size) →
    (e2 + s1 ≤ e1) → (e1 ≤ a.size) →
    (a.extract s1 e1).extract s2 e2 = a.extract (s1 + s2) (s1 + e2) := by
    sorry

end Array
