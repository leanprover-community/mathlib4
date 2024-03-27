/-
Copyright (c) 2024 Jiecheng Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiecheng Zhao
-/
import Std.Data.Array
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
   (Array.extract.loop a i s e).size = i + e.size:=
    fun i s e a_1 ↦ extract_len_aux i s e a_1

theorem extract_end_le_start_eq_empty {a: Array α } :
    (j ≤ i) → a.extract i j = #[] := by
  exact fun a_1 ↦ extract_empty_of_stop_le_start a a_1

theorem extract_end_le_start_size_zero {a : Array α } (h: s ≥ e) : (a.extract s e).size = 0 := by
  rw [extract_end_le_start_eq_empty h]
  simp

theorem extract_size {a: Array α} : (e ≤ a.size) → (a.extract s e).size = e - s := by
  intro h
  by_cases h2: s ≤ e
  simp [extract, Nat.min_def, h]
  rw [Array.extract_loop_len]
  simp only [size_toArray, List.length_nil, Nat.add_zero]
  rw [Nat.add_comm, Nat.sub_add_cancel]
  exact h
  exact h2
  simp at h2
  rw [extract_end_le_start_size_zero]
  rw [Nat.sub_eq_zero_of_le]
  exact Nat.le_of_lt h2
  exact Nat.le_of_lt h2

theorem get_eq_list_get {a : Array α } {i : Nat} : (h: i < a.size) → (a[i]'h = a.data[i]'h) :=
  fun _ ↦ rfl

theorem get_append_aux {a b: Array α } (h : i < a.size) : i < (a ++ b).size := by
  simp only [size_append]
  apply Nat.lt_of_lt_of_le h
  exact Nat.le_add_right (size a) (size b)

theorem extract_overflow_eq_extract_to_end {a : Array α} :
  (a.size ≤ l) →  a.extract p l = a.extract p a.size := by
  intro h
  simp [extract, Nat.min_eq_right h]


theorem extract_loop_init_eq_append_aux0 {a e: Array α } : ∀ b, ∀ s, ¬ s < a.size →
  extract.loop a i s (e ++ b) = e ++ extract.loop a i s b := by
  intro b s h
  unfold extract.loop
  simp [h]

theorem append_eq_data_append {b c: Array α } : b ++ c = {data := b.data ++ c.data}
  := by
  apply ext'
  simp only [append_data]

theorem append_push {a b : Array α } : push (a ++ b) e = a ++ push b e := by
  simp [push, append_eq_data_append]

theorem extract_loop_init_eq_empty {a : Array α } {i s : Nat} (e: Array α ):
  extract.loop a i s e = e ++ extract.loop a i s #[] := by
  exact extract_loop_eq_aux a e i s

@[simp]
theorem extract_zero_length {a : Array α} :
  a.extract i i = #[] := by
  refine extract_end_le_start_eq_empty ?_
  exact Nat.le_refl i

theorem extract_append_only_first_aux {a b: Array α} :
  ∀ m i: Nat, (i + m ≤ a.size) →
   (a ++ b).extract i (i + m) = a.extract i (i + m) := by
  intro m
  induction m
  simp
  rename_i n nih
  intro i h
  unfold extract
  simp [Nat.min_def, Nat.succ_eq_add_one] at *
  have h1 : i + (n + 1) ≤ a.size + b.size := by
    apply Nat.le_trans h
    exact Nat.le_add_right (size a) (size b)
  simp [h1, h]
  unfold extract.loop
  simp
  have h2: i < a.size + b.size := by
    apply Nat.lt_of_le_of_lt _ h1
    exact Nat.le.intro rfl
  have h3: i < a.size := by
    apply Nat.lt_of_lt_of_le _ h
    refine Nat.lt_add_of_pos_right ?h
    exact Nat.zero_lt_succ n
  simp [h2, h3]
  rw [show i + (n + 1) = i + 1 + n by simp_arith] at h
  have := nih (i + 1) h
  rw [Nat.add_comm n, ←Nat.add_assoc  ] at h1
  simp [extract, Nat.min_def, h1, h] at this
  rw [show i + (n + 1) - i = n + 1 by exact Nat.add_sub_self_left i (n + 1)]
  simp
  rw [extract_loop_init_eq_empty, extract_loop_init_eq_empty (push #[] a[i])]
  apply?

theorem extract_append_of_lt {a b: Array α} {i j : Nat}:
    (j ≤ a.size) →
    (a ++ b).extract i j = a.extract i j :=  by
  intro h
  by_cases h1: i ≤ j
  let m := j - i
  have : j = i + m := by
    exact (Nat.sub_eq_iff_eq_add' h1).mp rfl
  rw [this, extract_append_only_first_aux]
  rw [← this]
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
