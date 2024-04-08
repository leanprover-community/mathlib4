/-
Copyright (c) 2024 Jiecheng Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiecheng Zhao
-/
import Std.Data.Array.Lemmas
/-!
# lemmas about Array.extract

Some useful lemmas about Array.extract
-/
set_option autoImplicit true

namespace Array


@[simp]
theorem extract_zero_length {a : Array α} :
    a.extract i i = #[] := by
  refine extract_empty_of_stop_le_start a ?h
  exact Nat.le_refl i

theorem size_extract_to_stop {a: Array α} : (e ≤ a.size) → (a.extract s e).size = e - s := by
  intro h1
  simp only [size_extract]
  rw [Nat.min_eq_left h1]

theorem extract_append_left {a b: Array α} {i j : Nat} (h: j ≤ a.size):
    (a ++ b).extract i j = a.extract i j := by
  apply ext
  · have h' : j ≤ a.size + b.size := by
      apply Nat.le_trans h
      exact Nat.le_add_right (size a) (size b)
    simp only [size_extract, size_append, h', Nat.min_eq_left, h]
  · intro h1 h2 h3
    simp only [get_extract]
    rw [get_append_left]

theorem extract_append_right {a b: Array α} {i j : Nat} (h: i ≥ a.size):
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := by
  by_cases h1 : i ≥ j
  · rw [extract_empty_of_stop_le_start _ h1, extract_empty_of_stop_le_start]
    exact Nat.sub_le_sub_right h1 (size a)
  by_cases h2 : i ≥ (a ++ b).size
  · have h3:extract (a ++ b) i j = #[] := extract_empty_of_size_le_start (a ++ b) h2
    have h4:extract b (i - size a) (j - size a) = #[] := by
      apply extract_empty_of_size_le_start
      rw [size_append] at h2
      exact (Nat.le_sub_iff_add_le' h).mpr h2
    rw [h3, h4]
  · simp only [ge_iff_le, Nat.not_le] at h1
    simp only [size_append, ge_iff_le, Nat.not_le] at h2
    apply ext
    · simp only [size_extract]
      by_cases h3: j ≤ a.size + b.size
      · have h4: j - a.size ≤ b.size := Nat.sub_le_iff_le_add'.mpr h3
        simp only [size_append, h3, Nat.min_eq_left, h4]
        rw [Nat.sub_sub, Nat.add_comm, Nat.sub_add_cancel h]
      · have h3': j ≥ a.size + b.size := Nat.le_of_not_ge h3
        have h4:  j - a.size ≥ b.size := Nat.le_sub_of_add_le' h3'
        simp only [size_append, h3', Nat.min_eq_right, h4]
        apply @Nat.add_right_cancel _ (i - a.size)
        have h5 : i ≤ a.size + b.size := Nat.le_of_succ_le h2
        have h6 : i - a.size ≤ b.size := Nat.sub_le_iff_le_add'.mpr h5
        rw [← Nat.add_sub_assoc h, Nat.sub_add_cancel h5, Nat.add_comm,
          Nat.add_sub_cancel, Nat.sub_add_cancel h6]
    · intro k h4 h5
      simp only [get_extract, get_append_right (Nat.le_trans h (Nat.le_add_right i k)),
        Nat.sub_add_comm h]

theorem extract_overflow_eq_extract_to_end {a : Array α} :
    (a.size ≤ l) →  a.extract p l = a.extract p a.size := by
  intro h
  simp only [extract, Nat.min_eq_right h, Nat.sub_eq, mkEmpty_eq, Nat.min_self]

theorem extract_extract_aux {a : Array α } :
    (s1 + e2 ≤ e1) → (e1 ≤ a.size) →
    (a.extract s1 e1).extract s2 e2 = a.extract (s1 + s2) (s1 + e2) := by
  intro h1 h2
  apply ext
  · have hsize1 : s1 + e2 ≤ a.size := Nat.le_trans h1 h2
    have hsize2 : e2 ≤ e1 - s1 := Nat.le_sub_of_add_le' h1
    simp only [size_extract, h2, Nat.min_eq_left, hsize2, hsize1]
    rw [Nat.sub_add_eq, Nat.add_comm, Nat.add_sub_cancel]
  · intro i h1 h2
    simp only [get_extract, Nat.add_assoc]

theorem extract_extract {a : Array α }
    (h2 : s1 + e2 ≤ e1) :
    (a.extract s1 e1).extract s2 e2 = a.extract (s1 + s2) (s1 + e2) := by
  by_cases h: e1 ≤ a.size
  · exact extract_extract_aux h2 h
  by_cases h3 : s1 + e2 ≤ a.size
  · rw [extract_overflow_eq_extract_to_end (Nat.le_of_not_ge h : e1 ≥ a.size),
        extract_extract_aux h3 (Nat.le_of_eq rfl : a.size ≤ a.size)]
  by_cases h1 : s1 ≤ a.size
  · have h4: s1 + (extract a s1 a.size).size = a.size := by
      rw [size_extract_to_stop (Nat.le_of_eq rfl),
          Nat.add_comm,
          Nat.sub_add_cancel h1]
    have h5: e2 ≥ (extract a s1 (size a)).size := by
      apply @Nat.le_of_add_le_add_left s1
      rw [h4]
      exact Nat.le_of_not_ge h3
    rw [extract_overflow_eq_extract_to_end (Nat.le_of_not_ge h : e1 ≥ a.size),
    extract_overflow_eq_extract_to_end (Nat.le_of_not_ge h3 : s1 + e2 ≥ a.size),
    extract_overflow_eq_extract_to_end h5,
    extract_extract_aux (Nat.le_of_eq h4) (Nat.le_of_eq rfl),
    h4]
  · simp only [Nat.not_le] at h1
    have hsize1: a.size ≤ s1 := Nat.le_of_lt h1
    have hsize2: a.size ≤ s1 + s2 := by
      apply Nat.le_trans hsize1
      exact Nat.le_add_right s1 s2
    rw [extract_empty_of_size_le_start a hsize1,
      extract_empty_of_size_le_start a hsize2,
      extract_empty]

end Array
