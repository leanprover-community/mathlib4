/-
Copyright (c) 2024 Jiecheng Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiecheng Zhao
-/
import Batteries.Data.Array.Lemmas
/-!
# Lemmas about `Array.extract`

Some useful lemmas about Array.extract
-/
set_option autoImplicit true

namespace Array

@[simp]
theorem extract_eq_nil_of_start_eq_end {a : Array α} :
    a.extract i i = #[] := by
  refine extract_empty_of_stop_le_start a ?h
  exact Nat.le_refl i

theorem extract_append_left {a b : Array α} {i j : Nat} (h : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  apply ext
  · simp only [size_extract, size_append]
    omega
  · intro h1 h2 h3
    rw [get_extract, get_append_left, get_extract]

theorem extract_append_right {a b : Array α} {i j : Nat} (h : a.size ≤ i) :
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := by
  apply ext
  · rw [size_extract, size_extract, size_append]
    omega
  · intro k hi h2
    rw [get_extract, get_extract,
      get_append_right (show size a ≤ i + k by omega)]
    congr
    omega

theorem extract_eq_of_size_le_end {a : Array α} (h : a.size ≤ l) :
    a.extract p l = a.extract p a.size := by
  simp only [extract, Nat.min_eq_right h, Nat.sub_eq, mkEmpty_eq, Nat.min_self]

theorem extract_extract {a : Array α} (h : s1 + e2 ≤ e1) :
    (a.extract s1 e1).extract s2 e2 = a.extract (s1 + s2) (s1 + e2) := by
  apply ext
  · simp only [size_extract]
    omega
  · intro i h1 h2
    simp only [get_extract, Nat.add_assoc]

end Array
