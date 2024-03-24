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

theorem extract_size {a: Array α} : (e ≤ a.size) → (a.extract s e).size = e - s := sorry

theorem extract_append_only_first {a b: Array α} {i j : Nat}:
    (j ≤ a.size) →
    (a ++ b).extract i j = a.extract i j := sorry

theorem extract_append_only_second {a b: Array α} {i j : Nat}:
    (i ≥ a.size) →
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := sorry

theorem get_append_only_first {a b: Array α } (h : i < a.size):
    (a ++ b)[i]'(sorry) = a[i] := by sorry

theorem get_append_only_second {a b: Array α} (h : i ≥ a.size) (h2: i < a.size + b.size) :
    (a ++ b)[i]'(sorry) = b[i - a.size]'(sorry) := by sorry

theorem extract_mid_split {a: Array α} :
    i ≤ j → j ≤ k → a.extract i k = a.extract i j ++ a.extract j k := by sorry

theorem extract_start_overflow_eq_empty {a: Array α} (h: s ≥ a.size) :
    a.extract s e = #[] := by sorry

theorem extract_extract {a : Array α } : (s1 + s2 ≤ a.size) →
    (e2 + s1 ≤ e1) → (e1 ≤ a.size) →
    (a.extract s1 e1).extract s2 e2 = a.extract (s1 + s2) (s1 + e2) := by
    sorry

end Array
