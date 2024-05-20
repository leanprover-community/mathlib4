/-
Copyright (c) 2021 Chris Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Bailey
-/
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Data.String.Defs
import Mathlib.Tactic.Basic

namespace String

lemma congr_append : ∀ (a b : String), a ++ b = String.mk (a.data ++ b.data)
  | ⟨_⟩, ⟨_⟩ => rfl

@[simp] lemma length_replicate (n : ℕ) (c : Char) : (replicate n c).length = n := by
  simp only [String.length, String.replicate, List.length_replicate]

lemma length_eq_list_length (l : List Char) : (String.mk l).length = l.length := by
  simp only [String.length]

/-- The length of the String returned by `String.leftpad n a c` is equal
  to the larger of `n` and `s.length` -/
@[simp] lemma leftpad_length (n : ℕ) (c : Char) :
    ∀ (s : String), (leftpad n c s).length = max n s.length
  | ⟨s⟩ => by simp only [leftpad, String.length, List.leftpad_length]

lemma leftpad_prefix (n : ℕ) (c : Char) : ∀ s, IsPrefix (replicate (n - length s) c) (leftpad n c s)
  | ⟨l⟩ => by simp only [IsPrefix, replicate, leftpad, String.length, List.leftpad_prefix]

lemma leftpad_suffix (n : ℕ) (c : Char) : ∀ s, IsSuffix s (leftpad n c s)
  | ⟨l⟩ => by simp only [IsSuffix, replicate, leftpad, String.length, List.leftpad_suffix]

end String
