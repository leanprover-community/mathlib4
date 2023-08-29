/-
Copyright (c) 2021 Chris Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Bailey
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Defs

namespace String

lemma congr_append : ∀ (a b : String), a ++ b = String.mk (a.data ++ b.data)
  | ⟨_⟩, ⟨_⟩ => rfl

@[simp] lemma length_append : ∀ (as bs : String), (as ++ bs).length = as.length + bs.length
  | ⟨as⟩, ⟨bs⟩ => by
    rw [congr_append]
    -- ⊢ length { data := { data := as }.data ++ { data := bs }.data } = length { dat …
    simp only [String.length]
    -- ⊢ List.length (as ++ bs) = List.length as + List.length bs
    exact List.length_append as bs
    -- 🎉 no goals

@[simp] lemma length_replicate (n : ℕ) (c : Char) : (replicate n c).length = n := by
  simp only [String.length, String.replicate, List.length_replicate]
  -- 🎉 no goals

lemma length_eq_list_length (l : List Char) : (String.mk l).length = l.length := by
  simp only [String.length]
  -- 🎉 no goals

/-- The length of the String returned by `String.leftpad n a c` is equal
  to the larger of `n` and `s.length` -/
@[simp] lemma leftpad_length (n : ℕ) (c : Char) :
    ∀ (s : String), (leftpad n c s).length = max n s.length
  | ⟨s⟩ => by simp only [leftpad, String.length, List.leftpad_length]
              -- 🎉 no goals

lemma leftpad_prefix (n : ℕ) (c : Char) : ∀ s, isPrefix (replicate (n - length s) c) (leftpad n c s)
  | ⟨l⟩ => by simp only [isPrefix, replicate, leftpad, String.length, List.leftpad_prefix]
              -- 🎉 no goals

lemma leftpad_suffix (n : ℕ) (c : Char) : ∀ s, isSuffix s (leftpad n c s)
  | ⟨l⟩ => by simp only [isSuffix, replicate, leftpad, String.length, List.leftpad_suffix]
              -- 🎉 no goals

end String
