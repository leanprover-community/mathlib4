import Mathlib.Data.List.Basic
import Mathlib.Data.String.Defs

namespace String

lemma congr_append : ∀ (a b : String), a ++ b = String.mk (a.data ++ b.data)
| ⟨a⟩, ⟨b⟩ => rfl

@[simp] lemma length_append : ∀ (as bs : String), (as ++ bs).length = as.length + bs.length
| ⟨as⟩, ⟨bs⟩ => by
  rw [congr_append]
  simp only [String.length]
  exact List.length_append as bs

@[simp] lemma length_repeat' (c : Char) (n : ℕ) : (repeat' c n).length = n :=
by simp only [String.length, String.repeat', List.length_repeat']

lemma length_eq_list_length (l : List Char) : (String.mk l).length = l.length :=
by simp only [String.length]

/-- The length of the String returned by `String.leftpad n a c` is equal
  to the larger of `n` and `s.length` -/
@[simp] lemma leftpad_length (n : ℕ) (c : Char) : ∀ (s : String), (leftpad n c s).length = max n s.length
| ⟨s⟩ => by simp only [leftpad, String.length, List.leftpad_length]

lemma leftpad_prefix (n : ℕ) (c : Char) : ∀ s, isPrefix (repeat' c (n - length s)) (leftpad n c s)
| ⟨l⟩ => by simp only [isPrefix, repeat', leftpad, String.length, List.leftpad_prefix]

lemma leftpad_suffix (n : ℕ) (c : Char) : ∀ s, isSuffix s (leftpad n c s)
| ⟨l⟩ => by simp only [isSuffix, repeat', leftpad, String.length, List.leftpad_suffix]

end String
