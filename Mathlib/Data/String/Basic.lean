/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Lex
import Mathlib.Data.Char

/-!
# Strings

Supplementary theorems about the `string` type.
-/


namespace String

/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
def ltb : Iterator → Iterator → Bool
  | s₁, s₂ => by
    cases s₂.hasNext; · exact false
    cases h₁ : s₁.hasNext; · exact true
    exact
      if s₁.curr = s₂.curr then ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
#align string.ltb String.ltb

instance hasLt' : LT String :=
  ⟨fun s₁ s₂ => ltb s₁.mkIterator s₂.mkIterator⟩
#align string.has_lt' String.hasLt'

instance decidableLt : @DecidableRel String (· < ·) := by infer_instance
#align string.decidable_lt String.decidableLt

-- short-circuit type class inference
@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList
  | ⟨i₁⟩, ⟨i₂⟩ => by
    suffices ∀ {p₁ p₂ s₁ s₂}, ltb ⟨s₁, p₁⟩ ⟨s₂, p₂⟩ ↔ s₁ < s₂ by
      sorry
    intros p₁ p₂ s₁ s₂
    induction' s₁ with a s₁ IH generalizing p₁ p₂ s₂ <;> cases' s₂ with b s₂ <;> rw [ltb] <;>
      simp [Iterator.hasNext]
    · rfl
    · exact iff_of_true rfl List.Lex.nil
    · exact iff_of_false Bool.ff_ne_tt (not_lt_of_lt List.Lex.nil)
    · dsimp [iterator.has_next, iterator.curr, iterator.next]
      split_ifs
      · subst b
        exact IH.trans list.lex.cons_iff.symm
      · simp
        refine' ⟨List.Lex.rel, fun e => _⟩
        cases e
        · cases h rfl
        assumption
#align string.lt_iff_to_list_lt String.lt_iff_toList_lt

instance hasLe : LE String :=
  ⟨fun s₁ s₂ => ¬s₂ < s₁⟩
#align string.has_le String.hasLe

instance decidableLe : @DecidableRel String (· ≤ ·) := inferInstance
#align string.decidable_le String.decidableLe

-- short-circuit type class inference
@[simp]
theorem le_iff_toList_le {s₁ s₂ : String} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList :=
  (not_congr lt_iff_toList_lt).trans not_lt
#align string.le_iff_to_list_le String.le_iff_toList_le

theorem to_list_inj : ∀ {s₁ s₂}, toList s₁ = toList s₂ ↔ s₁ = s₂
  | ⟨_⟩, _ => ⟨congr_arg _, congr_arg _⟩
#align string.to_list_inj String.to_list_inj

theorem nil_as_string_eq_empty : [].asString = "" :=
  rfl
#align string.nil_as_string_eq_empty String.nil_as_string_eq_empty

@[simp]
theorem to_list_empty : "".toList = [] :=
  rfl
#align string.to_list_empty String.to_list_empty

theorem as_string_inv_to_list (s : String) : s.toList.asString = s := by
  cases s
  rfl
#align string.as_string_inv_to_list String.as_string_inv_to_list

@[simp]
theorem to_list_singleton (c : Char) : (String.singleton c).toList = [c] :=
  rfl
#align string.to_list_singleton String.to_list_singleton

theorem to_list_nonempty : ∀ {s : String}, s ≠ String.empty → s.toList = s.head :: (s.popn 1).toList
  | ⟨s⟩, h => by cases s <;> [cases h rfl, rfl]
#align string.to_list_nonempty String.to_list_nonempty

@[simp]
theorem head_empty : "".data.head = default :=
  rfl
#align string.head_empty String.head_empty

@[simp]
theorem popn_empty {n : ℕ} : "".popn n = "" := by
  induction' n with n hn
  · rfl
  · rcases hs : "" with ⟨_ | ⟨hd, tl⟩⟩
    · rw [hs] at hn
      conv_rhs => rw [← hn]
      simp only [popn, mk_iterator, iterator.nextn, iterator.next]
    · simpa only [← to_list_inj] using hs
#align string.popn_empty String.popn_empty

instance : LinearOrder String where
  lt := (· < ·)
  le := (· ≤ ·)
  decidableLt := by infer_instance
  decidableLe := String.decidableLe
  DecidableEq := by infer_instance
  le_refl a := le_iff_to_list_le.2 le_rfl
  le_trans a b c := by
    simp only [le_iff_to_list_le]
    exact fun h₁ h₂ => h₁.trans h₂
  le_total a b := by
    simp only [le_iff_to_list_le]
    exact le_total _ _
  le_antisymm a b := by
    simp only [le_iff_to_list_le, ← to_list_inj]
    apply le_antisymm
  lt_iff_le_not_le a b := by simp only [le_iff_to_list_le, lt_iff_to_list_lt, lt_iff_le_not_le]

end String

open String

theorem List.to_list_inv_as_string (l : List Char) : l.asString.toList = l := by
  cases hl : l.as_string
  exact StringImp.mk.inj hl.symm
#align list.to_list_inv_as_string List.to_list_inv_as_string

@[simp]
theorem List.length_as_string (l : List Char) : l.asString.length = l.length :=
  rfl
#align list.length_as_string List.length_as_string

@[simp]
theorem List.as_string_inj {l l' : List Char} : l.asString = l'.asString ↔ l = l' :=
  ⟨fun h => by rw [← List.to_list_inv_as_string l, ← List.to_list_inv_as_string l', to_list_inj, h],
    fun h => h ▸ rfl⟩
#align list.as_string_inj List.as_string_inj

@[simp]
theorem String.length_to_list (s : String) : s.toList.length = s.length := by
  rw [← String.as_string_inv_to_list s, List.to_list_inv_as_string, List.length_as_string]
#align string.length_to_list String.length_to_list

theorem List.as_string_eq {l : List Char} {s : String} : l.asString = s ↔ l = s.toList := by
  rw [← as_string_inv_to_list s, List.as_string_inj, as_string_inv_to_list s]
#align list.as_string_eq List.as_string_eq
