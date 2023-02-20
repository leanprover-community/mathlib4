/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.string.basic
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Lex
import Mathbin.Data.Char

/-!
# Strings

Supplementary theorems about the `string` type.
-/


namespace String

/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
def ltb : Iterator → Iterator → Bool
  | s₁, s₂ => by
    cases s₂.has_next; · exact ff
    cases h₁ : s₁.has_next; · exact tt
    exact
      if s₁.curr = s₂.curr then
        have : s₁.next.2.length < s₁.2.length :=
          match s₁, h₁ with
          | ⟨_, a :: l⟩, h => Nat.lt_succ_self _
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr termination_by'
  ⟨_, measure_wf fun s => s.1.2.length⟩
#align string.ltb String.ltb

instance hasLt' : LT String :=
  ⟨fun s₁ s₂ => ltb s₁.mkIterator s₂.mkIterator⟩
#align string.has_lt' String.hasLt'

instance decidableLt : @DecidableRel String (· < ·) := by infer_instance
#align string.decidable_lt String.decidableLt

-- short-circuit type class inference
@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList
  | ⟨i₁⟩, ⟨i₂⟩ =>
    by
    suffices ∀ {p₁ p₂ s₁ s₂}, ltb ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ ↔ s₁ < s₂ from this
    intros
    induction' s₁ with a s₁ IH generalizing p₁ p₂ s₂ <;> cases' s₂ with b s₂ <;> rw [ltb] <;>
      simp [iterator.has_next]
    · rfl
    · exact iff_of_true rfl List.Lex.nil
    · exact iff_of_false Bool.false_ne_true (not_lt_of_lt List.Lex.nil)
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

instance decidableLe : @DecidableRel String (· ≤ ·) := by infer_instance
#align string.decidable_le String.decidableLe

-- short-circuit type class inference
@[simp]
theorem le_iff_toList_le {s₁ s₂ : String} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList :=
  (not_congr lt_iff_toList_lt).trans not_lt
#align string.le_iff_to_list_le String.le_iff_toList_le

theorem toList_inj : ∀ {s₁ s₂}, toList s₁ = toList s₂ ↔ s₁ = s₂
  | ⟨s₁⟩, ⟨s₂⟩ => ⟨congr_arg _, congr_arg _⟩
#align string.to_list_inj String.toList_inj

theorem nil_asString_eq_empty : [].asString = "" :=
  rfl
#align string.nil_as_string_eq_empty String.nil_asString_eq_empty

@[simp]
theorem toList_empty : "".toList = [] :=
  rfl
#align string.to_list_empty String.toList_empty

theorem asString_inv_toList (s : String) : s.toList.asString = s :=
  by
  cases s
  rfl
#align string.as_string_inv_to_list String.asString_inv_toList

@[simp]
theorem toList_singleton (c : Char) : (String.singleton c).toList = [c] :=
  rfl
#align string.to_list_singleton String.toList_singleton

theorem toList_nonempty : ∀ {s : String}, s ≠ String.empty → s.toList = s.headI :: (s.popn 1).toList
  | ⟨s⟩, h => by cases s <;> [cases h rfl, rfl]
#align string.to_list_nonempty String.toList_nonempty

@[simp]
theorem head_empty : "".headI = default :=
  rfl
#align string.head_empty String.head_empty

@[simp]
theorem popn_empty {n : ℕ} : "".popn n = "" :=
  by
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
  le_refl a := le_iff_toList_le.2 le_rfl
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

theorem List.toList_inv_asString (l : List Char) : l.asString.toList = l :=
  by
  cases hl : l.as_string
  exact StringImp.mk.inj hl.symm
#align list.to_list_inv_as_string List.toList_inv_asString

@[simp]
theorem List.length_asString (l : List Char) : l.asString.length = l.length :=
  rfl
#align list.length_as_string List.length_asString

@[simp]
theorem List.asString_inj {l l' : List Char} : l.asString = l'.asString ↔ l = l' :=
  ⟨fun h => by rw [← List.toList_inv_asString l, ← List.toList_inv_asString l', to_list_inj, h],
    fun h => h ▸ rfl⟩
#align list.as_string_inj List.asString_inj

@[simp]
theorem String.length_toList (s : String) : s.toList.length = s.length := by
  rw [← String.asString_inv_toList s, List.toList_inv_asString, List.length_asString]
#align string.length_to_list String.length_toList

theorem List.asString_eq {l : List Char} {s : String} : l.asString = s ↔ l = s.toList := by
  rw [← as_string_inv_to_list s, List.asString_inj, as_string_inv_to_list s]
#align list.as_string_eq List.asString_eq

