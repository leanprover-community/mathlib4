/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.list.modeq
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Modeq
import Mathbin.Data.List.Rotate

/-! # List rotation and modular arithmetic -/


namespace List

variable {α : Type _}

theorem nth_rotate :
    ∀ {l : List α} {n m : ℕ} (hml : m < l.length), (l.rotate n).nth m = l.nth ((m + n) % l.length)
  | [], n, m, hml => (Nat.not_lt_zero _ hml).elim
  | l, 0, m, hml => by simp [Nat.mod_eq_of_lt hml]
  | a :: l, n + 1, m, hml =>
    have h₃ : m < List.length (l ++ [a]) := by simpa using hml
    (lt_or_eq_of_le
          (Nat.le_of_lt_succ <| Nat.mod_lt (m + n) (lt_of_le_of_lt (Nat.zero_le _) hml))).elim
      (fun hml' =>
        by
        have h₁ :
          (m + (n + 1)) % (a :: l : List α).length = (m + n) % (a :: l : List α).length + 1 :=
          calc
            (m + (n + 1)) % (l.length + 1) = ((m + n) % (l.length + 1) + 1) % (l.length + 1) :=
              add_assoc m n 1 ▸ Nat.ModEq.add_right 1 (Nat.mod_mod _ _).symm
            _ = (m + n) % (l.length + 1) + 1 := Nat.mod_eq_of_lt (Nat.succ_lt_succ hml')
            
        have h₂ : (m + n) % (l ++ [a]).length < l.length := by simpa [Nat.add_one] using hml'
        rw [List.rotate_cons_succ, nth_rotate h₃, List.get?_append h₂, h₁, List.get?] <;> simp)
      fun hml' =>
      by
      have h₁ : (m + (n + 1)) % (l.length + 1) = 0 :=
        calc
          (m + (n + 1)) % (l.length + 1) = (l.length + 1) % (l.length + 1) :=
            add_assoc m n 1 ▸
              Nat.ModEq.add_right 1 (hml'.trans (Nat.mod_eq_of_lt (Nat.lt_succ_self _)).symm)
          _ = 0 := by simp
          
      rw [List.length, List.rotate_cons_succ, nth_rotate h₃, List.length_append, List.length_cons,
          List.length, zero_add, hml', h₁, List.get?_concat_length] <;>
        rfl
#align list.nth_rotate List.nth_rotate

theorem rotate_eq_self_iff_eq_repeat [hα : Nonempty α] :
    ∀ {l : List α}, (∀ n, l.rotate n = l) ↔ ∃ a, l = List.repeat a l.length
  | [] => ⟨fun h => Nonempty.elim hα fun a => ⟨a, by simp⟩, by simp⟩
  | a :: l =>
    ⟨fun h =>
      ⟨a,
        (List.ext_nthLe (by simp)) fun n hn h₁ =>
          by
          rw [← Option.some_inj, ← List.nthLe_get?]
          conv =>
            lhs
            rw [← h (List.length (a :: l) - n)]
          rw [nth_rotate hn, add_tsub_cancel_of_le (le_of_lt hn), Nat.mod_self, nth_le_repeat]
          rfl⟩,
      fun ⟨a, ha⟩ n =>
      ha.symm ▸
        List.ext_nthLe (by simp) fun m hm h =>
          by
          have hm' :
            (m + n) % (List.repeat a (List.length (a :: l))).length < List.length (a :: l) := by
            rw [List.length_repeat] <;> exact Nat.mod_lt _ (Nat.succ_pos _)
          rw [nth_le_repeat, ← Option.some_inj, ← List.nthLe_get?, nth_rotate h, List.nthLe_get?,
              nth_le_repeat] <;>
            simp_all⟩
#align list.rotate_eq_self_iff_eq_repeat List.rotate_eq_self_iff_eq_repeat

theorem rotate_repeat (a : α) (n : ℕ) (k : ℕ) : (List.repeat a n).rotate k = List.repeat a n :=
  let h : Nonempty α := ⟨a⟩
  rotate_eq_self_iff_eq_repeat.mpr ⟨a, by rw [length_repeat]⟩ k
#align list.rotate_repeat List.rotate_repeat

theorem rotate_one_eq_self_iff_eq_repeat [Nonempty α] {l : List α} :
    l.rotate 1 = l ↔ ∃ a : α, l = List.repeat a l.length :=
  ⟨fun h =>
    rotate_eq_self_iff_eq_repeat.mp fun n =>
      Nat.rec l.rotate_zero (fun n hn => by rwa [Nat.succ_eq_add_one, ← l.rotate_rotate, hn]) n,
    fun h => rotate_eq_self_iff_eq_repeat.mpr h 1⟩
#align list.rotate_one_eq_self_iff_eq_repeat List.rotate_one_eq_self_iff_eq_repeat

end List

