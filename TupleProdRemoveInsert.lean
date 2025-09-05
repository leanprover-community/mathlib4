import Mathlib

open Fin
open Finset
open List

variable [CommMonoid M]

namespace Fin

#check cons
#check snoc

#check prod_cons

#check Fin.induction

theorem exists_cons (p : Fin (n + 1) → M) : ∃ h t, p = cons h t := by
  sorry

theorem insertNth_succ_cons : (insertNth i.succ x (cons hd tl) : Fin (n + 2) → M) = cons hd (insertNth i x tl) := by
  --exact?
  sorry

theorem insertNth_succ_cons' : (insertNth ⟨i + 1, h⟩ x (cons hd tl) : Fin (n + 2) → M) = cons hd (insertNth ⟨i, i_lt⟩ x tl) := by
  sorry

@[to_additive (attr := simp), simp]
theorem prod_insertNth (p : Fin n → M) : ∏ j, insertNth i x p j = x * ∏ j, p j :=
  go_prod n i.val i.isLt p
where
  --@[to_additive]
  go_prod : ∀ n i (h : i < n + 1) (p : Fin n → M), ∏ j, insertNth ⟨i, h⟩ x p j = x * ∏ j, p j
  | n, 0, h, p => by simp only [zero_eta, insertNth_zero', prod_cons]
  | 0, i, h, p => by
    set i : Fin 1 := ⟨i, h⟩
    simp [show p = ![] from Subsingleton.elim _ _]
    --simp [show p = elim0 from Subsingleton.elim _ _]
    have : insertNth i x ![] = ![x] := by
    --have : i.insertNth x ![] elim0 = ![x] := by
      have : i = 0 := by exact fin_one_eq_zero i
      simp [this]
      rfl
    simp [this]
  | n + 1, i + 1, h, p => by
    obtain ⟨hd, tl, rfl⟩ := exists_cons p
    simp
    have i_lt := Nat.lt_of_succ_lt_succ h
    --let insert_tl : Fin (n + 1) → M := insertNth ⟨i, i_lt⟩ x tl
    have : ∏ j, insertNth ⟨i + 1, h⟩ x (cons hd tl) j = hd * ∏ j, insertNth ⟨i, i_lt⟩ x tl j := by
      have := insertNth_succ_cons' (n := n) (i := i) (h := h) (x := x) (hd := hd) (tl := tl) (i_lt := i_lt)
      simp [this]
    simp [this]
    have ih := go_prod n i i_lt tl
    rw [ih]
    exact mul_left_comm hd x (∏ j, tl j)

end Fin

namespace List

#check prod_cons

@[to_additive (attr := simp), simp]
theorem prod_insertIdx {l : List M} (h : i ≤ l.length) : (l.insertIdx i a).prod = a * l.prod := by
  induction i generalizing l
  case zero => rfl
  case succ i ih =>
    obtain ⟨hd, tl, rfl⟩ := exists_cons_of_length_pos (Nat.zero_lt_of_lt h)
    simp [ih (Nat.le_of_lt_succ h), mul_left_comm]

end List
namespace List.Vector

section MulOne

variable {M} [Mul M] [One M]

theorem prod_cons {v : List.Vector M n} : (cons a v).toList.prod = a * v.toList.prod := rfl

end MulOne

@[to_additive (attr := simp), simp]
theorem prod_insertIdx {v : List.Vector M n} : (v.insertIdx a i).toList.prod = a * v.toList.prod := by
  apply List.prod_insertIdx
  rw [length_val]
  exact is_le i

end List.Vector
