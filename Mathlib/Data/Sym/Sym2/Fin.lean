/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Choose.Bounds

private def chooseTwoInv (x) := (Nat.sqrt (8 * x + 1) - 1) / 2
theorem choose_two_le (x) : (chooseTwoInv x + 1).choose 2 ≤ x := by
  sorry


@[simps!]
def nonemptyIntervalFinEquiv {n} :
    NonemptyInterval (Fin n) ≃o Fin ((n + 1).choose 2) where
  toFun x := ⟨((x.1.2 + 1 : Nat).choose 2 + x.1.1 : ℕ), sorry⟩
  invFun x :=
    have hy : chooseTwoInv _ < _ := sorry
    ⟨(⟨x.1 - (chooseTwoInv x.1 + 1).choose 2, by
      apply Nat.sub_lt_left_of_lt_add
      · apply choose_two_le
      refine x.prop.trans_le ?_
      simp [Nat.choose_two_right]
      apply Nat.div_le_of_le_mul
      sorry⟩, ⟨chooseTwoInv _, hy⟩), sorry⟩
  left_inv
  | ⟨(a, b), p⟩ => by
    ext <;> dsimp
    · sorry
    · sorry
  right_inv x := by
    ext
    refine Nat.add_sub_of_le (choose_two_le _)
  map_rel_iff' {m n} := by
    sorry

/-- The numbering of the elements of `Sym2 (Fin n)` in lexicographic order. -/
@[simps!]
def Sym2.equivFin {n} : Sym2 (Fin n) ≃ Fin ((n + 1).choose 2) :=
  Sym2.sortEquiv.trans nonemptyIntervalFinEquiv.toEquiv

open Sym2

#eval! [s(0,0), s(0,1), s(1,1), s(0,2), s(1,2), s(2,2)].map (equivFin (n := 3) )
#guard ∀ i : Fin _, equivFin (equivFin (n := 50).symm i) = i
