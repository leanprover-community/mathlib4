import Mathlib.GroupTheory.Coset
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Data.Fintype.Powerset

variable {T : Type*} [Fintype T]

example : Fintype.card {t : Finset T // t.card = 1} = Fintype.card T := by
  simp only [Fintype.card_finset_len, Nat.choose_one_right]
