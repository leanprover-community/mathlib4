import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Min
import Mathlib.Order.Basic

namespace Fintype

def chooseMinOfCardPos {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (h : 0 < Fintype.card α) : α :=
  Finset.min' Finset.univ ((Fintype.card_pos_iff).1 h)

@[simp]
theorem chooseMinOfCardPos_eq_min {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (h : 0 < Fintype.card α) :
    chooseMinOfCardPos h = Finset.min' Finset.univ ((Fintype.card_pos_iff).1 h) :=
rfl

end Fintype
