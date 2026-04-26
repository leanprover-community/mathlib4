import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Nonempty

namespace Fintype

/-- Choose an element of a finite type with nonzero cardinality. -/
noncomputable def chooseOfCardNeZero (α : Type*) [Fintype α]
    (h : Fintype.card α ≠ 0) : α := by
  classical
  have h' : 0 < Fintype.card α := Nat.pos_iff_ne_zero.mpr h
  have : Nonempty α := (Fintype.card_pos_iff).1 h'
  exact Classical.choice this

end Fintype
