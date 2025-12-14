import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Basic
import Mathlib.Tactic

/-! ### Interaction with DenselyOrdered -/

section DenselyOrdered

variable {α : Type*} [LinearOrder α]

/-- A preorder cannot be both densely ordered and locally finite,
unless it is trivial (all elements are equal). -/
theorem not_locallyFiniteOrder [DenselyOrdered α] [LocallyFiniteOrder α] :
    Subsingleton α := by
  rw [← not_nontrivial_iff_subsingleton]
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  rcases lt_trichotomy x y with h | h | h
  · exact not_lt_of_denselyOrdered_of_locallyFinite x y h
  · contradiction
  · exact not_lt_of_denselyOrdered_of_locallyFinite y x h

/-- A nontrivial densely ordered preorder is not locally finite. -/
theorem not_locallyFiniteOrder_of_nontrivial [DenselyOrdered α] [Nontrivial α] :
    IsEmpty (LocallyFiniteOrder α) := by
  constructor
  intro h_lfo
  have : Subsingleton α := not_locallyFiniteOrder
  exact not_nontrivial_iff_subsingleton.mpr this ‹Nontrivial α›

end DenselyOrdered
