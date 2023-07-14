import Mathlib

instance Prod.orderedSub
    [Preorder α] [Add α] [Sub α] [OrderedSub α] [Sub β] [Preorder β] [Add β] [OrderedSub β] :
    OrderedSub (α × β) where
  tsub_le_iff_right _ _ _ :=
  ⟨fun w ↦ ⟨tsub_le_iff_right.mp w.1, tsub_le_iff_right.mp w.2⟩,
   fun w ↦ ⟨tsub_le_iff_right.mpr w.1, tsub_le_iff_right.mpr w.2⟩⟩

instance Pi.orderedSub {ι : Type _} {α : ι → Type _}
    [∀ i, Preorder (α i)] [∀ i, Add (α i)] [∀ i, Sub (α i)] [∀ i, OrderedSub (α i)] :
    OrderedSub ((i : ι) → α i) where
  tsub_le_iff_right _ _ _ :=
  ⟨fun w i ↦ tsub_le_iff_right.mp (w i),
   fun w i ↦ tsub_le_iff_right.mpr (w i)⟩

example : OrderedSub (ℕ × ℕ) := inferInstance
open scoped NNReal in
example : OrderedSub (ℕ × ℝ≥0) := inferInstance
example : OrderedSub ((n : ℕ) → (m : Fin n) → ℕ) := inferInstance

theorem tsub_lt_tsub_left
    [AddCommMonoid α] [PartialOrder α] [Sub α] [OrderedSub α] [ExistsAddOfLE α]
    [CovariantClass α α ((· : α) + ·) (· ≤ · )] [ContravariantClass α α ((· : α) + ·) (· ≤ · )]
    [CovariantClass α α ((· : α) + ·) (· < · )] [ContravariantClass α α ((· : α) + ·) (· < · )]
    {a b c : α} (w : c < b) (h : b ≤ a) : a - b < a - c := by
  rw [tsub_lt_iff_right h]
  obtain ⟨d, rfl⟩ := exists_add_of_le w.le
  rw [←add_assoc]
  rw [tsub_add_cancel_of_le (lt_of_lt_of_le w h).le]
  exact lt_add_of_pos_right a (pos_of_lt_add_right w)

example {a b c : ℕ} (w : c < b) (h : b ≤ a) : a - b < a - c := tsub_lt_tsub_left w h
open scoped NNReal in
example {a b c : ℕ × ℝ≥0} (w : c < b) (h : b ≤ a) : a - b < a - c := tsub_lt_tsub_left w h
