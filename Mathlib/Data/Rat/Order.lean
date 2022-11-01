import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring

instance : Preorder Rat where
  le               := (· ≤· )
  le_refl          := sorry
  le_trans         := sorry
  lt_iff_le_not_le := sorry

instance : PartialOrder Rat where
  le_antisymm := sorry

instance : LinearOrder Rat where
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  le_total := sorry
  decidable_le := inferInstance

instance : LinearOrderedCommRing Rat where
  add_le_add_left := sorry
  zero_le_one := sorry
  mul_pos := sorry
  le_total := sorry
  decidable_le := sorry
  exists_pair_ne := sorry
  mul_comm := sorry
  min_def := sorry
  max_def := sorry
