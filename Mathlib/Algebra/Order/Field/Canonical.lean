import Mathlib.Algebra.Order.Ring.Defs

/-!
# Canonically ordered semifields
-/

@[expose] public section

variable {α : Type*} [Semifield α] [LinearOrder α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/-- Construct a `LinearOrderedCommGroupWithZero` from a canonically linear ordered semifield. -/
abbrev CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero α where
  bot := 0
  bot_le := zero_le
  zero_le := zero_le
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    have : PosMulStrictMono α := PosMulReflectLT.toPosMulStrictMono _
    mul_lt_mul_of_pos_left hbc ha

variable [IsStrictOrderedRing α] [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
