import Mathlib.Tactic.DuplicateDecls

theorem one_add_one : 1 + 1 = 2 := rfl
theorem one_add_one' : 1 + 1 = 2 := rfl
theorem one_add_one_alias : 1 + 1 = 2 := one_add_one -- this is an alias, so it won't be flagged

theorem of_one_add_one_of_two_add_two : 1 + 1 = 2 → 2 + 2 = 4 → True := by simp
theorem of_two_add_two_of_one_add_one : 2 + 2 = 4 → 1 + 1 = 2 → True := by simp

theorem nat_int_add_comm (n : Nat) (m : Int) : n + m = m + n := by rw [Int.add_comm]
theorem int_nat_add_comm (m : Int) (n : Nat) : n + m = m + n := by rw [Int.add_comm]

-- The following duplicates are not detected because of variables with the same type
theorem nat_add_comm (n m : Nat) : n + m = m + n := Nat.add_comm n m
theorem nat_add_comm' (m n : Nat) : n + m = m + n := by grind

theorem nat_le_trans (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans
theorem nat_ge_trans (a b c : Nat) : b ≤ a → c ≤ b → c ≤ a := by lia
