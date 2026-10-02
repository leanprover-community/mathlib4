import Mathlib.Tactic.DuplicateDecls

/-! Theorems-/

theorem one_add_one : 1 + 1 = 2 := rfl
theorem one_add_one' : 1 + 1 = 2 := rfl
theorem one_add_one_alias : 1 + 1 = 2 := one_add_one -- this is an alias, so it won't be flagged

theorem of_one_add_one_of_two_add_two : 1 + 1 = 2 → 2 + 2 = 4 → True := by simp
theorem of_two_add_two_of_one_add_one : 2 + 2 = 4 → 1 + 1 = 2 → True := by simp

theorem nat_int_add_comm (n : Nat) (m : Int) : n + m = m + n := by rw [Int.add_comm]
theorem int_nat_add_comm (m : Int) (n : Nat) : n + m = m + n := by rw [Int.add_comm]

theorem Eq.trans_Type {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  h₂ ▸ h₁

-- The following duplicates are not detected because of variables with the same type
theorem nat_add_comm (n m : Nat) : n + m = m + n := Nat.add_comm n m
theorem nat_add_comm' (m n : Nat) : n + m = m + n := by grind

theorem nat_le_trans (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans
theorem nat_ge_trans (a b c : Nat) : b ≤ a → c ≤ b → c ≤ a := by lia

/-! Instances -/
-- The value is not looked at, because instances are meant to be canonical.
-- We check whether a definition is an instance based on its type. We might want to change this.
@[implicit_reducible] def instAddNat' : Add Nat := ⟨Nat.sub⟩
@[implicit_reducible] def instAddNat'' : Add Nat := ⟨Nat.mul⟩

/-! Definitions -/

-- For definitions that are not instances, we look at both the type and the value.
def addTen (n : Nat) := n + 10
def addTen' (n : Nat) := n + 10
def addTwenty (n : Nat) := n + 20
