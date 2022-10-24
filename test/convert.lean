import Mathlib.Tactic.Convert
import Std.Tactic.GuardExpr

example (P : Prop) (h : P) : P := by convert h

example (α β : Type) (h : α = β) (b : β) : α := by
  convert b

example (α β : Type) (h : ∀ α β : Type, α = β) (b : β) : α := by
  convert b
  apply h

example (α β : Type) (h : α = β) (b : β) : Nat × α := by
  convert (37, b)

example (α β : Type) (h : β = α) (b : β) : Nat × α := by
  convert ← (37, b)

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b)

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b) using 2
  guard_target == (Nat × α) = (Nat × β)
  congr

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b) using 3

-- TODO when `data.set.basic` has been ported, restore these tests from mathlib3

-- open set

-- variables {α β : Type}
-- @[simp] lemma singleton_inter_singleton_eq_empty {x y : α} :
--   ({x} ∩ {y} = (∅ : set α)) ↔ x ≠ y :=
-- by simp [singleton_inter_eq_empty]

-- example {f : β → α} {x y : α} (h : x ≠ y) : f ⁻¹' {x} ∩ f ⁻¹' {y} = ∅ :=
-- begin
--   have : {x} ∩ {y} = (∅ : set α) := by simpa using h,
--   convert preimage_empty,
--   rw [←preimage_inter,this],
-- end
