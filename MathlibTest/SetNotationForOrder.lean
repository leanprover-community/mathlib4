module

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.SetNotationForOrder

attribute [use_set_notation_for_order] Set

section Delab

-- `LE.le` is printed as `≤` or `⊆` depending on the type.

/-- info: a ⊆ b : Prop -/
#guard_msgs in
variable (a b : Set Nat) in
#check LE.le a b

/-- info: a ≤ b : Prop -/
#guard_msgs in
variable (a b : Nat) in
#check LE.le a b

/-- info: a ⊂ b : Prop -/
#guard_msgs in
variable (a b : Set Nat) in
#check LT.lt a b

/-- info: a < b : Prop -/
#guard_msgs in
variable (a b : Nat) in
#check LT.lt a b

/-- info: a ⊇ b : Prop -/
#guard_msgs in
variable (a b : Set Nat) in
#check GE.ge a b

/-- info: a ≥ b : Prop -/
#guard_msgs in
variable (a b : Nat) in
#check GE.ge a b

/-- info: a ⊃ b : Prop -/
#guard_msgs in
variable (a b : Set Nat) in
#check GT.gt a b

/-- info: a > b : Prop -/
#guard_msgs in
variable (a b : Nat) in
#check GT.gt a b

end Delab

section Elab

set_option pp.notation false -- So we can see the difference between `LE.le` and `Subset`.

-- `⊆` is elaborated to `LE.le` or `Subset` depending on the type.

/-- info: LE.le a b : Prop -/
#guard_msgs in
variable (a b : Set Nat) in
#check a ⊆ b

/-- info: Subset a b : Prop -/
#guard_msgs in
variable (a b : List Nat) in
#check a ⊆ b

/-- info: LT.lt a b : Prop -/
#guard_msgs in
variable (a b : Set Nat) in
#check a ⊂ b

/-- info: GE.ge a b : Prop -/
#guard_msgs in
variable (a b : Set Nat) in
#check a ⊇ b

/-- info: Superset a b : Prop -/
#guard_msgs in
variable (a b : List Nat) in
#check a ⊇ b

/-- info: GT.gt a b : Prop -/
#guard_msgs in
variable (a b : Set Nat) in
#check a ⊃ b


-- `⊆` is not elaborated to `LE.le` even if that is the only valid relation on this type
variable (a b : Nat) in
/--
error: failed to synthesize instance of type class
  HasSubset Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check a ⊆ b

/-
Sometimes, the type in the relation is not known at first.
In that case, elaboration is postponed until the type is known.
This is demonstrated in the following examples, where `t ⊆ s` is at fist elaborated
without knowing the types of `s` and `t`.
The type of `t` is later inferred when elaborating `p t`.
Using that information, `t ⊆ s` can be elaborated correctly.
-/

/-- info: ∀ (s : Set Nat), Exists fun t => And (LE.le t s) (p t) : Prop -/
#guard_msgs in
variable (p : Set Nat → Prop) in
#check ∀ s, ∃ t ⊆ s, p t

/-- info: ∀ (s : List Nat), Exists fun t => And (Subset t s) (p t) : Prop -/
#guard_msgs in
variable (p : List Nat → Prop) in
#check ∀ s, ∃ t ⊆ s, p t

/-!
These tests show something that used to be possible, but does not work anymore:
If you write `_ ⊆ _`, the type cannot be inferred, and hence, elaboration of this term
is either postposed, or it elaborates to `Subset _ _`.
-/
example (a b : Set Nat) : True ∨ True ∨ a ⊆ b := by
  -- `simp_rw` fails, because `_ ⊆ _` elaborates to `Subset _ _`
  fail_if_success simp_rw [or_comm (b := _ ⊆ _)]
  -- `rw` fails, because elaboration of `_ ⊆ _` has been delayed.
  fail_if_success rw [or_comm (b := _ ⊆ _)]
  -- We need to use `≤` to do the rewrite.
  rw [or_comm (b := _ ≤ _)]
  left; trivial

example (a b : List Nat) : True ∨ True ∨ a ⊆ b := by
  -- `rw` fails, because elaboration of `_ ⊆ _` has been delayed.
  fail_if_success rw [or_comm (b := _ ⊆ _)]
  -- `simp_rw` succeeds, because `simp` forces the simp lemma to be fully elaborated.
  simp_rw [or_comm (b := _ ⊆ _)]
  left; trivial

end Elab
