import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Testing for the `gcongr` tactic
-/

namespace GCongrTests

/-
Test that `gcongr` lemmas are applied in the `reducible` transparency by default.
Previously, `DFunLike.coe` would be unfolded when applying a `@[gcongr]` lemma.
-/
section transparency
open MeasureTheory

variable {α : Type*} (a : Set α) {μ : OuterMeasure α} {μ' : OuterMeasure α}

@[gcongr high] lemma mono_outerMeasure (h : μ ≤ μ') : μ a ≤ μ' a := h a
example (h : μ ≤ μ') : μ a ≤ μ' a := by gcongr

variable [MeasurableSpace α] {ν : Measure α} {ν' : Measure α}

@[gcongr] lemma mono_measure (h : ν ≤ ν') : ν a ≤ ν' a := h a
example (h : ν ≤ ν') : ν a ≤ ν' a := by gcongr

end transparency

/-
Test that a more general `@[gcongr]` lemma always applies, and the resulting reflexive goals
are closed with `rfl`.
-/
section rfl

axiom myAdd : Nat → Nat → Nat

axiom rel : Nat → Nat → Prop

local infix:50 "~" => rel

variable {a b c d : Nat}

@[gcongr] axiom myAdd_mono : a ~ c → b ~ d → myAdd a b ~ myAdd c d

axiom myAdd_rfl : a ~ a

/--
error: unsolved goals
case a
a b c d : ℕ
h : b~d
⊢ a~a

case a.a
a b c d : ℕ
h : b~d
⊢ c~c
-/
#guard_msgs in
example (h : b ~ d) : myAdd a (myAdd b c) ~ myAdd a (myAdd d c) := by
  gcongr

/--
error: tactic 'gcongr' failed, subgoal a~a is not allowed by the provided pattern and is not closed by `rfl`
case a
a b c d : ℕ
h : b~d
⊢ a~a
-/
#guard_msgs in
example (h : b ~ d) : myAdd a (myAdd b c) ~ myAdd a (myAdd d c) := by
  gcongr myAdd _ (myAdd ?_ _)

attribute [refl] myAdd_rfl

example (h : b ~ d) : myAdd a (myAdd b c) ~ myAdd a (myAdd d c) := by
  gcongr

example (h : b ~ d) : myAdd a (myAdd b c) ~ myAdd a (myAdd d c) := by
  gcongr myAdd _ (myAdd ?_ _)

end rfl

end GCongrTests
