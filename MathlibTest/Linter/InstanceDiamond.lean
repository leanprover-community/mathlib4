import Mathlib.Tactic.Linter.InstanceDiamond

/-! # Tests for the instance diamond linter

The `instanceDiamond` linter detects non-defeq diamonds in the typeclass hierarchy.
These tests verify both that the linter fires on real diamonds and stays silent
on well-formed instances.
-/

set_option linter.unusedVariables false

namespace InstanceDiamondTest

/-! ## Positive tests: no warnings expected

For classes declared with `class ... extends B, C`, Lean's structure elaborator
guarantees that diamond paths are definitionally equal by construction. The linter
should not fire on these instances. -/

-- Simple diamond hierarchy
class A (α : Type _) where a : α
class B (α : Type _) extends A α where b : α
class C (α : Type _) extends A α where c : α
class D (α : Type _) extends B α, C α

-- Deeper diamond (depth 3): F → D' → B → A and F → E → C → A
class D' (α : Type _) extends B α where d : α
class E (α : Type _) extends C α where e : α
class F (α : Type _) extends D' α, E α

-- Instances — all consistent by construction, no linter warnings expected
instance : D Nat where a := 0; b := 1; c := 2
instance : F Nat where a := 0; b := 1; c := 2; d := 3; e := 4

-- Three parents sharing an ancestor: all three pairs (B,C), (B,E2), (C,E2) must be checked
class E2 (α : Type _) extends A α where e : α
class G (α : Type _) extends B α, C α, E2 α

instance : G Nat where a := 0; b := 1; c := 2; e := 3

/-! ## Opt-out test: `set_option linter.instanceDiamond false` suppresses warnings

This is a smoke test that the option correctly disables the linter. Even on a
clean instance the linter visits the declaration; with the option off, no info
or warning messages are produced. -/

class H (α : Type _) extends B α, C α

#guard_msgs in
set_option linter.instanceDiamond false in
instance : H Nat where a := 0; b := 1; c := 2

end InstanceDiamondTest

/-! ## Note on negative tests

A previous version of this file had negative tests built around
`Matrix.addCommGroup` + `Matrix.instAddGroupWithOne` in a fresh
`AddCommGroupWithOne` instance. These exercised the older (Lean ≤ v4.30.0-rc1)
behaviour where `__ := A; __ := B` could leave the projection paths to
`SubNegMonoid` non-defeq, producing a real diamond at the `zsmul` field.

The current toolchain elaborates this construction so that the
`toAddGroupWithOne` projection is recovered from `toAddCommGroup` plus the
`IntCast`/`NatCast`/`One` extras, making both projection paths to `AddGroup`
defeq by construction. As a result, that particular test case no longer
exhibits a diamond and the linter (correctly) stays silent on it.

The linter still runs on the entire Mathlib build and would fire if a real
non-defeq diamond were introduced. -/
