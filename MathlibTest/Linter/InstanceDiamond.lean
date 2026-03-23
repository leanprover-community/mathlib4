import Mathlib.Tactic.Linter.InstanceDiamond
import Mathlib.Data.Matrix.Diagonal

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

/-! ## Negative tests: diamonds from combining separately-defined instances

The linter detects non-defeq diamonds when an instance is built by combining
separately-defined parent instances via `__ :=` syntax. This occurs because
the non-first-parent projection (e.g. `AddCommGroupWithOne.toAddGroupWithOne`)
produces a structurally different expression than the first-parent path
at `reducible_and_instances` transparency.

The root-cause filter means only the most primitive failing ancestor is reported.
For the `AddCommGroupWithOne` diamond, the root cause is `SubNegMonoid` (specifically
the `zsmul` field), not the higher-level `AddGroup`.

We use a type synonym `M` to create a fresh instance declaration that triggers the
linter, using the same underlying `Matrix.addCommGroup` and `Matrix.instAddGroupWithOne`
instances that cause the diamond in the real Mathlib hierarchy. -/

abbrev M (n : Type*) (α : Type*) := Matrix n n α

/--
warning: instance diamond at SubNegMonoid:
  the projection chains [AddCommGroupWithOne.toAddCommGroup,
 AddCommGroup.toAddGroup,
 AddGroup.toSubNegMonoid] and [AddCommGroupWithOne.toAddGroupWithOne,
 AddGroupWithOne.toAddGroup,
 AddGroup.toSubNegMonoid]
  produce results which are not definitionally equal
  at `with_reducible_and_instances` transparency.
  Differing fields:
    zsmul:
      lhs: { toSubNegMonoid := Pi.subNegMonoid, neg_add_cancel := ⋯ }
      rhs: { toAddMonoid := instACGWO_test.toAddGroupWithOne.toAddMonoid,
  toNeg := instACGWO_test.toAddGroupWithOne.toNeg, toSub := instACGWO_test.toAddGroupWithOne.toSub, sub_eq_add_neg := ⋯,
  zsmul := AddGroupWithOne.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯ }
example {n : Type u_1} {α : Type u_2} [inst : DecidableEq n] [inst : AddCommGroupWithOne α] :
    (instACGWO_test : AddCommGroupWithOne (M n α)).toAddCommGroup.toAddGroup.toSubNegMonoid =
    (instACGWO_test : AddCommGroupWithOne (M n α)).toAddGroupWithOne.toAddGroup.toSubNegMonoid := by
  with_reducible_and_instances rfl

Note: This linter can be disabled with `set_option linter.instanceDiamond false`
-/
#guard_msgs (warning, drop info) in
noncomputable instance instACGWO_test
    {n : Type*} {α : Type*} [DecidableEq n] [AddCommGroupWithOne α] :
    AddCommGroupWithOne (M n α) where
  __ := Matrix.addCommGroup
  __ := Matrix.instAddGroupWithOne

-- Verify the linter's example: the statement type-checks but rfl fails (the diamond is real)
/--
error: Tactic `rfl` failed: The left-hand side
  @AddGroup.toSubNegMonoid (M n α) instACGWO_test.toAddGroup
is not definitionally equal to the right-hand side
  @AddGroup.toSubNegMonoid (M n α) instACGWO_test.toAddGroupWithOne.toAddGroup

n : Type u_1
α : Type u_2
inst✝ : DecidableEq n
inst : AddCommGroupWithOne α
⊢ instACGWO_test.toSubNegMonoid = instACGWO_test.toAddGroupWithOne.toAddGroup.toSubNegMonoid
-/
#guard_msgs (error) in
example {n : Type u_1} {α : Type u_2} [inst : DecidableEq n] [inst : AddCommGroupWithOne α] :
    (instACGWO_test : AddCommGroupWithOne (M n α)).toAddCommGroup.toAddGroup.toSubNegMonoid =
    (instACGWO_test : AddCommGroupWithOne (M n α)).toAddGroupWithOne.toAddGroup.toSubNegMonoid := by
  with_reducible_and_instances rfl

/-! ## Opt-out test: `set_option linter.instanceDiamond false` suppresses warnings -/

#guard_msgs in
set_option linter.instanceDiamond false in
noncomputable instance instACGWO_silent
    {n : Type*} {α : Type*} [DecidableEq n] [AddCommGroupWithOne α] :
    AddCommGroupWithOne (M n α) where
  __ := Matrix.addCommGroup
  __ := Matrix.instAddGroupWithOne

end InstanceDiamondTest
