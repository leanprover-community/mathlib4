/-
Copyright (c) 2021 Johan Commelin.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Kevin Buzzard

! This file was ported from Lean 3 source module linear_order_with_pos_mul_pos_eq_zero
! leanprover-community/mathlib commit 328375597f2c0dd00522d9c2e5a33b6a6128feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.WithZero.Defs

/-!
An example of a `linear_ordered_comm_monoid_with_zero` in which the product of two positive
elements vanishes.

This is the monoid with 3 elements `0, ε, 1` where `ε ^ 2 = 0` and everything else is forced.
The order is `0 < ε < 1`.  Since `ε ^ 2 = 0`, the product of strictly positive elements can vanish.

Relevant Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/mul_pos
-/


namespace Counterexample

/-- The three element monoid. -/
inductive Foo
  | zero
  | eps
  | one
  deriving DecidableEq
#align counterexample.foo Counterexample.Foo

namespace Foo

instance inhabited : Inhabited Foo :=
  ⟨zero⟩
#align counterexample.foo.inhabited Counterexample.Foo.inhabited

instance : Zero Foo :=
  ⟨zero⟩

instance : One Foo :=
  ⟨one⟩

local notation "ε" => eps

/-- The order on `foo` is the one induced by the natural order on the image of `aux1`. -/
def aux1 : Foo → ℕ
  | 0 => 0
  | ε => 1
  | 1 => 2
#align counterexample.foo.aux1 Counterexample.Foo.aux1

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
/-- A tactic to prove facts by cases. -/
unsafe def boom : tactic Unit :=
  sorry
#align counterexample.foo.boom counterexample.foo.boom

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
theorem aux1_inj : Function.Injective aux1 := by
  run_tac
    boom
#align counterexample.foo.aux1_inj Counterexample.Foo.aux1_inj

instance : LinearOrder Foo :=
  LinearOrder.lift' aux1 aux1_inj

/-- Multiplication on `foo`: the only external input is that `ε ^ 2 = 0`. -/
def mul : Foo → Foo → Foo
  | 1, x => x
  | x, 1 => x
  | _, _ => 0
#align counterexample.foo.mul Counterexample.Foo.mul

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
instance : CommMonoid Foo where
  mul := mul
  one := 1
  one_mul := by
    run_tac
      boom
  mul_one := by
    run_tac
      boom
  mul_comm := by
    run_tac
      boom
  mul_assoc := by
    run_tac
      boom

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
instance : LinearOrderedCommMonoidWithZero Foo :=
  { Foo.linearOrder, Foo.commMonoid with
    zero := 0
    zero_mul := by
      run_tac
        boom
    mul_zero := by
      run_tac
        boom
    mul_le_mul_left := by rintro ⟨⟩ ⟨⟩ h ⟨⟩ <;> revert h <;> decide
    zero_le_one := by decide }

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
theorem not_mul_pos :
    ¬∀ {M : Type} [LinearOrderedCommMonoidWithZero M],
        ∀ (a b : M) (ha : 0 < a) (hb : 0 < b), 0 < a * b := by
  intro h
  specialize
    h ε ε
      (by
        run_tac
          boom)
      (by
        run_tac
          boom)
  exact
    (lt_irrefl 0
        (h.trans_le
          (by
            run_tac
              boom))).elim
#align counterexample.foo.not_mul_pos Counterexample.Foo.not_mul_pos

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic counterexample.foo.boom -/
example : 0 < ε ∧ ε * ε = 0 := by
  run_tac
    boom

end Foo

end Counterexample

