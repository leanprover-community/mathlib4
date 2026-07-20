import Mathlib.Tactic.Simps.Basic

set_option linter.tacticCheckInstances true

/-! ## clean projection, no warning expected -/

structure Wrap (α : Type) where
  carrier : List α

#guard_msgs in
@[simps]
def mkWrap (s : List Nat) : Wrap Nat := { carrier := s }

/-! a semireducible alias `.implicit`-ill-typed equation. -/

structure Fn where
  toFun : Nat → Nat

def MyFn : Type := Fn

/--
warning: generated lemma idFn_toFun is not type-correct at `.implicit` transparency; consider marking some of the following as `@[implicit_reducible]`:
  MyFn

Note: This linter can be disabled with `set_option linter.tacticCheckInstances false`
-/
#guard_msgs in
@[simps]
def idFn : MyFn := ({ toFun := id } : Fn)

/-! marking the offender `@[implicit_reducible]` silences the warning -/

set_option allowUnsafeReducibility true
attribute [implicit_reducible] MyFn

#guard_msgs in
@[simps]
def idFn2 : MyFn := ({ toFun := id } : Fn)
