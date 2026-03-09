module

import MathlibTest.UnusedInstancesInType.Basic

set_option linter.unusedDecidableInType true

section unused

/--
warning: `foo` does not use the following hypothesis in its type:
  • [DecidableEq α] (#2)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem foo {α} [DecidableEq α] : True := True.intro

def Foo (α) [DecidableEq α] := Unit

#guard_msgs in
theorem bar {α} [DecidableEq α] (s : Foo α) : s = s := rfl

/--
warning: `foo₂` does not use the following hypothesis in its type:
  • [(α : Type) → Decidable (Nonempty α)] (#2)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem foo₂ (a : Type) [∀ α : Type, Decidable (Nonempty α)] (_ : Unit) [Nonempty a] : True :=
  trivial

/--
warning: `foo₃` does not use the following hypotheses in its type:
  • [(α : Type) → Decidable (Nonempty α)] (#2)
  • [DecidableEq β] (#3)

Consider removing these hypotheses and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem foo₃ {β} [∀ α : Type, Decidable (Nonempty α)] [DecidableEq β] : True := trivial

-- See through `let`, don't count it as an index
/--
warning: `foo₄` does not use the following hypothesis in its type:
  • [DecidableEq β] (#2)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem foo₄ {β} : let _ := 2; ∀ [DecidableEq β], True := trivial

-- Linter should not fire when `sorry` appears in the type, even though the instances are unused
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem fooSorry {β} [∀ α : Type, Decidable (Nonempty α)] [DecidableEq β] (b : sorry) : True :=
  trivial

end unused

section used

/- The linter either should not fire on these declarations because the instance hypotheses are used
in the type, or not fire on *every* instance in these declarations. -/

theorem fooUsing [DecidableEq (Nat → Nat)] : UsesInstanceOf (DecidableEq (Nat → Nat)) := trivial

theorem fooUsing₁ [DecidableEq (Nat → Nat)] : UsesInstanceOf (DecidableEq (Nat → Nat)) → True :=
  fun _ => trivial

/--
warning: `fooUsing₁'` does not use the following hypothesis in its type outside of proofs:
  • [DecidableEq (Nat → Nat)] (#1) (used in type, but only in a proof)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem fooUsing₁' [DecidableEq (Nat → Nat)] :
    UsesExactly (UsesInstanceInProof (DecidableEq (Nat → Nat))) → True :=
  fun _ => trivial

/--
warning: `fooUsing₁''` does not use the following hypothesis in its type outside of proofs:
  • [DecidableEq (Nat → Nat)] (#1) (used in type, but only in a proof)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem fooUsing₁'' [DecidableEq (Nat → Nat)]
    (_ : True := UsesInstanceInProof (DecidableEq (Nat → Nat)) (by infer_instance)) : True :=
  trivial

-- Should fire on parameter #1 but not parameter #2
/--
warning: `fooUsing₂` does not use the following hypothesis in its type:
  • [DecidablePred Nonempty] (#1)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem fooUsing₂ [DecidablePred Nonempty] [DecidableEq (Nat → Nat)] :
    UsesInstanceOf (DecidableEq (Nat → Nat)) → True :=
  fun _ => trivial

-- Note `optParam` test
theorem fooUsing₃ [DecidablePred Nonempty] [DecidableEq (Nat → Nat)]
    (_ : UsesInstanceOf (DecidablePred Nonempty) := trivial) :
    UsesInstanceOf (DecidableEq (Nat → Nat)) → True :=
  fun _ => trivial

end used

section setOptionIn

/-! Test workaround for lean4#11313 -/

set_option linter.unusedDecidableInType false in
theorem fooUsing₂' [DecidablePred Nonempty] [DecidableEq (Nat → Nat)] :
    UsesInstanceOf (DecidableEq (Nat → Nat)) → True :=
  fun _ => trivial

set_option linter.unusedDecidableInType false

/--
warning: `fooUsing₂''` does not use the following hypothesis in its type:
  • [DecidablePred Nonempty] (#1)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
set_option linter.unusedDecidableInType true in
theorem fooUsing₂'' [DecidablePred Nonempty] [DecidableEq (Nat → Nat)] :
    UsesInstanceOf (DecidableEq (Nat → Nat)) → True :=
  fun _ => trivial

end setOptionIn
