import Mathlib.Init
import Mathlib.Data.Fintype.Defs

def Uses (α : Sort u) (_ : α := by infer_instance) : Prop := True

set_option linter.mathlibStandardSet true

section decidable

section unused

/--
warning: `foo` has the hypothesis:
  • [DecidableEq α] (#2)
which is not used in the remainder of the type.

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem foo {α} [DecidableEq α] : True := True.intro

def Foo (α) [DecidableEq α] := Unit

#guard_msgs in
theorem bar {α} [DecidableEq α] (s : Foo α) : s = s := rfl

/--
warning: `foo₂` has the hypothesis:
  • [(α : Type) → Decidable (Nonempty α)] (#2)
which is not used in the remainder of the type.

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem foo₂ (a : Type) [∀ α : Type, Decidable (Nonempty α)] (_ : Unit) [Nonempty a] : True :=
  trivial

/--
warning: `foo₃` has the hypotheses:
  • [(α : Type) → Decidable (Nonempty α)] (#2)
  • [DecidableEq β] (#3)
which are not used in the remainder of the type.

Consider removing these hypotheses and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem foo₃ {β} [∀ α : Type, Decidable (Nonempty α)] [DecidableEq β] : True := trivial

-- See through `let`, don't count it as an index
/--
warning: `foo₄` has the hypothesis:
  • [DecidableEq β] (#2)
which is not used in the remainder of the type.

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem foo₄ {β} : let _ := 2; ∀ [DecidableEq β], True := trivial

-- Linter should not fire when `sorry` appears in the type, even though the instances are unused
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem fooSorry {β} [∀ α : Type, Decidable (Nonempty α)] [DecidableEq β] (b : sorry) : True :=
  trivial

end unused

section used

/- The linter either should not fire on these declarations because the instance hypotheses are used
in the type, or not fire on *every* instance in these declarations. -/

theorem fooUsing [DecidableEq (Nat → Nat)] : Uses (DecidableEq (Nat → Nat)) := trivial

theorem fooUsing₁ [DecidableEq (Nat → Nat)] : Uses (DecidableEq (Nat → Nat)) → True :=
  fun _ =>  trivial

-- Should fire on parameter #1 but not parameter #2
/--
warning: `fooUsing₂` has the hypothesis:
  • [DecidablePred Nonempty] (#1)
which is not used in the remainder of the type.

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
theorem fooUsing₂ [DecidablePred Nonempty] [DecidableEq (Nat → Nat)] :
    Uses (DecidableEq (Nat → Nat)) → True :=
  fun _ =>  trivial

-- Note `optParam` test
theorem fooUsing₃ [DecidablePred Nonempty] [DecidableEq (Nat → Nat)]
    (_ : Uses (DecidablePred Nonempty) := trivial) : Uses (DecidableEq (Nat → Nat)) → True :=
  fun _ =>  trivial

end used

end decidable

namespace Fintype

set_option linter.unusedFintypeInType true

section unused

/--
warning: `foo` has the hypothesis:
  • [Fintype α] (#2)
which is not used in the remainder of the type.

Consider replacing this hypothesis with the corresponding instance of `Finite` or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo {α} [Fintype α] : True := True.intro

def Foo (α) [Fintype α] := Unit

#guard_msgs in
theorem bar {α} [Fintype α] (s : Foo α) : s = s := rfl

/--
warning: `foo₂` has the hypotheses:
  • [(α : Type) → Fintype α] (#2)
  • [Fintype a] (#4)
which are not used in the remainder of the type.

Consider replacing these hypotheses with the corresponding instances of `Finite` or removing them entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo₂ (a : Type) [∀ α : Type, Fintype α] (_ : Unit) [Fintype a] : True :=
  trivial

-- TODO: why the newline + indentation in the pretty-printing of the forall?
/--
warning: `foo₃` has the hypotheses:
  • [(α : Type) → Fintype α] (#2)
  • [Fintype β] (#3)
which are not used in the remainder of the type.

Consider replacing these hypotheses with the corresponding instances of `Finite` or removing them entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo₃ {β} [∀ α : Type, Fintype α] [Fintype β] : True := trivial

-- See through `let`, don't count it as an index
/--
warning: `foo₄` has the hypothesis:
  • [Fintype β] (#2)
which is not used in the remainder of the type.

Consider replacing this hypothesis with the corresponding instance of `Finite` or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo₄ {β} : let _ := 2; ∀ [Fintype β], True := trivial

-- Linter should not fire when `sorry` appears in the type, even though the instances are unused
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem fooSorry {β} [∀ α : Type, Fintype α] [Fintype β] (b : sorry) : True :=
  trivial

end unused

section used

/- The linter either should not fire on these declarations because the instance hypotheses are used
in the type, or not fire on *every* instance in these declarations. -/

theorem fooUsing [Fintype (Nat → Nat)] : Uses (Fintype (Nat → Nat)) := trivial

theorem fooUsing₁ [Fintype (Nat → Nat)] : Uses (Fintype (Nat → Nat)) → True :=
  fun _ =>  trivial

-- Should fire on parameter #1 but not parameter #2
/--
warning: `fooUsing₂` has the hypothesis:
  • [Fintype Bool] (#1)
which is not used in the remainder of the type.

Consider replacing this hypothesis with the corresponding instance of `Finite` or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem fooUsing₂ [Fintype Bool] [Fintype (Nat → Nat)] :
    Uses (Fintype (Nat → Nat)) → True :=
  fun _ =>  trivial

-- Note `optParam` test
theorem fooUsing₃ [Fintype Bool] [Fintype (Nat → Nat)]
    (_ : Uses (Fintype Bool) := trivial) : Uses (Fintype (Nat → Nat)) → True :=
  fun _ =>  trivial

set_option linter.unusedFintypeInType false in
theorem fooUsing₂' [Fintype Bool] [Fintype (Nat → Nat)] :
    Uses (Fintype (Nat → Nat)) → True :=
  fun _ =>  trivial

end used

end Fintype

section setOptionIn

/-! Test workaround for lean4#11313 -/

set_option linter.unusedDecidableInType false in
theorem fooUsing₂' [DecidablePred Nonempty] [DecidableEq (Nat → Nat)] :
    Uses (DecidableEq (Nat → Nat)) → True :=
  fun _ => trivial

set_option linter.unusedDecidableInType false

/--
warning: `fooUsing₂''` has the hypothesis:
  • [DecidablePred Nonempty] (#1)
which is not used in the remainder of the type.

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
set_option linter.unusedDecidableInType true in
theorem fooUsing₂'' [DecidablePred Nonempty] [DecidableEq (Nat → Nat)] :
    Uses (DecidableEq (Nat → Nat)) → True :=
  fun _ =>  trivial

end setOptionIn
