module

import Mathlib.Init

set_option linter.style.redundantSyntax true

section Pipe

/--
@ +1:19...22
warning: Try this:
   ̵<̵|̵

`(0)` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs (positions := true) in
example : (Nat.succ <| (0)) = 1 := rfl

/--
warning: Try this:
   ̵<̵|̵

`0` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example : (Nat.succ <| 0) = 1 := rfl

/--
warning: Try this:
   ̵<̵|̵

`[1]` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example : (List.cons 0 <| [1]) = [0,1] := rfl

notation "ℕ" => Nat

/--
warning: Try this:
   ̵<̵|̵

`ℕ` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example (n : ℕ) : id <| ℕ := n

/--
warning: Try this:
   ̵<̵|̵

`·` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example : (ℕ → ℕ) → ℕ → ℕ := (· <| ·)

/--
warning: Try this:
   ̵<̵|̵

`nofun` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example : Empty → Empty := id <| nofun

/--
warning: Try this:
   ̵<̵|̵

`@ℕ` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example := id <| @ℕ

/--
warning: Try this:
   ̵<̵|̵

`Type*` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example := outParam <| Type*

instance : Inv (Rat → Rat) := ⟨id⟩
/--
warning: Try this:
   ̵<̵|̵

`x⁻¹` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example (f : Rat → Rat) (x : Rat) := f⁻¹ <| x⁻¹

-- The `{...}` notation is ambiguous between set notation and constructor notation
/--
warning: Try this:
   ̵<̵|̵

`{ 1, 2, 3 }` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example : Std.HashSet Nat := id <| {1, 2, 3}

/--
warning: Try this:
   ̵<̵|̵

`{ }` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example : Std.HashSet Nat := id <| {}

-- We currently don't lint against `<| fun` or `<| ¬`.
example : Nat → Nat := id <| fun x ↦ x
example : Nat → Nat := id <| @fun x ↦ x
example : ([0,1].foldl (init := 0) <| fun a b ↦ a + b) = 1 := rfl
example := id <| ¬ 0 ≤ 1

/--
warning: Try this:
   ̵<̵|̵

`do
  return 42` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example : Id Nat := id <| do
  return 42

-- Don't warn when the funtion is not an application or a syntax with `max` precedence.
instance : Add (Nat → Nat) := ⟨fun f _ ↦ f⟩
example (f g : Nat → Nat) := f + g <| 3

end Pipe

section PipeProj

/--
@ +1:14...18
warning: Try this:
   ̵|̵>̵.

`[1]` can be parsed at maximal precedence, so the operator `|>.` can be replaced with a normal `.` projection.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs (positions := true) in
example : ([1] |>.cons 0) = [0, 1] := rfl

/--
warning: Try this:
   ̵|̵>̵.

`·` can be parsed at maximal precedence, so the operator `|>.` can be replaced with a normal `.` projection.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs in
example (as : Array Nat) : Std.HashSet Nat := as.foldl (· |>.insert ·) {}

-- In these cases, replacing `|>.` with `.` causes weird parsing, so we don't lint them.
example : (1 |>.succ) = 2 := rfl
example := ``Nat |>.isStr
example : Nat := .zero |>.succ

-- We allow `|>.` when it follows a newline.
example : ([1]
  |>.cons 0) = [0, 1] := rfl

end PipeProj
