module

import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter

section
set_option linter.style.redundantSyntax true

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
@ +1:19...22
warning: Try this:
   ̵<̵|̵

`0` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs (positions := true) in
example : (Nat.succ <| 0) = 1 := rfl

/--
@ +1:22...25
warning: Try this:
   ̵<̵|̵

`[1]` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs (positions := true) in
example : (List.cons 0 <| [1]) = [0,1] := rfl

notation "ℕ" => Nat

/--
@ +1:20...23
warning: Try this:
   ̵<̵|̵

`ℕ` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs (positions := true) in
example (n : ℕ) : id <| ℕ := n

/--
@ +1:31...34
warning: Try this:
   ̵<̵|̵

`·` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs (positions := true) in
example : (ℕ → ℕ) → ℕ → ℕ := (· <| ·)

/--
@ +1:29...32
warning: Try this:
   ̵<̵|̵

`nofun` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs (positions := true) in
example : Empty → Empty := id <| nofun

/--
@ +1:13...16
warning: Try this:
   ̵<̵|̵

`@ℕ` can be parsed as a function argument, so the pipe operator `<|` can be omitted.

Note: This linter can be disabled with `set_option linter.style.redundantSyntax false`
-/
#guard_msgs (positions := true) in
example := id <| @ℕ

-- We currently don't lint against `<| fun` or `<| ¬`.
example : Nat → Nat := id <| fun x ↦ x
example : Nat → Nat := id <| @fun x ↦ x
example : ([0,1].foldl (init := 0) <| fun a b ↦ a + b) = 1 := rfl
example := id <| ¬ 0 ≤ 1

end
