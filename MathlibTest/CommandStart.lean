import Mathlib.Tactic.Linter.CommandStart
import Aesop.Frontend.Attribute
import Aesop.Frontend.Command
--import Mathlib.Tactic.Lemma
--import Mathlib.Data.Set.Defs
--import Mathlib.Logic.Function.Defs
--import Mathlib.adomaniLeanUtils.inspect_syntax
--import Mathlib.Util.ParseCommand

set_option linter.style.commandStart true

section Desiderata_and_todos

-- The "tactic `{...}` is ignored entirely:
-- the pretty-printer wants a space after `{`, but not one before `}`.
example : True := by {refine ?_   ;    trivial  }

-- Ideally, this would complain, but the pretty-printer prefers this version.
example : True = True := by
  conv =>
    ·rfl

-- Ideally, this would complain, but the linter ignores `throwError`
#eval do
  if false then throwError"s"

-- Ideally, these would complain, but we silenced the linter for `rcases`.
example (h : False) : False := by rcases  h
example (h : False) : False := by rcases(h)

structure X where
  A : {_ : Nat} → Nat → Nat

-- The pretty printer does not place spaces around the braces`{}`.
example : X where A{a}b := a + b

-- Ideally, these would complain, but we silenced the linter for `let`.
example := let(_) := 0; 0
example := let  _ := 0; 0

example : True := by {trivial }

-- Ideally, this would complain, but we silenced the linter for `declare_aesop_rule_sets`.
declare_aesop_rule_sets [$id](default := true)

-- The linter ignores `macro`, `elab` and `elab_rules`
macro "#F" : command => `(section
)
elab "#F" : command => do Lean.Elab.Command.elabCommand (← `(section)
)
elab_rules : tactic
| `(tactic| skip
) => do
  return

-- Ideally, this would complain, but we silenced the linter for term-mode `have`.
example : True :=
  have(h) := trivial
  h

-- Ideally, this would complain, but we silenced the linter for term-mode `replace`.
example (h : ∀ a : Nat, a = a) : 0 = 0 := by
  replace(h) := h 0
  exact h

-- Ideally, this would complain, but we silenced the linter for term-mode
example {c : Bool} : c = c := by
  induction c with
  | true| _ =>rfl

-- Ideally, this would complain, but `simp!` requires a trailing space.
example : 0 = 0 := by
  simp! ;

-- The pretty-printer prefers no spaces inside `{}`.
example := { Nat.succ n | n < 0 }


end Desiderata_and_todos

-- The linter ignores lists and arrays.
example := [
  0]
example := #[
  0]

/--
warning: missing space in the source

This part of the code
  'obtain(⟨h⟩)'
should be written as
  'obtain (⟨h⟩)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example (h : False) : False := by
  obtain(⟨h⟩) := h

-- Ignore `⟨...⟩`, since it is convenient to allow a line-break after `⟨` to align multiple fields.
example := (⟨
  0⟩ : Inhabited Nat)

/--
warning: missing space in the source

This part of the code
  'example: True'
should be written as
  'example : True'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example: True := trivial

-- Constructs that are ignored by the linter, and (former) false positives.
section noFalsePositives

-- Explicit name literals: used to error (and the suggested replacement is invalid syntax).
example := ``Nat

-- This example would trigger the linter if we did not special case
-- `where` in `Mathlib.Linter.Style.CommandStart.getUnlintedRanges`.
/-- A -/
example := aux
where
  /-- A -/
  aux : Unit := ()

-- Strings are ignored by the linter.
variable (a : String := "  ")
                   --
-- The linter skips double-quoted names.
variable (d : Lean.Name := ``Nat) in open Nat

-- Code inside `run_cmd` is not checked at all.
run_cmd
  for  _ in[0]   do
    let _    ←  `(
      end )

def Card : Type → Nat := fun _ => 0

/-- Symbols for use by all kinds of grammars. -/
inductive Symbol (T N : Type)
  /-- Terminal symbols (of the same type as the language) -/
  | terminal (t : T) : Symbol T N
  /-- Nonterminal symbols (must not be present when the word being generated is finalized) -/
  | nonterminal (n : N) : Symbol T N
deriving
  DecidableEq, Repr

-- embedded comments do not cause problems!
#guard_msgs in
open Nat in -- hi
example : True := trivial

-- embedded comments do not cause problems!
#guard_msgs in
open Nat in
 -- hi
example : True := trivial

-- embedded comments do not cause problems!
#guard_msgs in
open Nat in
  -- hi
example : True := trivial

structure FX where
  /-- A doc -/
  x : Nat

open Nat in /- hi -/
example : True := trivial

-- The notation `0::[]` disables the linter
variable (h : 0::[] = [])

/-- A doc string -/
-- comment
example : True := trivial
example : 0 = 0 :=
  calc _ = 0 + 0 := (Nat.add_zero _).symm
       _ = 1 * 0 + 0 := Nat.add_comm ..
       _ = 1 * 0 + 1 * 0 := Nat.add_comm ..
       _ = 1 * (0 + 0) := Nat.mul_add .. |>.symm
       _ = 0 := rfl

open Function in
inspect
theorem leftInverse_of_surjective_of_rightInverse {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx

open Lean Elab Command in
elab "us " cmd:command : command => do
  let s := cmd.raw.uniformizeSpaces
  let pretty ← Elab.Command.liftCoreM do Mathlib.Linter.Style.CommandStart.ppCategory' `command s
  let pretty := " ".intercalate <| (pretty.pretty.split (·.isWhitespace)).filter (!·.isEmpty)
  logInfo m!"cmd:\n{cmd}\n---\ns:\n{s}\n---\npretty:\n{pretty}\n---"
  logInfo <| InspectSyntax.toMessageData s
  elabCommand cmd

open Lean in
run_cmd
  let stx ← `(section     X)
  let s := stx.raw.uniformizeSpaces
  let pretty ← Elab.Command.liftCoreM do Mathlib.Linter.pretty s
  logInfo <| InspectSyntax.toMessageData s

open Lean Parser Mathlib.GuardExceptions in
run_cmd
  let str := "example : True := trivial"
  let s := captureException (← getEnv) topLevelCommandParserFn str
  match s with
  | .ok s =>
    logInfo <| InspectSyntax.toMessageData s
  | _ => logWarning "error!"


us
theorem «--» /- -/ : --
    ({True} : Set Prop) = {True} /- as -/ := rfl


-- Test that `Prop` and `Type` that are not escaped with `«...»` do not cause problems.
def Prop.Hello := 0
def Type.Hello := 0

/--
warning: extra space in the source

This part of the code
  'F  : True'
should be written as
  'F : True'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
lemma F  : True := trivial

namespace List

variable {α β : Type} (r : α → α → Prop) (s : β → β → Prop)

-- The two infix are needed.  They "hide" a `quotPrecheck`
local infixl:50 " ≼ " => r
-- The two infix are needed.  They "hide" a `quotPrecheck`
local infixl:50 " ≼ " => s

/--
warning: The `commandStart` linter had some parsing issues: feel free to silence it and report this error!

Note: This linter can be disabled with `set_option linter.style.commandStart.verbose false`
-/
#guard_msgs in
set_option linter.style.commandStart.verbose true in
example {a : α} (_ : a ≼ a) : 0 = 0 := rfl

end List

end noFalsePositives

-- Miscellaneous constructs: variable, include, omit statements; aesop rulesets
section misc
/--
warning: extra space in the source

This part of the code
  'field1     : Nat'
should be written as
  'field1 : Nat'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
structure A where
  field1     : Nat
  field2 : Nat

/--
warning: extra space in the source

This part of the code
  'field2     : Nat'
should be written as
  'field2 : Nat'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
structure B where
  field1 : Nat
  field2     : Nat

/--
warning: extra space in the source

This part of the code
  ':     Nat'
should be written as
  ': Nat field2'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  'field2     : Nat'
should be written as
  'field2 : Nat'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
structure C where
  field1 :     Nat
  field2     : Nat

-- Note that the linter does not attempt to recognise or respect manual alignment of fields:
-- this is often brittle and should usually be removed.
/--
warning: extra space in the source

This part of the code
  'field1    :  '
should be written as
  'field1 : Nat'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  ':     Nat'
should be written as
  ': Nat field2'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  'field2    : Nat'
should be written as
  'field2 : Nat'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
structure D where
  field1    :     Nat
  field2    : Nat

-- This also applies to consecutive declarations.
/--
warning: declaration uses 'sorry'
---
warning: extra space in the source

This part of the code
  'instance   {R}'
should be written as
  'instance {R} :'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
instance   {R} : Add R := sorry
/--
warning: declaration uses 'sorry'
---
warning: extra space in the source

This part of the code
  'instance   {R}'
should be written as
  'instance {R} :'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
instance   {R} : Add R := sorry

variable [h : Add Nat] [Add Nat]

/--
warning: extra space in the source

This part of the code
  'variable    [ h'
should be written as
  'variable [h :'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  '[ h  '
should be written as
  '[h : Add'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  'h    : Add'
should be written as
  '[h : Add'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  'Nat   ] ['
should be written as
  'Nat] [Add'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  '[ Add'
should be written as
  '[Add Nat]'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
variable    [ h    : Add Nat   ] [ Add Nat]

/--
warning: extra space in the source

This part of the code
  'omit  [h :'
should be written as
  'omit [h :'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  'Nat]  [Add'
should be written as
  'Nat] [Add'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
omit  [h : Add Nat]  [Add Nat]

/--
warning: extra space in the source

This part of the code
  'include     h

'
should be written as
  'include h'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
include     h

/--
warning: extra space in the source

This part of the code
  '@[aesop  (rule_sets'
should be written as
  '@[aesop (rule_sets'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
@[aesop  (rule_sets := [builtin]) safe apply] example : True := trivial

end misc

/--
warning: 'section' starts on column 1, but all commands should start at the beginning of the line.

Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
 section

/--
warning: extra space in the source

This part of the code
  'example    : True'
should be written as
  'example : True'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example    : True := trivial

/--
warning: extra space in the source

This part of the code
  ':     True'
should be written as
  ': True'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example :     True := trivial

/--
warning: extra space in the source

This part of the code
  'example  :  True'
should be written as
  'example : True'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space in the source

This part of the code
  ':  True'
should be written as
  ': True'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: missing space in the source

This part of the code
  ':=trivial'
should be written as
  ':= trivial'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example  :  True :=trivial

/--
warning: missing space in the source

This part of the code
  '(a: Nat)'
should be written as
  '(a : Nat)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
variable (a: Nat)

/--
warning: missing space in the source

This part of the code
  '(_a: Nat)'
should be written as
  '(_a : Nat)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example (_a: Nat) : True := trivial

/--
warning: missing space in the source

This part of the code
  '{a: Nat}'
should be written as
  '{a : Nat}'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a: Nat} : a = a := rfl

/--
a
b
c
d -/
example (_a : Nat) (_b : Int) : True := trivial

/--
warning: missing space in the source

This part of the code
  ':Nat}'
should be written as
  ': Nat}'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a :Nat} : a = a := rfl

/--
warning: extra space in the source

This part of the code
  'example  {a :Nat}'
should be written as
  'example {a :'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: missing space in the source

This part of the code
  ':Nat}'
should be written as
  ': Nat}'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example  {a :Nat} : a = a := rfl

/--
warning: unused variable `b`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: missing space in the source

This part of the code
  'Nat}{b :'
should be written as
  'Nat} {b :'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a : Nat}{b : Nat} : a = a := rfl

/--
warning: extra space in the source

This part of the code
  'Nat}  : a'
should be written as
  'Nat} : a ='


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a : Nat}  : a = a := rfl

/--
warning: extra space in the source

This part of the code
  'alpha   ] {a'
should be written as
  'alpha] {a'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {alpha} [Neg alpha   ] {a : Nat} : a = a := rfl

/--
warning: extra space in the source

This part of the code
  'example  : True'
should be written as
  'example : True'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
/-- Check that doc/strings do not get removed as comments. -/
example  : True := trivial

-- Unit tests for internal functions in the linter.
section internal

/--
info: #[srcNat: 12, srcPos: 12, fmtPos: 2, msg: extra space, length: 7
, srcNat: 4, srcPos: 4, fmtPos: 1, msg: extra space, length: 3
]
-/
#guard_msgs in
#eval
  let s := "example        f   g"
  let t := "example fg"
  Mathlib.Linter.parallelScan s t

/--
info: #[srcNat: 19, srcPos: 19, fmtPos: 21, msg: extra space, length: 1
, srcNat: 16, srcPos: 16, fmtPos: 19, msg: extra space, length: 2
, srcNat: 7, srcPos: 7, fmtPos: 12, msg: missing space, length: 1
]
-/
#guard_msgs in
#eval
  let s := "example  :   True :=trivial"
  let t := "example : True :=
    trivial"
  Mathlib.Linter.parallelScan s t

/--
info: #[srcNat: 4, srcPos: 4, fmtPos: 5, msg: missing space, length: 1
, srcNat: 2, srcPos: 2, fmtPos: 1, msg: extra space, length: 1
]
-/
#guard_msgs in
#eval
  let l := "hac d"
  let m := "h  acd"
  Mathlib.Linter.parallelScan l m

-- Starting from `c` (due to the `"d ef gh".length` input), form a "window" of successive sizes
-- `1, 2,..., 6`.  The output is trimmed and contains only full words, even partially overlapping
-- with the given lengths.
#guard Mathlib.Linter.Style.CommandStart.mkWindow "ab cd ef gh" "d ef gh".length 1 == "cd"
#guard Mathlib.Linter.Style.CommandStart.mkWindow "ab cd ef gh" "d ef gh".length 2 == "cd"
#guard Mathlib.Linter.Style.CommandStart.mkWindow "ab cd ef gh" "d ef gh".length 3 == "cd ef"
#guard Mathlib.Linter.Style.CommandStart.mkWindow "ab cd ef gh" "d ef gh".length 4 == "cd ef"
#guard Mathlib.Linter.Style.CommandStart.mkWindow "ab cd ef gh" "d ef gh".length 5 == "cd ef"
#guard Mathlib.Linter.Style.CommandStart.mkWindow "ab cd ef gh" "d ef gh".length 6 == "cd ef gh"

end internal
