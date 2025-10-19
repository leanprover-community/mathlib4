import Mathlib.Tactic.Linter.CommandStart
import Qq
import Aesop.Frontend.Attribute
import Aesop.Frontend.Command
--import Mathlib.Tactic.Lemma
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.adomaniLeanUtils.inspect_syntax
--import Mathlib.Util.ParseCommand

open Lean Elab Command Mathlib Linter Style.CommandStart in
elab tk:"#reformat " cmd:command : command => do
  let tktxt := "#reformat"
  if let some cmdSubstring := cmd.raw.getSubstring? then
  if let .error .. :=
    captureException (← getEnv) Parser.topLevelCommandParserFn cmd.raw.getSubstring?.get!.toString
  then
    logWarningAt tk m!"{tktxt}: Parsing failed"
    return
  elabCommand cmd
  if (← get).messages.hasErrors then
    logWarningAt tk m!"{tktxt}: Command has errors"
    return
  match ← getExceptions (verbose? := false) cmd with
  | none => logWarningAt tk m!"{tktxt} internal error!"
--  | some #[] => logInfoAt tk "All is good!"
  | some mex =>
    let (reported, _) := reportedAndUnreportedExceptions mex
    if reported.isEmpty then
      logInfoAt tk "All is good!"
      return
    let parts := mkStrings cmdSubstring (reported.map (·.rg.start))
    let reformatted := parts.foldl (· ++ ·.toString) ""
    liftTermElabM do Meta.liftMetaM do Lean.Meta.Tactic.TryThis.addSuggestion cmd reformatted

#reformat
set_option linter.style.commandStart true

#reformat
example : True ∧ True := by
  refine ?_
  constructor
  · {exact trivial}
  · apply ?_
    first | assumption | done | assumption | trivial
set_option linter.style.commandStart false in

#reformat
example    :   True∧
   True    :=by
  refine ?_
  constructor
  ·{exact  trivial}
  · apply  ?_    ;
    first|assumption|
     done|assumption   |     trivial









example : True ∧ True := by
  refine ?_
  constructor
  ·{exact  trivial}
  · apply  ?_    ;
    first|assumption|
     done|assumption   |     trivial





section Desiderata_and_todos

#mex
/-!    -/


/--
info: Pretty-printed syntax:
theorem FX (_ : Nat) : True := by trivial; done
---
info: 6 whitespace issues found: 6 reported and 0 unreported.
---
warning: reported: add space in the source

This part of the code
  'FX(_'
should be written as
  'FX (_'


[Lean.Parser.Command.declaration, Lean.Parser.Command.theorem, Lean.Parser.Command.declId, ident.FX]
---
warning: reported: remove space in the source

This part of the code
  'FX(_  :Nat)'
should be written as
  'FX(_ :Nat)'


[Lean.Parser.Command.declaration,
 Lean.Parser.Command.theorem,
 Lean.Parser.Command.declSig,
 null,
 Lean.Parser.Term.explicitBinder,
 null,
 Lean.Parser.Term.hole,
 atom._]
---
warning: reported: add space in the source

This part of the code
  ':Nat)'
should be written as
  ': Nat)'


[Lean.Parser.Command.declaration,
 Lean.Parser.Command.theorem,
 Lean.Parser.Command.declSig,
 null,
 Lean.Parser.Term.explicitBinder,
 null,
 atom.«:»]
---
warning: reported: add space in the source

This part of the code
  'True:='
should be written as
  'True :='


[Lean.Parser.Command.declaration,
 Lean.Parser.Command.theorem,
 Lean.Parser.Command.declSig,
 Lean.Parser.Term.typeSpec,
 ident.True]
---
warning: reported: remove space in the source

This part of the code
  'by  trivial;'
should be written as
  'by trivial;'


[Lean.Parser.Command.declaration,
 Lean.Parser.Command.theorem,
 Lean.Parser.Command.declValSimple,
 Lean.Parser.Term.byTactic,
 atom.by]
---
warning: reported: remove space in the source

This part of the code
  'trivial;  done'
should be written as
  'trivial; done'


[Lean.Parser.Command.declaration,
 Lean.Parser.Command.theorem,
 Lean.Parser.Command.declValSimple,
 Lean.Parser.Term.byTactic,
 Lean.Parser.Tactic.tacticSeq,
 Lean.Parser.Tactic.tacticSeq1Indented,
 null,
 atom.«;»]
-/
#guard_msgs in
set_option linter.style.commandStart false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
#mex
theorem FX(_  :Nat) : True:=     --
  by  trivial;  done



-- The "tactic `{...}` is ignored entirely:
-- the pretty-printer does not want a space after `{`, but wants one before `}`.
--set_option linter.style.commandStart false in
--#mex
example : True := by { trivial }
example : True := by {trivial}
example : True := by { refine ?_   ;    exact (by refine trivial)}

/--
warning: add space in the source

This part of the code
  '·rfl'
should be written as
  '· rfl'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: 'done' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : True = True := by
  · conv =>
    -- The *linter* forces a space in `·rfl`, but the pretty-printer does not.
    ·rfl
  done

set_option linter.style.commandStart false in
-- Both `¬ False` and `¬False` are allowed.
/--
info: Pretty-printed syntax:
example : ¬False ∨ ¬False := by simp
---
info: 1 whitespace issue found: 0 reported and 1 unreported.
---
info: unreported: remove space in the source

This part of the code
  '¬ False'
should be written as
  '¬False'


[Lean.Parser.Command.declaration,
 Lean.Parser.Command.example,
 Lean.Parser.Command.optDeclSig,
 null,
 Lean.Parser.Term.typeSpec,
 «term_∨_»,
 «term¬_»,
 atom.«¬»]
-/
#guard_msgs in
#mex
example : ¬ False ∨ ¬False := by simp

#mex
example : ¬ False ∨ ¬False := by simp

/--
warning: remove space in the source

This part of the code
  '( ·'
should be written as
  '(·)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
---
warning: remove space in the source

This part of the code
  '· )'
should be written as
  '(·)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {α} : α → α := by
  -- Focusing dot and centerdots are "correctly" interpreted, even with the special-casing of
  -- the `conv`-mode `·`.
  · exact ( · )

/--
warning: remove space in the source

This part of the code
  '+  ·)'
should be written as
  '+ ·)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example : Nat → Nat → Nat := by
  exact (· +  ·)

/--
warning: add space in the source

This part of the code
  'throwError"s"'
should be written as
  'throwError "s"'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
#eval do
  -- The *linter* forces a space in `throwError"s"`, but the pretty-printer does not.
  if false then throwError"s"
  if false then throwError "s"

/--
warning: remove space in the source

This part of the code
  'rcases  h'
should be written as
  'rcases h'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example (h : False) : False := by
  rcases  h

/--
warning: add space in the source

This part of the code
  'rcases(h)'
should be written as
  'rcases (h)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example (h : False) : False := by
  -- The *linter* forces a space in `rcases(h)`, but the pretty-printer does not.
  rcases(h)

structure X where
  A : {_ : Nat} → Nat → Nat

-- The pretty printer does not place spaces around the braces`{}`.
example : X where A{a}b := a + b

/--
warning: add space in the source

This part of the code
  'let(_)'
should be written as
  'let (_)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example :=
  -- The *linter* forces a space in `let(_)`, but the pretty-printer does not.
  let(_) := 0; 0

/--
warning: remove space in the source

This part of the code
  'let  h'
should be written as
  'let h'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example :=
  let  h := 0; h

example : True := by {trivial }

/-- warning: #mex: Processing error -/
#guard_msgs in
#mex
open Qq in
--set_option linter.style.commandStart.verbose true in
example {u : Lean.Level} (α : Q(Type u)) (_ : Q(Mul $α)) : Mul Q($α) where
  mul x y := q($x * $y)

-- Ideally, this would complain, but we silenced the linter for `declare_aesop_rule_sets`.
declare_aesop_rule_sets [$id](default := true)

-- `library_note` may have or not have a space between `""` and `/-- -/`
library_note ""/-- -/
library_note "" /-- -/

-- The pretty-printer does not place a space after `safe`.
--`attribute [aesop safe (rule_sets := [CategoryTheory])] Subsingleton.elim`

-- The linter ignores `macro`, `elab` and `elab_rules`
macro "#F" : command => `(section
)
elab "#F" : command => do Lean.Elab.Command.elabCommand (← `(section)
)
elab_rules : tactic
| `(tactic| skip
) => do
  return

/--
warning: add space in the source

This part of the code
  'have(h)'
should be written as
  'have (h)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example : True :=
  -- The *linter* forces a space in `have(_)`, but the pretty-printer does not.
  have(h) := trivial
  h

example : True :=
  -- The *linter* forces a space in `have(_)`, but the pretty-printer does not.
  have (h) := trivial
  h

/--
warning: add space in the source

This part of the code
  'replace(h)'
should be written as
  'replace (h)'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example (h : ∀ a : Nat, a = a) : 0 = 0 := by
  -- The *linter* forces a space in `replace(h)`, but the pretty-printer does not.
  replace(h) := h 0
  exact h

-- Ideally, `| true|` would complain.
example {c : Bool} : c = c := by
  induction c with
  | true| _ => rfl

/--
warning: add space in the source

This part of the code
  '=>rfl'
should be written as
  '=> rfl'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {c : Bool} : c = c := by
  induction c with
  | true| _ =>rfl

-- Ideally, this would complain, but `simp!` requires a trailing space.
example : 0 = 0 := by
  simp! ;

-- The pretty-printer prefers no spaces inside `{}`.
example := { Nat.succ n | n < 0 }
-- The pretty-printer prefers spaces inside `{}`.
example := {n // n < 0}

end Desiderata_and_todos

-- The linter ignores lists and arrays.
example := [
  0]
example := #[
  0]

/--
warning: add space in the source

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
warning: add space in the source

This part of the code
  'example:'
should be written as
  'example :'


Note: This linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example: True := trivial

-- Constructs that are ignored by the linter, and (former) false positives.
section noFalsePositives

-- Explicit name literals: used to error (and the suggested replacement is invalid syntax).
example := ``Nat

-- The *linter* forces a space after `where`, but the pretty-printer does not.
/-- A doc-string -/
example := if bool then aux else aux
where
  /-- A separate doc-string -/
  aux : Unit := ()
  /-- Another too -/
  bool := true

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

structure DFX where
  /-- A doc -/
  x : Nat

#exit
open Lean Elab Command Mathlib.Linter in
elab "#final_scan " stx:command : command => do
  elabCommand stx
  let ustx := stx.raw.uniformizeSpaces
  let simplySpaced ← pretty ustx <|> return default
  let final := scanWatching true #[] stx.raw.getKind stx ustx (simplySpaced).toSubstring

  logInfo <| m!"Syntax with no spaces:\n{ustx}\n{InspectSyntax.toMessageData ustx}"
  logInfo <| m!"Reconstructed string:\n{simplySpaced}"
  let ok? := captureException (← getEnv) Parser.topLevelCommandParserFn simplySpaced
  if let .ok es := ok? then
    logInfo <| m!"Reconstruced syntax:\n{es}\n{InspectSyntax.toMessageData es}"
    logInfo <| m!"Compare: {ustx.compare es}"
  else
    logWarning "Did not parse correctly"
  logInfo m!"{final.1}"
  logInfo m!"{final.2}"

#final_scan
open Nat in /- hi -/
/-- Here is also   -/
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

#eval
  let s1 := "/--    asd awe  adg ghdrt \n\n ñk -/".toSubstring
  let s2 := "/-- asd  awe adg ghdrt\n\nñk-/ this one continues".toSubstring
  Mathlib.Linter.consumeIgnoring s1 s2 (·.all Char.isWhitespace)


run_cmd
  let mut a := "⟨ακ⟩".toSubstring
  let mut con := 0
  while !a.isEmpty do
    dbg_trace "Step {con}: {a}"
    con := con + 1
    a := a.drop 1
  IO.println con


--inspect
#final_scan
open Function in
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
  let pretty ← Elab.Command.liftCoreM do Mathlib.Linter.ppCategory' `command s
  let pretty := " ".intercalate <| (pretty.pretty.split (·.isWhitespace)).filter (!·.isEmpty)
  logInfo m!"cmd:\n{cmd}\n---\ns:\n{s}\n---\npretty:\n{pretty}\n---"
  logInfo <| InspectSyntax.toMessageData s
  elabCommand cmd

open Lean in
run_cmd
  let stx ← `(section     X)
  let s := stx.raw.uniformizeSpaces
  let pretty ← Mathlib.Linter.pretty s
  logInfo <| InspectSyntax.toMessageData s

open Lean Parser Mathlib.Linter in
run_cmd
  let str := "example : True := trivial"
  let s := captureException (← getEnv) topLevelCommandParserFn str
  match s with
  | .ok s =>
    logInfo <| InspectSyntax.toMessageData s
  | _ => logWarning "error!"



open Lean Elab Command in
elab "#again " verb?:(&" verbose")? stx:command : command => do
  elabCommand stx
  let s := stx.raw.uniformizeSpaces
  let sstring := reduceWhitespace s.regString
  let pretty ← Mathlib.Linter.pretty s
  let sNoSpaces := sstring.replace " " ""
  let prettyNoSpaces := pretty.replace " " ""
  let eq? := sNoSpaces == prettyNoSpaces
  let withSpaces ← insertSpaces verb?.isSome stx -- pretty
  logInfo <| InspectSyntax.toMessageData withSpaces
  logInfo
    m!"{eq?}: reduced and pretty are {if eq? then "" else "not "}equal up to spaces\n\n\
      Syntax:\n{s}\nReduced:\n{sstring}\nPretty:\n{pretty}\n{withSpaces.regString}\nRegener↑\n{pretty == (reduceWhitespace withSpaces.regString)}"

set_option linter.style.commandStart false in
#again verbose
example := 0


set_option linter.style.commandStart false in
#again
inspect
/--This    he las      -/
theorem «--» /- -/ : --
    ({ True } : Set Prop) = { True } /- as -/ := rfl

#again
open Function in
theorem leftInverse_of_surjective_of_rightInverse1 {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx




#again
inspect
#final_scan
theorem «--» /- -/ : --
    ({ True } : Set Prop) = { True } /- as -/ := rfl


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
