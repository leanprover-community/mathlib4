module

public import Aesop.Frontend.Attribute
public import Aesop.Frontend.Command
import all Mathlib.Tactic.Linter.Whitespace
public import Mathlib.Tactic.Linter.Whitespace
import Mathlib.Tactic.Lemma
public import Lean.Elab.Command
public meta import Lean.Meta.Tactic.TryThis
public import Mathlib.Util.ParseCommand
import Batteries.Util.LibraryNote
public import Batteries.Linter.UnreachableTactic
public import Qq
import Qq.Typ
import Mathlib.Tactic.FindSyntax
public import Mathlib.Util.Superscript

namespace Bundle
set_option linter.style.whitespace true
scoped notation:max "π " F':max E':max => Nat.add F' E'

#guard_msgs in
example := π 3 4

/--
warning: add space in the source

This part of the code
  '3(4)'
should be written as
  '3 (4)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example := π 3(4)

#guard_msgs in
example := π 3 (4)

/--
warning: remove space in the source

This part of the code
  '3  (4)'
should be written as
  '3 (4)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example := π 3  (4)

/--
warning: remove space in the source

This part of the code
  '(π  0'
should be written as
  '(π 0'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '0  1)'
should be written as
  '0 1)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '+  (π'
should be written as
  '+ (π'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '(π  0'
should be written as
  '(π 0'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '0  1)'
should be written as
  '0 1)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example := (π  0  1) + 0 +  (π  0  1)

/--
warning: remove space in the source

This part of the code
  '(π  0'
should be written as
  '(π 0'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '0  1)'
should be written as
  '0 1)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '(π  0'
should be written as
  '(π 0'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '0  1)'
should be written as
  '0 1)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example := (π  0  1) + 0 -  (π  0  1)

/--
warning: remove space in the source

This part of the code
  '(π  0'
should be written as
  '(π 0'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '0  1)'
should be written as
  '0 1)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '(π  0'
should be written as
  '(π 0'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '0  1'
should be written as
  '0 1'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '+  1)'
should be written as
  '+ 1)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example := (π  0  1) + 0 -  (π  0  1  +  1)

-- Undesirable: spaces after the third argument of `π` are ignored.
#guard_msgs in
example := (π 0 1 )

open Mathlib.Tactic (subscriptTerm) in
/-- For `m ≤ n`, `⦋m⦌ₙ` is the `m`-dimensional simplex in `Truncated n`. The
proof `p : m ≤ n` can also be provided using the syntax `⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  "⦋" term ("," term)? "⦌" noWs subscriptTerm : term
scoped macro_rules
  | `(⦋$m:term⦌$n:subscript) =>
    `($m + $n)
  | `(⦋$m:term, $p:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, $p⟩ : SimplexCategory.Truncated $n))

/-- info: 15 -/
#guard_msgs in
#eval
  ⦋0⦌₀₊₁₊₀₊₁₃ + 1

/--
info: 15
---
warning: remove space in the source

This part of the code
  '⦋0⦌₀₊₁₊ ₀₊₁₃'
should be written as
  '₊ ₀'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
#eval
  ⦋0⦌₀₊₁₊ ₀₊₁₃ + 1

/--
info: 15
---
warning: add space in the source

This part of the code
  '⦋0⦌₀₊₁₊₀₊₁₃+'
should be written as
  '₁₃ +'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
#eval
  ⦋0⦌₀₊₁₊₀₊₁₃+ 1

end Bundle

-- `meta` definitions are ignored
#guard_msgs in
set_option linter.style.whitespace true in
meta def New  := 0

set_option linter.style.whitespace true

#guard_msgs in
example : True ∧ True := by
  refine ?_
  constructor
  · {exact trivial}
  · apply ?_
    first | assumption | done | assumption | trivial

/--
warning: remove space in the source

This part of the code
  'example    :'
should be written as
  'example :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  ':   True∧'
should be written as
  ': True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'True∧'
should be written as
  'True ∧'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'True    :=by'
should be written as
  'True :='


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  ':=by'
should be written as
  ':= by'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  '·{exact'
should be written as
  '· {'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'apply  ?_'
should be written as
  'apply ?_;'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove spaces in the source

This part of the code
  '?_    ;'
should be written as
  '?_;'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'first|assumption|'
should be written as
  'first |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'first|assumption|'
should be written as
  '| assumption'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'first|assumption|'
should be written as
  'assumption |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'done|assumption'
should be written as
  'done |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'done|assumption'
should be written as
  '| assumption'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'done|assumption   |'
should be written as
  'assumption |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '|     trivial'
should be written as
  '| trivial'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example    :   True∧
   True    :=by
  refine ?_
  constructor
  ·{exact  trivial}
  · apply  ?_    ;
    first|assumption|
     done|assumption   |     trivial

/--
warning: add space in the source

This part of the code
  '·{exact'
should be written as
  '· {'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'apply  ?_'
should be written as
  'apply ?_;'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove spaces in the source

This part of the code
  '?_    ;'
should be written as
  '?_;'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'first|assumption|'
should be written as
  'first |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'first|assumption|'
should be written as
  '| assumption'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'first|assumption|'
should be written as
  'assumption |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'done|assumption'
should be written as
  'done |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'done|assumption'
should be written as
  '| assumption'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'done|assumption   |'
should be written as
  'assumption |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '|     trivial'
should be written as
  '| trivial'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example : True ∧ True := by
  refine ?_
  constructor
  ·{exact  trivial}
  · apply  ?_    ;
    first|assumption|
     done|assumption   |     trivial




-- Ideally, `| true|` would complain.
/--
warning: add space in the source

This part of the code
  'true|'
should be written as
  'true |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {c : Bool} : c = c := by
  induction c with
  | true| _ => rfl

/--
warning: add space in the source

This part of the code
  'true|'
should be written as
  'true |'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  '=>rfl'
should be written as
  '=> rfl'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {c : Bool} : c = c := by
  induction c with
  | true| _ =>rfl


section Desiderata_and_todos

-- Pretty-printing of unification hints: currently, they are not linted.
public def Foo := Nat

#guard_msgs in
unif_hint (_C : Foo) where
  ⊢ Foo =?= Foo

-- TODO: once the linter is fixed, this should error again
#guard_msgs in
unif_hint (_C : Foo) where
  ⊢  Foo =?= Foo

-- TODO: add tests around unary minus --- do we want to completely omit it?

/-!    -/


#guard_msgs in
set_option linter.style.whitespace false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

theorem FX(_  :Nat) : True:=     --
  by  trivial;  done



-- The "tactic `{...}` is ignored entirely:
-- the pretty-printer does not want a space after `{`, but wants one before `}`.
--set_option linter.style.whitespace false in
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: 'done' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : True = True := by
  · conv =>
    ·rfl
  done

set_option linter.style.whitespace false in
-- Both `¬ False` and `¬False` are allowed.
#guard_msgs in
example : ¬ False ∨ ¬False := by simp

example : ¬ False ∨ ¬False := by simp

/--
warning: remove space in the source

This part of the code
  '( ·'
should be written as
  '(·)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '· )'
should be written as
  '(·)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example (h : False) : False := by
  rcases(h)

structure X where
  A : {_ : Nat} → Nat → Nat

example : X where A {a} b := a + b

/--
warning: add space in the source

This part of the code
  'let(_)'
should be written as
  'let (_)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example :=
  let  h := 0; h

example : True := by {trivial }

open Qq in
--set_option linter.style.whitespace.verbose true in
example {u : Lean.Level} (α : Q(Type u)) (_ : Q(Mul $α)) : Mul Q($α) where
  mul x y := q($x * $y)

-- Ideally, this would complain, but we silenced the linter for `declare_aesop_rule_sets`.
declare_aesop_rule_sets [$id](default := true)

-- `library_note` may not have a space between `""` and `/-- -/`
/--
warning: add space in the source

This part of the code
  '"a"⧸--'
should be written as
  '"a" ⧸--'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
library_note "a"/-- Avoid empty doc-string -/
library_note "b" /-- Avoid empty doc-string -/

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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example (h : ∀ a : Nat, a = a) : 0 = 0 := by
  replace(h) := h 0
  exact h

-- Ideally, this would complain, but `simp!` requires a trailing space.
example : 0 = 0 := by
  simp! ;

-- The pretty-printer prefers no spaces inside `{}`.
-- TODO: fix this test; currently it causes a compile error
-- example := { Nat.succ n | n < 0 }
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example: True := trivial

-- Constructs that are ignored by the linter, and (former) false positives.
section noFalsePositives

-- This should not warn, because `True` could be a very long expression!
#guard_msgs in
example : True := by
  suffices
  True by
    trivial
  trivial

-- TODO: this *should* report the two double spaces surrounding `by`, but doesn't.
#guard_msgs in
example : True :=
  suffices True  by  refine ?_; trivial
  trivial

/--
warning: remove space in the source

This part of the code
  'refine  ?_;'
should be written as
  'refine ?_;'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example : True :=
  suffices True  by refine  ?_; trivial
  trivial

-- TODO: ideally, we could keep linting the contents of the `suffices`
#guard_msgs in
example {k : Int} (hk : k = 0) : k + k + k = 0 := by
  suffices
      h: k + k + k = 0
    from h
  simp [hk]

-- Explicit name literals: used to error (and the suggested replacement is invalid syntax).
example := ``Nat

-- The *linter* forces a space after `where`, but the pretty-printer does not.
variable (bool : Bool) in
/-- A doc-string -/
example := if bool then aux else aux
where
  /-- A separate doc-string -/
  aux : Unit := ()

/--
warning: unused variable `x`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: add space in the source

This part of the code
  'let(x)'
should be written as
  'let (x)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  'have(x)'
should be written as
  'have (x)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example : True :=
  let(x) : True := trivial
  have(x) : True := trivial
  x

-- For structure fields, all field definitions are linted.
/--
warning: remove space in the source

This part of the code
  'field1     :'
should be written as
  'field1 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure A where
  field1     : Nat
  field2 : Nat

/--
warning: remove space in the source

This part of the code
  'field2     :'
should be written as
  'field2 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure B where
  field1 : Nat
  field2     : Nat

/--
warning: remove space in the source

This part of the code
  ':     Nat'
should be written as
  ': Nat'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'field2     :'
should be written as
  'field2 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure C where
  field1 :     Nat
  field2     : Nat

-- Note that the linter does not attempt to recognise or respect manual alignment of fields:
-- this is often brittle and should usually be removed.
/--
warning: remove space in the source

This part of the code
  'field1    :'
should be written as
  'field1 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  ':     Nat'
should be written as
  ': Nat'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'field2    :'
should be written as
  'field2 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure D where
  field1    :     Nat
  field2    : Nat

-- This also applies to consecutive declarations.
/--
warning: declaration uses 'sorry'
---
warning: remove space in the source

This part of the code
  'instance   {R}'
should be written as
  'instance {R}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
instance   {R} : Add R := sorry

-- TODO: right now, defining a second private `Add` instance causes an error
-- Once the fix for lean4#11385 lands in mathlib; revert this to an `Add` instance
/--
warning: declaration uses 'sorry'
---
warning: remove space in the source

This part of the code
  'instance   {R}'
should be written as
  'instance {R}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
instance   {R} : Sub R := sorry

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

-- TODO: the linter is silenced on `inductive`s.
#guard_msgs in
/-- Symbols for use by all kinds of grammars. -/
inductive Symbol (T N : Type)
  /-- Terminal symbols (of the same type as the language) -/
  | terminal (t : T) : Symbol T N
  /-- Nonterminal symbols (must not be present when the word being generated is finalized) -/
  | nonterminal (n : N) : Symbol T N
deriving
  DecidableEq, Repr

/--
info: inductive A where/-- -/

  | _✝/-- -/

  | _✝
---
info: inductive A where
  | _✝
  | _✝
-/
#guard_msgs in
open Lean in
run_cmd
  let A := mkIdent `A
  let stx ← `(inductive $A where /-- -/| _ /-- -/ | _)
  logInfo stx
  let stx ← `(inductive $A where|_|_)
  logInfo stx

-- `inductive`s with internal docstrings have undesirable pretty-printing.
#guard_msgs in
inductive S
  /-- t -/
  | t   :    S
  /-- t -/
  | n : S

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

open Function in
theorem leftInverse_of_surjective_of_rightInverse {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx




open Function in
theorem leftInverse_of_surjective_of_rightInverse1 {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx



-- Test that `Prop` and `Type` that are not escaped with `«...»` do not cause problems.
def Prop.Hello := 0
def Type.Hello := 0

/--
warning: remove space in the source

This part of the code
  'F  :'
should be written as
  'F :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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
warning: The `whitespace` linter had some parsing issues: feel free to silence it and report this error!

Note: This linter can be disabled with `set_option linter.style.whitespace.verbose false`
-/
#guard_msgs in
set_option linter.style.whitespace.verbose true in
example {a : α} (_ : a ≼ a) : 0 = 0 := rfl

end List

end noFalsePositives

-- Miscellaneous constructs: variable, include, omit statements; aesop rulesets
section misc

-- TODO: cannot redeclare a private declaration A or B
/--
warning: remove space in the source

This part of the code
  'field1     :'
should be written as
  'field1 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure A' where
  field1     : Nat
  field2 : Nat

/--
warning: remove space in the source

This part of the code
  'field2     :'
should be written as
  'field2 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure B' where
  field1 : Nat
  field2     : Nat

/--
warning: remove space in the source

This part of the code
  ':     Nat'
should be written as
  ': Nat'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'field2     :'
should be written as
  'field2 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure C' where
  field1 :     Nat
  field2     : Nat

-- Note that the linter does not attempt to recognise or respect manual alignment of fields:
-- this is often brittle and should usually be removed.
/--
warning: remove space in the source

This part of the code
  'field1    :'
should be written as
  'field1 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  ':     Nat'
should be written as
  ': Nat'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'field2    :'
should be written as
  'field2 :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure D' where
  field1    :     Nat
  field2    : Nat

-- This also applies to consecutive declarations.
/--
warning: declaration uses 'sorry'
---
warning: remove space in the source

This part of the code
  'instance   {R}'
should be written as
  'instance {R}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
instance   {R} : Add R := sorry
/--
warning: declaration uses 'sorry'
---
warning: remove space in the source

This part of the code
  'instance   {R}'
should be written as
  'instance {R}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
instance   {R} : Add R := sorry

variable [h : Add Nat] [Add Nat]

/--
warning: remove space in the source

This part of the code
  'variable    ['
should be written as
  'variable [h'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '[ h'
should be written as
  '[h'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'h    :'
should be written as
  '[h :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove spaces in the source

This part of the code
  'Nat   ]'
should be written as
  'Nat]'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  '[ Add'
should be written as
  '[Add'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
variable    [ h    : Add Nat   ] [ Add Nat]

/--
warning: remove space in the source

This part of the code
  'omit  [h'
should be written as
  'omit [h'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  'Nat]  [Add'
should be written as
  'Nat] [Add'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
omit  [h : Add Nat]  [Add Nat]

/--
warning: remove space in the source

This part of the code
  'include     h'
should be written as
  'include h'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
include     h

/--
warning: remove space in the source

This part of the code
  '@[aesop  (rule_sets'
should be written as
  '@[aesop (rule_sets'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
@[aesop  (rule_sets := [builtin]) safe apply] example : True := trivial

end misc

-- TODO: should this warn? right now, it does not (any more?)
#guard_msgs in
 section

/--
warning: remove space in the source

This part of the code
  'example    :'
should be written as
  'example :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example    : True := trivial

/--
warning: remove space in the source

This part of the code
  ':     True'
should be written as
  ': True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example :     True := trivial

/--
warning: remove space in the source

This part of the code
  'example  :'
should be written as
  'example :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: remove space in the source

This part of the code
  ':  True'
should be written as
  ': True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  ':=trivial'
should be written as
  ':= trivial'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example  :  True :=trivial

/--
warning: add space in the source

This part of the code
  '(a:'
should be written as
  '(a :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
variable (a: Nat)

/--
warning: add space in the source

This part of the code
  '(_a:'
should be written as
  '(_a :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example (_a: Nat) : True := trivial

/--
warning: add space in the source

This part of the code
  '{a:'
should be written as
  '{a :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
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
warning: add space in the source

This part of the code
  ':Nat}'
should be written as
  ': Nat}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {a :Nat} : a = a := rfl

/--
warning: remove space in the source

This part of the code
  'example  {a'
should be written as
  'example {a'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: add space in the source

This part of the code
  ':Nat}'
should be written as
  ': Nat}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example  {a :Nat} : a = a := rfl

/--
warning: unused variable `b`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: add space in the source

This part of the code
  'Nat}{b'
should be written as
  'Nat} {b'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {a : Nat}{b : Nat} : a = a := rfl

/--
warning: remove space in the source

This part of the code
  'Nat}  :'
should be written as
  'Nat} :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {a : Nat}  : a = a := rfl

/--
warning: remove spaces in the source

This part of the code
  'alpha   ]'
should be written as
  'alpha]'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {alpha} [Neg alpha   ] {a : Nat} : a = a := rfl

/--
warning: remove space in the source

This part of the code
  'example  :'
should be written as
  'example :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
/-- Check that doc/strings do not get removed as comments. -/
example  : True := trivial
