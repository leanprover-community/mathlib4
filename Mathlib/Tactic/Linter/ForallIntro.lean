/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
# Collapse `∀`/`intro` in `have`
-/

namespace Lean.Syntax
/-!
# `Syntax` filters
-/

partial
def filterMapM {m : Type → Type} [Monad m] (stx : Syntax) (f : Syntax → m (Option Syntax)) :
    m (Array Syntax) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

def filterMap (stx : Syntax) (f : Syntax → Option Syntax) : Array Syntax :=
  stx.filterMapM (m := Id) f

def filter (stx : Syntax) (f : Syntax → Bool) : Array Syntax :=
  stx.filterMap (fun s => if f s then some s else none)

end Lean.Syntax

/-!
#  The "forallIntro" linter

The "forallIntro" linter emits a warnings when it sees `have : ∀ ... := by intro(s) ...`.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The "forallIntro" linter emits a warnings when it sees `have : ∀ ... := by intro(s) ...`. -/
register_option linter.forallIntro : Bool := {
  defValue := true
  descr := "enable the forallIntro linter"
}
/-- the `SyntaxNodeKind`s of `intro` and `intros`. -/
abbrev introTacs := #[``Lean.Parser.Tactic.intros, ``Lean.Parser.Tactic.intro]

/-- `dropNIntroVar n stx` takes as input a natural number `n` and the `Syntax` `stx`.
If `stx` is not the tactic `intros ...` or `intro ...`, then it returns `(none, #[])`.
Otherwise, `dropNIntroVar` "removes the left-most `n` variable from `stx`", with the following
replacements:
· `0, anything`                  ↦ `(some anything,       #[])`;
· `n, intros`                    ↦ `(some intros,         #[])`;
· `n, intro`                     ↦ `(none,                #[])`;
· `n, intro x`                   ↦ `(none,                #[x])`;
· `n, intro(s) x₁ ... xₙ`        ↦ `(none,                #[x₁, ..., xₙ])`;
· `n, intro(s) x₁ ... xₙ y₁ ...` ↦ `(some (intro y₁ ...), #[x₁, ..., xₙ])`;

Note that only `intros` with no variable stays `intros`.
All remaining uses of `intros` convert to `none` or some use of `intro`.
-/
def dropNIntroVar : Nat → Syntax → Option Syntax × Array Syntax
  | n, stx@(.node s1 k #[intr, .node s2 `null vars]) =>
    if k == ``Lean.Parser.Tactic.intros && vars.isEmpty then (some stx, #[]) else
    if k == ``Lean.Parser.Tactic.intro  && vars.isEmpty && n == 1 then (none, #[.missing]) else
    let first := vars.extract 0 n
    let varsExtractN := vars.extract n vars.size
    let newIntro : Syntax :=  -- recreate `intro [n fewer variables]`, even if input is `intros`
      .node s1 ``Lean.Parser.Tactic.intro #[mkAtomFrom intr "intro", .node s2 `null varsExtractN]
    match k, (n + 1 ≤ vars.size : Bool) with
      | ``Lean.Parser.Tactic.intros, true => (some newIntro, first)
      | ``Lean.Parser.Tactic.intro,  true => (some newIntro, first)
      | _, _ => (none, first)
  | _, _ => (none, #[])

/-- `dropFirstIntroVar stx` is the specialization of `dropNIntroVar` to the case of dropping
just one variable.
The second `Array` component is an `Array` with at most one element and the function returns
either the unique entry there or `.missing`. -/
def dropFirstIntroVar (stx : Syntax) : Option Syntax × Syntax :=
  match dropNIntroVar 1 stx with
    | (intr, #[var]) => (intr, var)
    | (intr, _) => (intr, .missing)

def splitBinders {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Array Syntax)
  | `(bracketedBinder| ($as* : $b)) => as.mapM fun a => `(bracketedBinder| ($a : $b))
  | `(bracketedBinder| {$as* : $b}) => as.mapM fun a => `(bracketedBinder| {$a : $b})
  | `(bracketedBinder| ⦃$as* : $b⦄) => as.mapM fun a => `(bracketedBinder| ⦃$a : $b⦄)
  | _ => return #[]

/-- if the input syntax is not `by intro(s); ...`, then it returns `none`.
Otherwise, it removes one identifier introduced by `intro(s)` and returns the resulting syntax. -/
def Term.dropOneIntro {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option (Syntax × Syntax))
  | `(by $first; $ts*) => do
    if introTacs.contains first.raw.getKind then
      match dropFirstIntroVar first with
        | (some newIntro, var) =>
          let newtacs : Syntax.TSepArray `tactic "" :=
            { ts with elemsAndSeps := #[newIntro, mkNullNode] ++ ts.elemsAndSeps }
          let tacSeq ← `(tacticSeq| $[$newtacs]*)
          return some (← `(term| by $tacSeq), var)
        | (none, var) =>
          return some (← `(term| by $[$ts]*), var)
    else
      return none
  | _ => return none

/--
`recombineBinders ts1 ts2` takes as input two `TSyntaxArray`s and removes the first entry of the
second array and pushes it to the last array.
Implicitly, it forces an update of the `SyntaxNodeKinds` with no check on type correctness:
we leave this check to the elaboration of the produced syntax in a later step.

In the intended application of `recombineBinders`, the `SyntaxNodeKinds` are
* ``ks1 = `Lean.Parser.Term.letIdBinder``,
* ``ks2 = [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]``.

The corresponding `TSyntaxArray`s are
* the identifiers `id₁ id₂ ...` appearing in a `have this id₁ id₂ ...` tactic, and
* the variables bound in a `∀` quantifiers.
-/
def recombineBinders {ks1 ks2 : SyntaxNodeKinds} (ts1 : TSyntaxArray ks1) (ts2 : TSyntaxArray ks2) :
    Option (TSyntaxArray ks1 × TSyntaxArray ks2 × Syntax) :=
  if h : 0 < ts2.size then
    let first := ts2[0]
    (ts1.push ⟨first.raw⟩, ts2.erase first, first.raw)
  else
    none

/--
`allStxCore cmd stx` takes two `Syntax` inputs `cmd` and `stx`.
If `stx` is not a `have` tactic whose type does not begin with a `∀` binder, or whose
proof does not start with `:= by intro(s)`, then it returns none.
Otherwise, it moves one variable bound by `∀` "to the left of `:`", it removes one variable
bound by `intro(s)`.
Next, it replaces `stx` inside `cmd` with the cleaned up `have` statement and elaborates
the resulting syntax.
If the result does not elaborate, then it returns none.
If the result elaborates successfully, then it returns the pair consisting of
the replaced `cmd` and the new `stx`.
-/
def allStxCore (cmd : Syntax) : Syntax → CommandElabM (Option (Syntax × Syntax))
  | stx@`(tactic| have $id:haveId $bi1* : ∀ $bi2*, $body := $t) => do
    let spreadBi2 := ← bi2.mapM fun b => do
      let spb ← splitBinders b; if spb.isEmpty then return #[b] else return spb
    match recombineBinders bi1 (spreadBi2.flatten.map (⟨·⟩)) with
      | none => return none  -- if we ran out of `∀`, then we are done
      | some (bi1', bi2', forallVar) =>
        match ← Term.dropOneIntro t with
          | none => return none  -- if we ran out of `intro(s)`, then we are done
          | some (t', introVar) =>
            --dbg_trace "forallVar: {forallVar}\nintroVar: {introVar}\n"
            let newHave := ←
              if bi2'.isEmpty then
                `(tactic| have $id:haveId $[$bi1']* : $body := $(⟨t'⟩))
              else
                `(tactic| have $id:haveId $[$bi1']* : ∀ $[$bi2']*, $body := $(⟨t'⟩))
            let newCmd ← cmd.replaceM fun s => do
              if s == stx then return some newHave else return none
            let newCmd ← newCmd.replaceM fun s => do
              if s.isOfKind ``Lean.Parser.Command.declId then
                let x ← liftTermElabM mkFreshId
                return some (← `(declId | $(mkIdent x))) else return none
            let s ← modifyGet fun st => (st, { st with messages := {} })
            withoutModifyingEnv do elabCommand newCmd
            let msgs ← modifyGet (·.messages, s)
            if msgs.hasErrors then
              let errs := msgs.unreported.filter (·.severity matches .error)
              for err in errs.toArray do
                logInfo m!"{← err.toString}"
              let ids := [forallVar, introVar].map (·.filter (·.isOfKind `ident))
              let i0 := ids[0]!.getD 0 default
              let i1 := ids[1]!.getD 0 default
              if i0 != i1 then
                logWarningAt i0 m!"rename '{i0}' to '{i1}'..."
                logWarningAt i1  m!"... or rename '{i1}' to '{i0}'?"
              return none
            else
              return some (newCmd, newHave)
  | _ => return none

/-- `allStx cmd stx` repeatedly applies `allStxCore`, until it returns `none`.
When that happens, `allStx` returns the "new `have` syntax" that was produced by `allStxCore`
on the step prior to returning `none`. -/
partial
def allStx (cmd stx : Syntax) (count : Nat) : CommandElabM (Syntax × Nat) := do
  match ← allStxCore cmd stx with
    | none => return (stx, count)
    | some (cmd, stx) => allStx cmd stx (count + 1)

namespace ForallIntro

/-- Gets the value of the `linter.forallIntro` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.forallIntro o

@[inherit_doc Mathlib.Linter.linter.forallIntro]
def forallIntroLinter : Linter where run := withSetOptionIn fun cmd ↦ do
  unless getLinterHash (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let haves := cmd.filter (·.isOfKind ``Lean.Parser.Tactic.tacticHave_)
  for haveStx in haves do
--  if let some haveStx := cmd.raw.find? (·.isOfKind ``Lean.Parser.Tactic.tacticHave_) then
    --dbg_trace "found have"
    let (newHave, _count) ← allStx cmd haveStx 0
    --dbg_trace "extracted {count} binders"
    if haveStx != newHave then
      Linter.logLint linter.forallIntro haveStx m!"replace{indentD haveStx}\nwith{indentD newHave}"
    --logInfo newHave
--    let newCmd ← cmd.replaceM fun s => do if s == haveStx then return some newHave else return none
--    if cmd != newCmd then
--      logInfo m!"No change needed"
--    else
--      Linter.logLint linter.forallIntro haveStx m!"Please use\n---\n{newCmd}\n---"

initialize addLinter forallIntroLinter

end ForallIntro

end Mathlib.Linter
