import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Defs
import Mathlib.adomaniLeanUtils.inspect_syntax
import Batteries.Data.Array.Basic
import Mathlib.Tactic

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

/-- `dropIntroVars stx` takes as input the `Syntax` `stx`.
If `stx` is not the tactic `intros ...` or `intro ...`, then it returns `none`.
Otherwise, `dropIntroVars` "removes the left-most variable from `stx`", with the following
replacements:
· `intros`        ↦ `some intros`;
· `intros x`      ↦ `none`;
· `intros x ...`  ↦ `intro ...`;
· `intro`         ↦ `none`;
· `intro x`       ↦ `none`;
· `intro x y ...` ↦ `intro y ...`.

Note that only `intros` with no variable stays `intros`.
All remaining used of `intros` convert to `none` or some use of `intro`.
-/
def dropIntroVars : Syntax → Option Syntax
  | stx@(.node s1 k #[intr, .node s2 `null vars]) =>
    let varsDropFirst := vars.erase (vars.getD 0 .missing)
    let newIntro : Syntax :=  -- recreate `intro [one fewer variable]`, even if input is `intros`
      .node s1 ``Lean.Parser.Tactic.intro #[mkAtomFrom intr "intro", .node s2 `null varsDropFirst]
    match k, vars.size with
      | ``Lean.Parser.Tactic.intros, 0  => stx
      | ``Lean.Parser.Tactic.intros, 1  => none
      | ``Lean.Parser.Tactic.intros, _  => some newIntro
      | ``Lean.Parser.Tactic.intro, 0 |
        ``Lean.Parser.Tactic.intro, 1   => none
      | ``Lean.Parser.Tactic.intro, _   => some newIntro
      | _, _ => none
  | _ => none

/-- if the input syntax is not `by intro(s); ...`, then it returns `none`.
Otherwise, it removes one identifier introduced by `intro(s)` and returns the resulting syntax. -/
def Term.dropOneIntro {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option Syntax)
  | `(by $first; $ts*) => do
    if introTacs.contains first.raw.getKind then
      match dropIntroVars first with
        | some newIntro =>
          let newtacs : Syntax.TSepArray `tactic "" :=
            { ts with elemsAndSeps := #[newIntro, mkNullNode] ++ ts.elemsAndSeps }
          let tacSeq ← `(tacticSeq| $[$newtacs]*)
          return some (← `(term| by $tacSeq))
        | none =>
          return some (← `(term| by $[$ts]*))
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
    Option (TSyntaxArray ks1 × TSyntaxArray ks2) :=
  if h : 0 < ts2.size then
    let first := ts2[0]
    (ts1.push ⟨first.raw⟩, ts2.erase first)
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
* the replaced `cmd` and the new `stx`.
-/
def allStxCore (cmd : Syntax) : Syntax → CommandElabM (Option (Syntax × Syntax))
  | stx@`(tactic| have $id:haveId $bi1* : ∀ $bi2*, $body := $t) => do
    match recombineBinders bi1 bi2 with
      | none => return none  -- if we ran out of `∀`, then we are done
      | some (bi1', bi2') =>
        let newTerm? := ← Term.dropOneIntro t
        match newTerm? with
          | none => return none  -- if we ran out of `intro(s)`, then we are done
          | some t' =>
            let newHave := ←
              if bi2'.isEmpty then
                `(tactic| have $id:haveId $[$bi1']* : $body := $(⟨t'⟩))
              else
                `(tactic| have $id:haveId $[$bi1']* : ∀ $[$bi2']*, $body := $(⟨t'⟩))
            let newCmd ← cmd.replaceM fun s => do
              if s == stx then return some newHave else return none
            let s ← modifyGet fun st => (st, { st with messages := {} })
            elabCommandTopLevel newCmd
            let msgs ← modifyGet (·.messages, s)
            if msgs.hasErrors then
              let errs := msgs.unreported.filter (·.severity matches .error)
              logInfo m!"{← errs.toArray.mapM (·.toString)}"
              return none
            else
              return some (newCmd, newHave)
  | _ => return none

/-- `allStx cmd stx` repeatedly applies `allStxCore`, until it returns `none`.
When that happens, `allStx` returns the "new `have` syntax" that was produced by `allStxCore`
on the step prior to returning `none`. -/
partial
def allStx (cmd stx : Syntax) : CommandElabM Syntax := do
  match ← allStxCore cmd stx with
    | none => return stx
    | some (cmd, stx) => allStx cmd stx

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
  for stx in haves do
--  if let some stx := cmd.raw.find? (·.isOfKind ``Lean.Parser.Tactic.tacticHave_) then
    --dbg_trace "found have"
    let newHave ← allStx cmd stx
    --logInfo newHave
    let newCmd ← cmd.replaceM fun s => do if s == stx then return some newHave else return none
    if cmd != newCmd then
--      logInfo m!"No change needed"
--    else
      Linter.logLint linter.forallIntro stx m!"Please use\n---\n{newCmd}\n---"

initialize addLinter forallIntroLinter

end ForallIntro

end Mathlib.Linter
