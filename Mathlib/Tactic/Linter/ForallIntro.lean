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

open Lean Elab Command

/-- the `SyntaxNodeKind`s of `intro` and `intros`. -/
abbrev introTacs := #[``Lean.Parser.Tactic.intros, ``Lean.Parser.Tactic.intro]

/-- if the input is `have .. : ∀ ids : typs, ... := by intro(s)...`, then
it returns `(#[ids, typs], #[intro(s)])`, otherwise it returns `(#[], #[])`.
Note that `typs` could be `null`.
-/

def dropIntroVars : Syntax → Option Syntax
  | stx@(.node s1 k #[intr, .node s2 `null vars]) =>
    let varsDropFirst := vars.erase (vars.getD 0 .missing)
    let skipStx := none --some <| mkNode ``Lean.Parser.Tactic.skip #[mkAtom "skip"]
    let newIntro : Syntax :=  -- recreate `intro [one fewer variable]`, even if input is `intros`
      .node s1 ``Lean.Parser.Tactic.intro #[mkAtomFrom intr "intro", .node s2 `null varsDropFirst]
    match k, vars.size with
      | ``Lean.Parser.Tactic.intros, 0 =>
        stx -- `intros` stays `intros`
      | ``Lean.Parser.Tactic.intros, 1 =>
        skipStx -- `intros x` converts to `skip`
      | ``Lean.Parser.Tactic.intros, _ =>
        some newIntro -- `intros x ...` converts to `intro ...`
      | ``Lean.Parser.Tactic.intro, 0 | ``Lean.Parser.Tactic.intro, 1 =>
        skipStx -- `intro` and `intro x` convert to `skip`
      | ``Lean.Parser.Tactic.intro, _ =>
        some newIntro -- `intro x y ...` converts to `intro y ...`
      | _, _ => none
  | _ => none

def Term.dropOneIntro {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option Syntax)
  | `(by $first; $ts*) => do
    if introTacs.contains first.raw.getKind then
      match dropIntroVars first with
        | some newIntro =>
          let newtacs : Syntax.TSepArray `tactic "" :=
            { ts with elemsAndSeps := #[newIntro, mkNullNode] ++ ts.elemsAndSeps }
          let tacSeq ← `(tacticSeq| $[$newtacs]*)
          --logInfo m!"shortened '{first}': '{← `(term| by $tacSeq)}'"
          return some (← `(term| by $tacSeq))
        | none =>
          --logInfo m!"shortened '{first}': '{← `(term| by $[$ts]*)}'"
          return some (← `(term| by $[$ts]*))
    else
      return none
  | _ => return default

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

partial
def allStx (cmd stx : Syntax) : CommandElabM Syntax := do
  match ← allStxCore cmd stx with
    | none => return stx
    | some (cmd, stx) => allStx cmd stx

elab "fh " cmd:command : command => do
  elabCommand cmd
  let haves := cmd.raw.filter (·.isOfKind ``Lean.Parser.Tactic.tacticHave_)
  for stx in haves do
--  if let some stx := cmd.raw.find? (·.isOfKind ``Lean.Parser.Tactic.tacticHave_) then
    --dbg_trace "found have"
    let newHave ← allStx cmd stx
    --logInfo newHave
    let newCmd ← cmd.raw.replaceM fun s => do if s == stx then return some newHave else return none
    if cmd == newCmd then
      logInfo m!"No change needed"
    else
      logWarning m!"Please use\n---\n{newCmd}\n---"

-- and the test is successful!
/--
warning: declaration uses 'sorry'
---
warning: Please use
---
example : True :=
  by
  have (_ : Nat) x y : x + y = 0 := by
    refine ?_
    sorry
  trivial
---
-/
#guard_msgs in
fh
--inspect
example : True := by
  have (_ : Nat) : ∀ x y, x + y = 0 := by
    intros s t
    refine ?_
    sorry
  trivial

/--
warning: declaration uses 'sorry'
---
info: No change needed
-/
#guard_msgs in
fh
--inspect
example : True := by
  have (_ : Nat) : ∀ x y, x + y = 0 := by
    refine ?_
    sorry
  trivial

/--
warning: Please use
---
example : True := by
  have (n : Nat) : n = n := by rfl
  trivial
---
-/
#guard_msgs in
fh
--inspect
example : True := by
  have : ∀ (n : Nat), n = n := by
    intro s
    rfl
  trivial

/--
warning: declaration uses 'sorry'
---
warning: Please use
---
example : True :=
  by
  have (k : Nat) _ : ‹_› = k := by
    intros
    sorry
  trivial
---
-/
#guard_msgs in
fh
--inspect
example : True := by
  have :  ∀ (k : Nat), ∀ _, ‹_› = k := by
    intros
    sorry
  trivial
