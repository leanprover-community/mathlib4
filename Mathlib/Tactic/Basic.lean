/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Lean
import Mathlib.Tactic.PPWithUniv
import Mathlib.Tactic.ExtendDoc
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.OldObtain
import Mathlib.Tactic.Simproc.ExistsAndEq

/-!
# Basic tactics and utilities for tactic writing

This file defines some basic utilities for tactic writing, and also
- a dummy `variables` macro (which warns that the Lean 4 name is `variable`)
- the `introv` tactic, which allows the user to automatically introduce the variables of a theorem
and explicitly name the non-dependent hypotheses,
- an `assumption` macro, calling the `assumption` tactic on all goals
- the tactics `match_target` and `clear_aux_decl` (clearing all auxiliary declarations from the
context).
-/

namespace Mathlib.Tactic
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

/-- Syntax for the `variables` command: this command is just a stub,
and merely warns that it has been renamed to `variable` in Lean 4. -/
syntax (name := «variables») "variables" (ppSpace bracketedBinder)* : command

/-- The `variables` command: this is just a stub,
and merely warns that it has been renamed to `variable` in Lean 4. -/
@[command_elab «variables»] def elabVariables : CommandElab
  | `(variables%$pos $binders*) => do
    logWarningAt pos "'variables' has been replaced by 'variable' in lean 4"
    elabVariable (← `(variable%$pos $binders*))
  | _ => throwUnsupportedSyntax

/-- Given two arrays of `FVarId`s, one from an old local context and the other from a new local
context, pushes `FVarAliasInfo`s into the info tree for corresponding pairs of `FVarId`s.
Recall that variables linked this way should be considered to be semantically identical.

The effect of this is, for example, the unused variable linter will see that variables
from the first array are used if corresponding variables in the second array are used. -/
def pushFVarAliasInfo {m : Type → Type} [Monad m] [MonadInfoTree m]
    (oldFVars newFVars : Array FVarId) (newLCtx : LocalContext) : m Unit := do
  for old in oldFVars, new in newFVars do
    if old != new then
      let decl := newLCtx.get! new
      pushInfoLeaf (.ofFVarAliasInfo { id := new, baseId := old, userName := decl.userName })

/--
The tactic `introv` allows the user to automatically introduce the variables of a theorem and
explicitly name the non-dependent hypotheses.
Any dependent hypotheses are assigned their default names.

Examples:
```
example : ∀ a b : Nat, a = b → b = a := by
  introv h,
  exact h.symm
```
The state after `introv h` is
```
a b : ℕ,
h : a = b
⊢ b = a
```

```
example : ∀ a b : Nat, a = b → ∀ c, b = c → a = c := by
  introv h₁ h₂,
  exact h₁.trans h₂
```
The state after `introv h₁ h₂` is
```
a b : ℕ,
h₁ : a = b,
c : ℕ,
h₂ : b = c
⊢ a = c
```
-/
syntax (name := introv) "introv " (ppSpace colGt binderIdent)* : tactic
@[tactic introv] partial def evalIntrov : Tactic := fun stx ↦ do
  match stx with
  | `(tactic| introv)                     => introsDep
  | `(tactic| introv $h:ident $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro $h:ident; introv $hs:binderIdent*))
  | `(tactic| introv _%$tk $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro _%$tk; introv $hs:binderIdent*))
  | _ => throwUnsupportedSyntax
where
  introsDep : TacticM Unit := do
    let t ← getMainTarget
    match t with
    | Expr.forallE _ _ e _ =>
      if e.hasLooseBVars then
        intro1PStep
        introsDep
    | _ => pure ()
  intro1PStep : TacticM Unit :=
    liftMetaTactic fun goal ↦ do
      let (_, goal) ← goal.intro1P
      pure [goal]

/-- Try calling `assumption` on all goals; succeeds if it closes at least one goal. -/
macro "assumption'" : tactic => `(tactic| any_goals assumption)

elab "match_target " t:term : tactic => do
  withMainContext do
    let (val) ← elabTerm t (← inferType (← getMainTarget))
    if not (← isDefEq val (← getMainTarget)) then
      throwError "failed"

/-- This tactic clears all auxiliary declarations from the context. -/
elab (name := clearAuxDecl) "clear_aux_decl" : tactic => withMainContext do
  let mut g ← getMainGoal
  for ldec in ← getLCtx do
    if ldec.isAuxDecl then
      g ← g.tryClear ldec.fvarId
  replaceMainGoal [g]

attribute [pp_with_univ] ULift PUnit PEmpty

/-- Result of `withResetServerInfo`. -/
structure withResetServerInfo.Result (α : Type) where
  /-- Return value of the executed tactic. -/
  result? : Option α
  /-- Messages produced by the executed tactic. -/
  msgs    : MessageLog
  /-- Info trees produced by the executed tactic, wrapped in `CommandContextInfo.save`. -/
  trees   : PersistentArray InfoTree

/--
Runs a tactic, returning any new messages and info trees rather than adding them to the state.
-/
def withResetServerInfo {α : Type} (t : TacticM α) :
    TacticM (withResetServerInfo.Result α) := do
  let (savedMsgs, savedTrees) ← modifyGetThe Core.State fun st =>
    ((st.messages, st.infoState.trees), { st with messages := {}, infoState.trees := {} })
  Prod.snd <$> MonadFinally.tryFinally' t fun result? => do
    let msgs  ← Core.getMessageLog
    let ist   ← getInfoState
    let trees ← ist.trees.mapM fun tree => do
      let tree := tree.substitute ist.assignment
      let ctx := .commandCtx <| ← CommandContextInfo.save
      return InfoTree.context ctx tree
    modifyThe Core.State fun st =>
      { st with messages := savedMsgs, infoState.trees := savedTrees }
    return { result?, msgs, trees }

end Mathlib.Tactic

/-- A mathlib library note: the note's content should be contained in its doc-string. -/
def LibraryNote := Unit

open Lean in
/-- `library_note2 «my note» /-- documentation -/` creates a library note named `my note`
in the `Mathlib.LibraryNote` namespace, whose content is `/-- documentation -/`.
You can access this note using, for example, `#print Mathlib.LibraryNote.«my note»`.
-/
macro "library_note2 " name:ident ppSpace dc:docComment : command =>
  `($dc:docComment def $(mkIdent (Name.append `Mathlib.LibraryNote name.getId)) : LibraryNote := ())

open Lean Elab Command in
/-- Support the old `library_note "foo"` syntax, with a deprecation warning. -/
elab "library_note2 " name:str ppSpace dc:docComment : command => do
  logWarningAt name <|
    "deprecation warning: library_note2 now takes an identifier instead of a string.\n" ++
    "Hint: replace the double quotes with «french quotes»."
  let name := Name.mkSimple name.getString
  let stx ← `(library_note2 $(mkIdent name):ident $dc:docComment)
  elabCommandTopLevel stx

library_note2 «partially-applied ext lemmas»
/--
When possible, `ext` lemmas are stated without a full set of arguments. As an example, for bundled
homs `f`, `g`, and `of`, `f.comp of = g.comp of → f = g` is a better `ext` lemma than
`(∀ x, f (of x) = g (of x)) → f = g`, as the former allows a second type-specific extensionality
lemmas to be applied to `f.comp of = g.comp of`.
If the domain of `of` is `ℕ` or `ℤ` and `of` is a `RingHom`, such a lemma could then make the goal
`f (of 1) = g (of 1)`.

For bundled morphisms, there is a `ext` lemma that always applies of the form
`(∀ x, ⇑f x = ⇑g x) → f = g`. When adding type-specific `ext` lemmas like the one above, we want
these to be tried first. This happens automatically since the type-specific lemmas are inevitably
defined later.
-/
