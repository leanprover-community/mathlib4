/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public meta import Lean.Elab.Command
meta import Lean.PrettyPrinter.Delaborator.Builtins
import Mathlib.Init

/-!
# `#check` tactic

This module defines a tactic version of the `#check` command.
While `#check t` is similar to `have := t`, it is a little more convenient
since it elaborates `t` in a more tolerant way and so it can be possible to get a result.
For example, `#check` allows metavariables.

This module also defines the `#check'` tactic and command, which behaves like `#check` but only
shows explicit arguments in the signature.
-/

meta section

open Lean Elab Meta Tactic Command

namespace Mathlib.Tactic

open Command PrettyPrinter Delaborator in
/-- Like `checkCore`, but logs different messages depending on whether `showImplicit` is
true. Note that this differs from `checkCore` only in that it modifies the constructed message,
lowers to `TermElabM`, and always takes `ignoreStuckTC := true` (as `#check` ultimately does).

This declaration may realize constants, and so should be run without modifying the environment.

Info messages are placed at `tk`. If there are several resolved names for `term`, shows
information only for the first of them instead of failing. -/
partial def checkCoreAux (tk : Syntax) (term : Term) (showImplicit : Bool) : TermElabM Unit :=
  Term.withDeclName `_check do
  -- show signature for `#check id`/`#check @id`
  if let `($id:ident) := term then
    try
      for c in (← realizeGlobalConstWithInfos term) do
        addCompletionInfo <| .id term id.getId (danglingDot := false) {} none
        logInfoAt tk <|← do if showImplicit then pure <| .signature c else
          pure <| m!"{.ofConstName c}{delabSignatureWithoutImplicit (← getConstInfo c).type}"
        return
    catch _ => pure ()  -- identifier might not be a constant but constant + projection
  -- TODO: handle expressions in `#check'`. Currently it behaves the same as `#check` here.
  let e ← Term.elabTerm term none
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
  -- Users might be testing out buggy elaborators. Let's typecheck before proceeding:
  withRef tk <| Meta.check e
  let e ← Term.levelMVarToParam (← instantiateMVars e)
  if e.isSyntheticSorry then
    return
  let type ← inferType e
  logInfoAt tk m!"{e} : {type}"
where
  /-- Delaborates `type` as ` binders* : returnType`. Note the leading space; this means that we
  ought to put `{.ofConstName c}` directly before it. Note: this strategy gives us hover
  information on `c`, allowing the user to inspect the full type signature if they wish. -/
  delabSignatureWithoutImplicit (type : Expr) : MessageData :=
    let delab : Delab := delabForallParamsWithSignature fun binders type => do
      let binders := binders.filter (·.raw.isOfKind ``Parser.Term.explicitBinder)
      -- `delabForallParamsWithSignature` may "stop early" if e.g. a binder is unnamed.
      match type with
      | `(∀ $binders'*, $type) =>
        let binders' := binders'.filter (·.raw.isOfKind ``Parser.Term.explicitBinder)
        -- Note: this is a "dangerous" use of `TSyntax.mk`. See also `delabConstWithSignature`.
        return ⟨← `(declSig| $binders* $binders'* : $type)⟩
      -- TODO: handle `_ → {_ : _} → ⋯`
      | _ => return ⟨← `(declSig| $binders* : $type)⟩
    .ofFormatWithInfosM (PrettyPrinter.ppExprWithInfos (delab := delab) type)

/-- The `#check'` command is like `#check`, but only prints explicit arguments in the signature
(i.e., omitting implicit and typeclass arguments). -/
elab tk:"#check' " t:term : command => withoutModifyingEnv <| runTermElabM fun _ => do
  checkCoreAux tk t (showImplicit := false)

/--
`#check t` elaborates the term `t` and then pretty prints it with its type as `e : ty`.

If `t` is an identifier, then it pretty prints a type declaration form
for the global constant `t` instead.
Use `#check (t)` to pretty print it as an elaborated expression.

Like the `#check` command, the `#check` tactic allows stuck typeclass instance problems.
These become metavariables in the output.

To display only explicit arguments in the type signature, see `#check'`.
-/
elab tk:"#check " colGt term:term : tactic => do
  withoutModifyingStateWithInfoAndMessages <| withMainContext <|
    checkCoreAux tk term (showImplicit := true)

/--
The `#check' t` tactic elaborates the term `t` and then pretty prints it with its type as `e : ty`.
In contrast to `#check t`, we only pretty-print explicit arguments, and omit implicit or type class
arguments. Currently this only works when `t` is the name of a declaration.

If `t` is an identifier, then it pretty prints a type declaration form
for the global constant `t` instead.
Use `#check' (t)` to pretty print it as an elaborated expression.

Like other `#check` commands, the `#check'` tactic allows stuck typeclass instance problems.
These become metavariables in the output.
-/
elab tk:"#check' " colGt term:term : tactic => do
  withoutModifyingStateWithInfoAndMessages <| withMainContext <|
    checkCoreAux tk term (showImplicit := false)

end Mathlib.Tactic
