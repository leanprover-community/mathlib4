/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.PrettyPrinter
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.PrettyPrinter.Delaborator.Builtins

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
true. Note that this differs from `checkCore` in making sure terms are always elaborated without
implicit arguments inserted, modifies the constructed message, lowers to `TermElabM`, and always
takes `ignoreStuckTC := true` (as `#check` does).

This declaration may realize constants, and so should be run without modifying the environment.

Info messages are placed at `tk`. In case there are several resolved names for `term`, show
information for the first of them. -/
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
  -- Elaborate without inserting implicit arguments
  let e ← Term.elabTerm (← `(term|@$term)) none
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
  -- Users might be testing out buggy elaborators. Let's typecheck before proceeding:
  withRef tk <| Meta.check e
  let e ← Term.levelMVarToParam (← instantiateMVars e)
  if e.isSyntheticSorry then
    return
  let type ← inferType e
  let type ← if showImplicit then pure m!"{type}" else
    delabForallWithSignatureWithoutImplicit type
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
        return ⟨← `(declSig| $binders* $binders'* : $type)⟩
      | _ => return ⟨← `(declSig| $binders* : $(← deleteImplicitArrowBinder type))⟩
    .ofFormatWithInfosM (PrettyPrinter.ppExprWithInfos (delab := delab) type)

  /-- Like `delabForallWithSignature`, but omits implicit binders. Also handles the case where
  `type` is already a `∀` correctly. -/
  delabForallWithSignatureWithoutImplicit (type : Expr) : TermElabM MessageData := do
    let isProp ← isProp type
    let delab : Delab := delabForallParamsWithSignature fun binders type => do
      let binders := binders.filter (·.raw.isOfKind ``Parser.Term.explicitBinder)
      -- `delabForallParamsWithSignature` may "stop early" if e.g. a binder is unnamed.
      let (binders', type) ← match type with
        | `(∀ $binders':bracketedBinder*, $type) =>
          pure (binders'.filter (·.raw.isOfKind ``Parser.Term.explicitBinder), type)
        | _ => pure (#[], ← deleteImplicitArrowBinder type)
      let binders := binders ++ binders'
      if binders.isEmpty then
        return type
      else if isProp && (← getPPOption getPPForalls) then
        `(∀ $binders*, $type)
      else
        binders.foldrM (fun binder acc => do
          return ⟨← `(Parser.Term.depArrow| $binder → $acc)⟩) type
    return .ofFormatWithInfosM (PrettyPrinter.ppExprWithInfos (delab := delab) type)

  /-- Given syntax for an arrow type `A₀ → A₁ → ⋯ → Aₙ`, removes every `Aᵢ` which is not a term or
  an explicit binder. -/
  deleteImplicitArrowBinder : Term → DelabM Term
    | `(Parser.Term.depArrow| $binder:bracketedBinder → $type) => do
      if binder.raw.isOfKind ``Parser.Term.explicitBinder then
        `(term| $binder:bracketedBinder → $(← deleteImplicitArrowBinder type))
      else
        deleteImplicitArrowBinder type
    | `($binder:term → $type) => do `($binder:term → $(← deleteImplicitArrowBinder type))
    | type => return type

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
-/
elab tk:"#check " colGt term:term : tactic => do
  withoutModifyingStateWithInfoAndMessages <| withMainContext <|
    checkCoreAux tk term (showImplicit := true)

/--
The `#check' t` tactic elaborates the term `t` and then pretty prints it with its type as `e : ty`.
In contrast to `#check t`, we only pretty-print explicit arguments, and omit implicit or type class
arguments.

If `t` is an identifier, then it pretty prints a type declaration form
for the global constant `t` instead.
Use `#check' (t)` to pretty print it as an elaborated expression.

Like the `#check'` command, the `#check'` tactic allows stuck typeclass instance problems.
These become metavariables in the output.
-/
elab tk:"#check' " colGt term:term : tactic => do
  withoutModifyingStateWithInfoAndMessages <| withMainContext <|
    checkCoreAux tk term (showImplicit := false)

end Mathlib.Tactic
