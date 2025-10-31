/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Init

/-
# Unused `Decidable*` hypotheses linter

This linter a declaration's type for `Decidable*` instance hypotheses which are not used in the
statement's type, and could therefore be replaced by `classical` in the proof.

Note that this linter is off by default for now.

## TODO

- It is awkward to both (1) only consider binders which are used in the resulting expression (and
  not, e.g., introduced by `variable`) and (2) associate binders used in the final expression with
  their originating syntax. But not impossible! We would want to:
  - look at the local context of the (single) `TermInfo` child of the `CustomInfo` node whose value
    is of type `Lean.Elab.Term.BodyInfo` and whose `parentDecl?` is the declaration in question.
  - Then, process these in the same way `elabMutualDef` does (i.e. with `withSectionFVars`, an
    unfortunately `private` definition).
  - Get the used fvars, search for them as expressions in the infotree, and *hope* that them
    appearing immediately subsequent to the `TermInfo` for their type is a real invariant and not
    something that just usually happens. (Why do we need to do this type? Because a binder like `
    [DecidableEq α]` creates an fvar `inst†` which is not recorded along with any position info in
    the infotree--only the type has source info. TODO: see how macro expansions in the type affect
    this.)
  - Match the syntax of the type (and its position info) to the command syntax so as to extract the
    full binder syntax (e.g. to get the syntax `[DecidableEq α]` from the syntax `Decidable Eq`)

  Whew! Ideally, Lean core eventually simply gives us more information to link the used binders
  with their source syntax, and all this becomes unnecessary.

- It would be nice to try to insert `classical` ourselves. The `bodyStx?` should be available in
  the snap for this purpose; we'd need to handle match alts and some other special syntax, though
  (e.g. how does a structure instance `where` work?).

- It would also be nice to re-elaborate to check that our suggestion actually works before
  suggesting it to the user. We might have to be careful here; we're halfway to `elabMutualDef` or
  similar, so maybe we could just try that. But we'd want to not maodify the environment (and more).

- Once feature-complete, this linter deserves a comprehensive "Implementation notes" section
  explaining the constraints that lead us to this specific (and somewhat unusual) design. It would
  have been nice to just use the infotrees or just use the command snap, but at this point in time
  Lean does not leave sufficient information in just one of them.
-/

open Lean Meta Elab Command Linter

/--
Gets the indices `i` of the binders of a nested `.forallE`, `(x₀ : A₀) → (x₁ : A₁) → ⋯ → X`,
such that
- `[xᵢ : Aᵢ]` has `instImplicit` `binderInfo`
-  `p Aᵢ` is `true`
- `Aᵢ₊₁ → ⋯ → X` does not depend on `xᵢ`. (It's in this sense that `xᵢ : Aᵢ` is "unused".)

This function runs `cleanupAnnotations` on each expression before examining it.

For performance, it also simply looks for loose bound variables to test dependence instead of
creating intermediate telescopes.
-/
private partial def Lean.Expr.getUnusedForallInstanceBinderIdxsWhere (p : Expr → Bool) (e : Expr) :
    Array Nat :=
  go e 0 #[]
where
  go (body : Expr) (current : Nat) (acc : Array Nat) : Array Nat :=
    match body.cleanupAnnotations with
    | .forallE _ type body bi => go body (current+1) <|
      if bi.isInstImplicit && p type && !(body.hasLooseBVar 0) then
        acc.push current
      else
        acc
    | _ => acc

namespace Mathlib.Linter.UnusedDecidable

/--
Returns `true` if `type` is an application of a `Decidable*` constant, or a forall with return type
a of the same form (i.e. of the form `∀ (x₀ : X₀) (x₁ : X₁) ⋯, Decidable* ..`). Specifically,
checks if the constant is one of: `DecidableEq`, `DecidableLE`, `DecidableLT`, `DecidableRel`,
`DecidablePred`, or `Decidable`.


Runs `cleanupAnnotations` on `type` and `forallE` bodies, and ignores metadata in applications.
-/
@[inline] partial def isAppOfDecidable (type : Expr) : Bool :=
    match type.cleanupAnnotations.getAppFn' with
    | .const n _ =>
      n == ``DecidableEq   ||
      n == ``DecidableLE   ||
      n == ``DecidableLT   ||
      n == ``DecidableRel  ||
      n == ``DecidablePred ||
      n == ``Decidable
    | .forallE _ _ body _ => isAppOfDecidable body
    | _ => false

/--
The `unusedDecidable` linter checks if a theorem's hypotheses include `Decidable*` instances which
are not used in the remainder of the type. If so, it suggests removing the instances and using
`classical` in the theorem's proof instead.

This linter fires on any declaration whose type is a `Prop`. It does not, however, fire on
subordinate `where` or `let rec` declarations.
-/
register_option linter.unusedDecidable : Bool := {
  defValue := false
  descr := "enable the unused `Decidable*` instance linter, which lints against `Decidable*` \
    instances in the hypotheses of theorems which are not used in the type and can therefore be \
    replaced with a use of `classical` in the proof."
}

/-- The linter for unused `Decidable*` hypotheses in proposition declarations. -/
def unusedDecidable : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.unusedDecidable (← getLinterOptions) do
      return
    for t in ← getInfoTrees do
      -- TODO: combine visits, since relevant term infos always come afterwards anyway
      -- TODO: check if some `Term.State` lets us see let recs to lift? Or jsut find names via def
      -- view?
      let some decls ← t.visitM
        (postNode := fun ctx i ch decls => do
          let decls := decls.reduceOption.flatten
          match i with
          | .ofCustomInfo i =>
            if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
              if let some decl := ctx.parentDecl? then
                let s := ctx.env
                return decl :: decls
              else return decls
            else return decls
          | _ => return decls)
        | return
      let env ← getEnv
      let vals? := decls.map env.findConstVal?
      liftTermElabM do for val? in vals? do
        if let some val := val? then
          unless (← inferType val.type).isProp do continue
          let unusedDecidableHyps :=
            val.type.getUnusedForallInstanceBinderIdxsWhere isAppOfDecidable
          unless unusedDecidableHyps.isEmpty do
            -- TODO: get syntax from infotrees for logging ref
            forallBoundedTelescope val.type (some <| unusedDecidableHyps.back! + 1)
              (cleanupAnnotations := true) fun fvars body => do
                let decidables ← unusedDecidableHyps.mapM fun idx =>
                  return m!"`[{← inferType fvars[idx]!}]`"
                logLint linter.unusedDecidable (← getRef) m!"\
                  `{.ofConstName val.name}` has the \
                  {if decidables.size = 1 then "hypothesis" else "hypotheses"} \
                  {.andList decidables.toList} which \
                  {if decidables.size = 1 then "is" else "are"} not used in the remainder of the \
                  type.\n\
                  Consider removing these hypotheses and using `classical` in the proof instead."

initialize addLinter unusedDecidable

end Mathlib.Linter.UnusedDecidable
