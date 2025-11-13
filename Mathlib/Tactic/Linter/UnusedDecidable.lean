/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Init
import Mathlib.Data.String.Defs
import Mathlib.Tactic.Lemma
import Batteries
import Qq

/-! efeg -/

open Qq Lean Meta

run_meta do
  let e := q(∀ (x : Nat), let i := String; ∀ (y : i), y.length = x)
  forallBoundedTelescope e (some 2) fun fvars body => logInfo m!"{fvars}\n{body}"

/-!
# Unused `Decidable*` hypotheses linter

This linter a declaration's type for `Decidable*` instance hypotheses which are not used in the
statement's type, and could therefore be replaced by `classical` in the proof.

Note that this linter is off by default for now.

## TODO

- It is awkward to associate binders used in the final expression with their originating syntax.
  But not impossible! We would want to:
  - look at the local context of the (single) `TermInfo` child of the `CustomInfo` node whose value
    is of type `Lean.Elab.Term.BodyInfo` and whose `parentDecl?` is the declaration in question.
  - Then, process these in the same way `elabMutualDef` does (i.e. with `withHeaderSecVars`, an
    unfortunately `private` definition).
  - Get the used fvars, search for them as expressions in the infotree, and *hope* that them
    appearing immediately subsequent to the `TermInfo` for their type is a real invariant and not
    something that just usually happens. (Why do we need this? Because a binder like
    `[DecidableEq α]` creates an fvar `inst†` which is not recorded along with any position info in
    the infotree--only the type has source info. TODO: see how macro expansions in the type affect
    this. Also see what `include` does to the infotrees, if anything.)
  - Match the syntax of the type (and its position info) to the command syntax so as to extract the
    full binder syntax (e.g. to get the syntax `[DecidableEq α]` from the syntax `Decidable Eq`)

  Whew! Ideally, Lean core eventually simply gives us more information to link the used binders
  with their source syntax, and all this becomes unnecessary.

  Or...we could restrict to `theorem`s in the first place. `theorem`s have the variables unused in the type excluded from the context of the `BodyInfo`.

- It would be nice to try to insert `classical` ourselves. It might be worth creating API for
  matching against all the necessary syntax here--or, maybe getting to `mkDefView` is sufficient.

- It would also be nice to re-elaborate to check that our suggestion actually works before
  suggesting it to the user. We might have to be careful here; we're halfway to `elabMutualDef` or
  similar, so maybe we could just try that. But we'd want to be careful to do it correctly, and
  avoid any issues arising from the fact that the declaration has already been elaborated.

- Technical: be sure to exclude implementation details when access fvarIds. Also
-/

open Lean Meta Elab Command Linter

/-
# Plan

## v1
- Logs on the signature if possible.
- provides restricted combinator.
-
-/

partial def Lean.Syntax.findSomeAux {α} (p : Syntax → Option α) : Syntax → Option α
  | stx@(.node _ _ args) => p stx <|> args.findSome? (findSomeAux p)
  | stx                  => p stx

def Lean.Syntax.findSome? {α} (stx : Syntax) (p : Syntax → Option α) : Option α :=
  findSomeAux p stx

/--
Gets the indices `i` of the binders of a nested `.forallE`, `(x₀ : A₀) → (x₁ : A₁) → ⋯ → X`,
such that
- `[xᵢ : Aᵢ]` has `instImplicit` `binderInfo`
-  `p Aᵢ` is `true`
- `Aᵢ₊₁ → ⋯ → X` does not depend on `xᵢ`. (It's in this sense that `xᵢ : Aᵢ` is "unused".)

Note that the argument to `p` may have loose bvars. This is a performance optimization.

This function runs `cleanupAnnotations` on each expression before examining it.

We see through `let`s, and do not increment the index when doing so. This behavior is compatible
with `forallBoundedTelescope`.
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
    /- See through `letE`, and just as in the interpretation of a bound provided to
    `forallBoundedTelescope`, do not increment the number of binders we've counted. -/
    | .letE _ _ _ body _ => go body current acc
    | _ => acc

namespace Lean.Elab.InfoTree

/--
Get the `parentDecl`s of every elaborated body. This includes `let rec`/`where`
definitions. Assumes that every declaration elaboration proceeds through `Lean.Elab.Term.BodyInfo`.
-/
def getDecls (t : InfoTree) : List Name :=
  t.collectNodesBottomUp fun ctx i _ decls =>
    match i with
    | .ofCustomInfo i =>
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
        if let some decl := ctx.parentDecl? then
          decl :: decls
        else decls
      else decls
    | _ => decls

-- Id.run do
--   let some decls ← t.visitM
--     (postNode := fun ctx i _ decls => do
--       let decls := decls.reduceOption.flatten
--       match i with
--       | .ofCustomInfo i =>
--         if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
--           if let some decl := ctx.parentDecl? then
--             return decl :: decls
--           else return decls
--         else return decls
--       | _ => return decls)
--     | return []
--   return decls

partial def findSome? {α} (f : ContextInfo → Info → PersistentArray InfoTree → Option α)
    (t : InfoTree) (ctx? : Option ContextInfo := none) : Option α :=
  go ctx? t
where go ctx?
  | context ctx t => go (ctx.mergeIntoOuter? ctx?) t
  | node i ts =>
    let a := match ctx? with
      | none => none
      | some ctx => f ctx i ts
    a <|> ts.findSome? (go <| i.updateContext? ctx?)
  | hole _ => none

/--
Given a constant name, find the first `TermInfo` whose expression is exactly that constant. Does
not resolve names.
-/
def getTermInfoForConst? (t : InfoTree) (decl : Name) : Option TermInfo :=
  t.findSome? fun
    | .ofTermInfo ti => if ti.expr.isConstOf decl then some ti else none
    | _ => none

/-- Get the syntax for the first occurrence of `decl` as the expression of some `TermInfo`. -/
def getConstRef? (t : InfoTree) (decl : Name) : Option Syntax :=
  t.getTermInfoForConst? decl |>.map (·.stx)


end Lean.Elab.InfoTree

def _root_.Lean.Syntax.rangeEq? (stx₁ stx₂ : Syntax) (canonicalOnly₁ canonicalOnly₂ := true) :
    Option Bool :=
  match stx₁.getRange? canonicalOnly₁, stx₂.getRange? canonicalOnly₂ with
  | some r₁, some r₂ => r₁ == r₂
  | _, _ => none

def _root_.Lean.Syntax.rangeEq (stx₁ stx₂ : Syntax) (canonicalOnly₁ canonicalOnly₂ := true) :
    Bool :=
  match stx₁.getRange? canonicalOnly₁, stx₂.getRange? canonicalOnly₂ with
  | some r₁, some r₂ => r₁ == r₂
  | _, _ => false

def _root_.Lean.Syntax.hasRange (stx : Syntax) (range : String.Range) (canonicalOnly := true) : Bool :=
  stx.getRange? canonicalOnly |>.map (· == range) |>.getD false



private def Lean.Elab.InfoTree.withDeclSigRef {m : Type → Type} [Monad m] [MonadRef m] {α} (cmd : Syntax)
    (t : InfoTree) (decl : Name) (x : m α) : m α := withRef cmd do
  let some idRef := t.getConstRef? decl | x
  let sigRef? := cmd.findSome? fun
    | `(Parser.Command.theorem| theorem $id$[.{$_,*}]? $sig:declSig $_:declVal)
    | `(«lemma»| lemma $id$[.{$_,*}]? $sig:declSig $_:declVal) =>
      if id.raw.rangeEq idRef then sig else none
    -- TODO: handle `let rec` decls (after `where`), handle defs etc.
    | _ => none
  -- Fall back to `idRef` if `sigRef` is not found or has no position info.
  withRef idRef <| withRef? sigRef? x

/-
# Next up:

- extract the fvarids from the local context of the node
- head back up the tree and get the instance type syntax via cursed infotree traversal
- compare ranges in the `TheoremViewSyntax` to find syntax and/or realize that it's to the right of the `:`, or elsewhere entirely
- adjust body as appropriate, matching on `by` or not, and checking for `classical`/`open scoped Calssical in` before inserting it

-/


namespace Mathlib.Linter.UnusedDecidable

/--
Returns `true` if `type` is an application of a `Decidable*` constant, or a forall with return type
a of the same form (i.e. of the form `∀ (x₀ : X₀) (x₁ : X₁) ⋯, Decidable* ..`). Specifically,
checks if the constant is one of: `DecidableEq`, `DecidableLE`, `DecidableLT`, `DecidableRel`,
`DecidablePred`, or `Decidable`.

Runs `cleanupAnnotations` on `type` and `forallE` bodies, and ignores metadata in applications.
-/
@[inline] partial def isAppOrForallOfConstP (p : Name → Bool) (type : Expr) : Bool :=
    match type.cleanupAnnotations.getAppFn' with
    | .const n _ => p n
    | .forallE _ _ body _ => isAppOrForallOfConstP p body
    | _ => false

@[inline] partial def isAppOrForallOfConst (declName : Name) (type : Expr) : Bool :=
  isAppOrForallOfConstP (· == declName) type

def isDecidableVariant (type : Expr) : Bool :=
  isAppOrForallOfConstP (type := type) fun n =>
    n == ``DecidableEq   ||
    n == ``DecidableLE   ||
    n == ``DecidableLT   ||
    n == ``DecidableRel  ||
    n == ``DecidablePred ||
    n == ``Decidable

class Foo : Prop where
  x : 0 = 0

instance : Foo := ⟨rfl⟩

run_cmd do
  let some info := (← getEnv).findAsync? ``instFoo | throwError "aa"
  logInfo m!"{info.kind matches .thm}"



/--
The `unusedDecidable` linter checks if a theorem's hypotheses include `Decidable*` instances which
are not used in the remainder of the type. If so, it suggests removing the instances and using
`classical` in the theorem's proof instead.

This linter fires on any declaration whose type is a `Prop`.
-/
register_option linter.unusedDecidable : Bool := {
  defValue := false
  descr := "enable the unused `Decidable*` instance linter, which lints against `Decidable*` \
    instances in the hypotheses of theorems which are not used in the type, and can therefore be \
    replaced with a use of `classical` in the proof."
}

def _root_.Nat.pluralizing (count : Nat) (singular plural : MessageData) : MessageData :=
  if count = 1 then singular else plural

def _root_.Lean.MessageData.pluralizing (count : Nat) (singular plural : MessageData) : MessageData :=
  if count = 1 then singular else plural

def _root_.String.withPlural (singular plural : String) (count : Nat) : String :=
  if count = 1 then singular else plural

def _root_.Lean.Environment.findTheoremAsync? (env : Environment) (decl : Name) :
    Option ConstantVal := do
  let info ← env.findAsync? decl
  if info.kind matches .thm then info.toConstantVal else none

def _root_.Lean.Elab.InfoTree.getTheorems (t : InfoTree) (env : Environment) : List ConstantVal :=
  t.getDecls.filterMap env.findTheoremAsync?


-- def _root_.Lean.Elab.InfoTree.getTheorems (t : InfoTree) (env : Environment) : List ConstantVal :=
--   t.getDecls.filterMap fun decl => do
--     let info ← env.findAsync? decl
--     if info.kind matches .thm then info.toConstantVal else none




structure Parameter where
  /- TODO: include syntax references to the binders here, and use the "real" fvars created during
  elaboration if possible -/
  /-- The free variable of the parameter created in a telescope for logging. -/
  fvar? : Option Expr
  /-- The type of the parameter created in a telescope for logging. -/
  type? : Option Expr
  /-- The index of the parameter among the `forall` binders in the type (starting at 1). -/
  idx : Nat

instance : ToMessageData Parameter where
  toMessageData (param : Parameter) :=
    if let some type := param.type? then
      m!"`[{type}]` (#{param.idx})"
    else
      m!"parameter #{param.idx}"

/-- Given a (full, resolvable) declaration name `foo` and an array of parameters
`#[p₁, p₂, ..., pₙ]`, constructs the message:
> \`{foo}\` has the hypothes(is/es) {p₁}, {p₂}, ..., and {pₙ} which (is/are) not used in the
  remainder of the type.
-/
def _root_.Lean.Name.unusedInstancesMsg (declName : Name)
    (unusedInstanceBinders : Array Parameter) : MessageData :=
  let unusedInstanceBinders := unusedInstanceBinders.map toMessageData
  m!"`{.ofConstName declName}` has the \
  {"hypothesis".withPlural "hypotheses" unusedInstanceBinders.size} \
  {.andList unusedInstanceBinders.toList} which \
  {"is".withPlural "are" unusedInstanceBinders.size} not used in the remainder of the type."


def _root_.Lean.Elab.InfoTree.onFirstNode {α} (t : InfoTree)
    (f : ContextInfo → Info → PersistentArray InfoTree → α) (ctx? : Option ContextInfo := none) :
    Option α :=
  t.findSome? (ctx? := ctx?) fun ctx i ch => some (f ctx i ch)

/-- Finds the local context of the body of `decl` by looking for the the child of the first
`Elab.Term.BodyInfo` in the infotree `t`, and getting the local context of the `TacticInfo` or
`TermInfo` present there.

Returns `none` if no `BodyInfo` node with `parentDecl?` `decl` is found; returns `.undef` if it is
found, but the `InfoTree` or the `Info`s therein have an unexpected structure. -/
def getLCtxOfDeclBody? (t : InfoTree) (decl : Name) (ctx? : Option ContextInfo := none) :
    LOption LocalContext :=
  -- Return `Option (Option LocalContext)`, with failures:
  -- `none` ↦ `LOption.none`: declaration not found
  -- `some none` ↦ `LOption.undef`: unexpected infotree structure
  let lctx?? := t.findSome? (ctx? := ctx?) fun ctx i ch =>
    match i with
    | .ofCustomInfo i =>
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo && ctx.parentDecl? == some decl then
        if let some body := ch[0]? then
          body.onFirstNode (ctx? := ctx) fun _ i _ =>
            match i with
            | .ofTermInfo ti => some ti.lctx
            | .ofTacticInfo ti => match ti.goalsBefore with
              | [mvarId] => some (ti.mctxBefore.getDecl mvarId).lctx
              | _ => none -- Not exactly one goal at body (Wrapped in `some` by `onFirstNode`)
            | _ => none -- Unexpected child of body (Wrapped in `some` by `onFirstNode`)
          else some none -- No body node
      else none
    | _ => none
  match lctx?? with
  | none => .none
  | some none => .undef
  | some (some lctx) => .some lctx

partial def _root_.Lean.Elab.InfoTree.forIn.{u₁,u₂} {m : Type u₁ → Type u₂}
    {β : Type u₁} [Monad m] (x : InfoTree) (b : β)
    (f : (ContextInfo × Info × PersistentArray InfoTree) → β → m (ForInStep β)) : m β :=
  return (← go none b x).run
where
  go ctx? b : InfoTree → m (ForInStep β)
  | .context ctx t => go (ctx.mergeIntoOuter? ctx?) b t
  | .node i ch => do
      let bstep ← match ctx? with
        | none => pure <| ForInStep.yield b
        | some ctx => f (ctx, i, ch) b
      match bstep with
      | .yield b => do
        let ctx? := i.updateContext? ctx?
        let mut b := b
        for t in ch do
          match ← go ctx? b t with
          | .yield b' => b := b'
          | bdone@(.done _) => return bdone
        return .yield b
      | bdone@(.done _) => pure bdone
  | .hole _ => pure <| .yield b

universe u₁ u₂ in
instance {m : Type u₁ → Type u₂} [Monad m] :
    ForIn m InfoTree (ContextInfo × Info × PersistentArray InfoTree) where
  forIn := InfoTree.forIn

/--
Gathers instance hypotheses in the type of `decl` that are unused in the remainder of the type and
whose types satisfy `p`. (Does not consider the body of the declaration.) Collects them into an
`Array Parameter`, and if (and only if) this array is nonempty, feeds it to `logOnUnused`.

Since `logOnUnused` will only be run if its argument is nonempty, it is allowed to be expensive.

Note that `p` is non-monadic, and may encounter loose bvars in its argument. This is a performance
optimization. However, the `Parameter`s are created in a telescope, and their fields will *not*
have loose bound variables.
-/
def _root_.Lean.ConstantVal.onUnusedInstancesWhere (decl : ConstantVal)
    (p : Expr → Bool) (logOnUnused : Array Parameter → TermElabM Unit) : CommandElabM Unit := do
  let unusedInstances := decl.type.getUnusedForallInstanceBinderIdxsWhere p
  if let some maxIdx := unusedInstances.back? then liftTermElabM do
    forallBoundedTelescope decl.type (some <| maxIdx + 1)
      (cleanupAnnotations := true) fun fvars _ => do
        let unusedInstances : Array Parameter ← unusedInstances.mapM fun idx =>
          return {
              fvar? := fvars[idx]?
              type? := ← fvars[idx]?.mapM (inferType ·)
              idx := idx + 1
            }
        logOnUnused unusedInstances

/-- Finds theorems whose bodies were elaborated in the current infotrees and whose (full)
declaration names satisfy `nameFilter`. Checks their type to see if it contains instance hypotheses
that (1) are unused in the remainder of the type (2) have types which satisfy `instanceTypeFilter`.
(Note: `instanceTypeFilter` is non-monadic, and may encounter bound variables in its argument. This
is a performance optimization. `isAppOrForallOfConstP` may be useful in detecting constant
applications and types of the form `∀ (...), bar ..` here.)

If any such parameters are found in the type of a theorem `foo`, we create a telescope in which the
types and free variables of the unused parameters are available as
`unusedParams : Array Parameter := #[p₁, p₂, ..., pₙ]`, as well as the theorem `thm : ConstantVal`
and current infotree `t`, and run `log t thm unusedParams`.

The ambient ref during `log t thm unusedParams` is the location of the type signature of the
theorem `thm`, if it can be found; else, we use the location of the theorem's name; else, we use
the whole command.

A simple pattern is therefore
```
fun _ thm unusedParams => do
  logLint linter.fooLinter (← getRef) m!"\
    {thm.name.unusedInstancesMsg unusedParams}\n\
    <extra caption>"
```
which logs

> \`{foo}\` has the hypothes[is/es] {p₁}, {p₂}, ..., and {pₙ} which [is/are] not used in the
  remainder of the type.
>
> \<extra caption\>
>
> This linter can be disabled with \`set_option {linter.fooLinter.name} false\`

pluralizing as appropriate.
-/
def _root_.Lean.Syntax.logUnusedInstancesInTheoremsWhere (cmd : Syntax)
    (declFilter : ConstantVal → Bool) (instanceTypeFilter : Expr → Bool)
    (log : InfoTree → ConstantVal → Array Parameter → TermElabM Unit) :
    CommandElabM Unit := do
  for t in ← getInfoTrees do
    let thms := t.getTheorems (← getEnv) |>.filter declFilter
    for thm in thms do
      thm.onUnusedInstancesWhere instanceTypeFilter fun unusedParams =>
        t.withDeclSigRef cmd thm.name do
          log t thm unusedParams

/-- Detects `Decidable*` instance hypotheses in the types of theorems which are not used in the
remainder of the type, and suggests replacing them with a use of `classical` in the proof or
`open scoped Classical in` at the term level. -/
def unusedDecidable : Linter where
  run := withSetOptionIn fun cmd => do
    unless getLinterValue linter.unusedDecidable (← getLinterOptions) do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      (!(`Decidable).isPrefixOf ·.name)
      isDecidableVariant
      fun _ thm unusedParams => do
        logLint linter.unusedDecidable (← getRef) m!"\
          {thm.name.unusedInstancesMsg unusedParams}\n\
          Consider removing these hypotheses and using `classical` in the proof instead. For terms,
          consider using `open Scoped classical in` at the term level (not the command level)."

initialize addLinter unusedDecidable

end Mathlib.Linter.UnusedDecidable
