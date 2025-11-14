/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Init
import Mathlib.Lean.Message
import Mathlib.Tactic.Lemma
import Batteries
import Qq

/-!
# Unused Instance Hypotheses Linters

This file declares linters which detect certain instance hypotheses in declarations that are unused
in the remainder of the type.

Currently, these linters only handle theorems. (This also includes `lemma`s and `instance`s of
`Prop` classes.)

- `unusedDecidable` linter (currently off by default): suggests replacing type-unused `Decidable*`
  instance hypotheses, and could therefore be replaced by `classical` in the proof.

TODO: add more linters!
TODO: create Try This suggestions.
-/

open Lean Meta Elab Command Linter

/--
Like `findConstantVal?`, but only finds the `ConstantVal` for `decl` in `env` if it is a theorem.
-/
def Lean.Environment.findTheoremConstantVal? (env : Environment) (decl : Name) :
    Option ConstantVal := do
  let info ← env.findAsync? decl
  if info.kind matches .thm then info.toConstantVal else none

namespace Lean.Expr

/--
Returns `true` if `type` is an application of a constant `decl` for which `p decl` is true, or a
forall with return type of the same form (i.e. of the form `∀ (x₀ : X₀) (x₁ : X₁) ⋯, decl ..` where
`p decl`).

Runs `cleanupAnnotations` on `type` and `forallE` bodies, and ignores metadata in applications.
-/
@[inline] partial def isAppOrForallOfConstP (p : Name → Bool) (type : Expr) : Bool :=
    match type.cleanupAnnotations.getAppFn' with
    | .const n _ => p n
    | .forallE _ _ body _ => isAppOrForallOfConstP p body
    | _ => false

/--
Returns `true` if `type` is an application of a constant `declName`, or a
forall with return type of the same form (i.e. of the form `∀ (x₀ : X₀) (x₁ : X₁) ⋯, declName ..`).

Runs `cleanupAnnotations` on `type` and `forallE` bodies, and ignores metadata in applications.
-/
@[inline] partial def isAppOrForallOfConst (declName : Name) (type : Expr) : Bool :=
  isAppOrForallOfConstP (· == declName) type

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
partial def getUnusedForallInstanceBinderIdxsWhere (p : Expr → Bool) (e : Expr) :
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

end Lean.Expr

namespace Lean.Syntax

/-- Finds the first subtree of `stx` for which `p subtree` is `some a`, descending the tree from
the top. -/
partial def findSome? {α} (p : Syntax → Option α) : Syntax → Option α
  | stx@(.node _ _ args) => p stx <|> args.findSome? (findSome? p)
  | stx                  => p stx

/-- Returns `true` exactly when `stxᵢ.getRange? canonicalOnlyᵢ` are both `some _` and are equal. -/
def rangeEq (stx₁ stx₂ : Syntax) (canonicalOnly₁ canonicalOnly₂ := true) : Bool :=
  match stx₁.getRange? canonicalOnly₁, stx₂.getRange? canonicalOnly₂ with
  | some r₁, some r₂ => r₁ == r₂
  | _, _ => false

end Lean.Syntax

namespace Lean.Elab.InfoTree

/--
Finds the first result of `f ctx info children` which is `some a`, descending the
tree from the top. Merges and updates contexts as it descends the tree.

If provided, `ctx?` is used as an initial context. This can be helpful when invoking `findSome?` in
the middle of a larger traversal.
-/
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
Finds the first result of `← f ctx info children` which is `some a`, descending the
tree from the top. Merges and updates contexts as it descends the tree.

If provided, `ctx?` is used as an initial context. This can be helpful when invoking `findSome?` in
the middle of a larger traversal.
-/
partial def findSomeM? {m : Type → Type} [Monad m] {α}
    (f : ContextInfo → Info → PersistentArray InfoTree → m (Option α))
    (t : InfoTree) (ctx? : Option ContextInfo := none) : m (Option α) :=
  go ctx? t
where go ctx?
  | context ctx t => go (ctx.mergeIntoOuter? ctx?) t
  | node i ts => do
    let a ← match ctx? with
      | none => pure none
      | some ctx => f ctx i ts
    match a with
    | some a => pure a
    | none => ts.findSomeM? (go <| i.updateContext? ctx?)
  | hole _ => pure none

/--
Returns the value of `f ctx info children` on the outermost `.node info children` which has
context, having merged and updated contexts appropriately.

If provided, `ctx?` is used as an initial context. This can be helpful when invoking `onFirstNode?`
in the middle of a larger traversal.
-/
def onFirstNode? {α} (t : InfoTree) (f : ContextInfo → Info → PersistentArray InfoTree → α)
    (ctx? : Option ContextInfo := none) : Option α :=
  t.findSome? (ctx? := ctx?) fun ctx i ch => some (f ctx i ch)

/-- Collects all `parentDecl`s that appear at any point throughout the infotree. -/
partial def getDecls (t : InfoTree) : NameSet :=
  go {} t
where
  /-- Visits all subinfotrees and collects `PartialContextInfo.parentDeclCtx`s directly. -/
  go acc : InfoTree → NameSet
  | .context (.parentDeclCtx decl) i => go (acc.insert decl) i
  | .context _ i => go acc i
  | node _ ch => ch.foldl (init := acc) go
  | .hole _ => acc

/--
Get the declarations elaborated in the infotree `t` which are theorems according to the
environment. This includes e.g. `instance`s of `Prop` classes in addition to declarations declared
using the keyword `theorem` directly.
-/
def getTheorems (t : InfoTree) (env : Environment) : List ConstantVal :=
  t.getDecls.toList.filterMap env.findTheoremConstantVal?

/--
Given a constant name, find the first `TermInfo` whose expression is exactly that constant. Expects
`decl` to be a fully resolved name.
-/
def getConstTermInfo? (t : InfoTree) (decl : Name) : Option TermInfo :=
  t.findSome? fun
    | _, .ofTermInfo ti, _ => if ti.expr.isConstOf decl then some ti else none
    | _, _, _ => none

/--
Get the syntax of the `TermInfo` corresponding to the first appearance of `decl` as an
`Expr.const ..`.

Usually, this is the syntax of the identifier occurring after a token like `def` or `theorem`,
*excluding*  universe syntax (i.e., `id` in `$id$[.{$_,*}]?`). In the case of `instance` with no
identifier, the `instance` token is used.

Note that the behavior described here is undocumented, and subject to change.
-/
def getConstRef? (t : InfoTree) (decl : Name) : Option Syntax :=
  t.getConstTermInfo? decl |>.map (·.stx)

/--
Attempts to run `x : m α` with the monad's ref set to the syntax for the type signature of the
originating syntax of `decl` within the syntax `cmd`, according to the information linking the name
`decl` to its syntax in the infotree `t`.

If the type signature's position info cannot be found, uses the position info of the syntax for
`decl` found in `t`. If that can't be found either, uses `cmd` as the ref.

For now, only handles declarations originating from `theorem`, `lemma`, and `instance` (including
when nested in `mutual` blocks or buried somewhere in `cmd`). Does not handle `let rec`/
`where`-style `let rec` declarations.
-/
private def withDeclSigRef {m : Type → Type} [Monad m] [MonadRef m] {α}
    (t : InfoTree) (cmd : Syntax) (decl : Name) (x : m α) : m α := withRef cmd do
  let some idRef := t.getConstRef? decl | x
  let sigRef? := cmd.findSome? fun
    | `(Parser.Command.theorem| theorem $id$[.{$_,*}]? $sig:declSig $_:declVal)
    | `(«lemma»| lemma $id$[.{$_,*}]? $sig:declSig $_:declVal)
    | `(Parser.Command.instance| $_:attrKind instance $[$_:namedPrio]?
        $id$[.{$_,*}]? $sig:declSig $_:declVal) =>
      if id.raw.rangeEq idRef then sig else none
    -- When no `declId` is present, Lean uses the position information for the `instance` token.
    | `(Parser.Command.instance| $_:attrKind instance%$tk $[$_:namedPrio]?
        $sig:declSig $_:declVal) => if tk.rangeEq idRef then sig else none
    -- TODO: handle `let rec` decls (after `where`), handle defs etc.
    | _ => none
  -- Fall back to `idRef` if `sigRef` is not found or has no position info.
  withRef idRef <| withRef? sigRef? x

end Lean.Elab.InfoTree

namespace Mathlib.Linter.UnusedInstances

/--
A structure for storing information about a parameter of some declaration, usually within some
telescope. We use this for recording the expressions and index associated to a parameter which was
unused in the remainder of the type.

`m!"{param}"` displays as `` `[{param.type?.get}]` (#{param.idx})`` (backticks included) if `type?`
is `some _`, and as `parameter #{param.idx}` as a failsafe if `type?` is `none`. (We always expect
`type?` to be `some _`, but would like a fallback if there are unexpected issues in telescoping.)
-/
private structure Parameter where
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

/--
Given a (full, resolvable) declaration name `foo` and an array of parameters
`#[p₁, p₂, ..., pₙ]`, constructs the message:
> \`{foo}\` has the hypothes(is/es) {p₁}, {p₂}, ..., and {pₙ} which (is/are) not used in the
  remainder of the type.
-/
private def _root_.Lean.Name.unusedInstancesMsg (declName : Name)
    (unusedInstanceBinders : Array Parameter) : MessageData :=
  let unusedInstanceBinders := unusedInstanceBinders.map toMessageData
  m!"`{.ofConstName declName}` has the \
  {"hypothesis".withPlural "hypotheses" unusedInstanceBinders.size} \
  {.andList unusedInstanceBinders.toList} which \
  {"is".withPlural "are" unusedInstanceBinders.size} not used in the remainder of the type."

/--
Gathers instance hypotheses in the type of `decl` that are unused in the remainder of the type and
whose types satisfy `p`. (Does not consider the body of the declaration.) Collects them into an
`Array Parameter`, and if (and only if) this array is nonempty, feeds it to `logOnUnused`.

Since `logOnUnused` will only be run if its argument is nonempty, it is allowed to be expensive.

Note that `p` is non-monadic, and may encounter loose bvars in its argument. This is a performance
optimization. However, the `Parameter`s are created in a telescope, and their fields will *not*
have loose bound variables.
-/
private def _root_.Lean.ConstantVal.onUnusedInstancesWhere (decl : ConstantVal)
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

-- TODO: check if type has `sorry` or we have errors
-- TODO: change docs if using `parentDeclCtx` strategy
/--
Finds theorems whose bodies were elaborated in the current infotrees and whose (full)
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

section Decidable

/--
Checks if `type` is an application of (or forall with return type which is an application of) a
`Decidable*` constant. Specifically, checks if the constant is one of:
- `Decidable`
- `DecidablePred`
- `DecidableRel`
- `DecidableEq`
- `DecidableLE`
- `DecidableLT`

Ignores metadata and cleans up annotations.
-/
def isDecidableVariant (type : Expr) : Bool :=
  type.isAppOrForallOfConstP fun n =>
    n == ``Decidable     ||
    n == ``DecidablePred ||
    n == ``DecidableRel  ||
    n == ``DecidableEq   ||
    n == ``DecidableLE   ||
    n == ``DecidableLT

/--
The `unusedDecidable` linter checks if a theorem's hypotheses include `Decidable*` instances which
are not used in the remainder of the type. If so, it suggests removing the instances and using
`classical` or `open scoped Classical in`, as appropriate, in the theorem's proof instead.

This linter fires only on theorems. (This includes `lemma`s and `instance`s of `Prop` classes.)
-/
register_option linter.unusedDecidable : Bool := {
  defValue := false
  descr := "enable the unused `Decidable*` instance linter, which lints against `Decidable*` \
    instances in the hypotheses of theorems which are not used in the type, and can therefore be \
    replaced by a use of `classical` in the proof."
}

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

end Decidable

end Mathlib.Linter.UnusedInstances
