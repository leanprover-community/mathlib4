/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Init
import Mathlib.Data.String.Defs
import Batteries

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


#check getInfoTrees

def NoType := Unit

def Lean.Elab.TermInfo.toMessageData (i : TermInfo) (ctx : ContextInfo) : MetaM MessageData := do
  let type := i.expectedType?.getD <| mkConst ``NoType
  let n := if i.isBinder then i.elaborator ++ `binder else i.elaborator
  let g ← mkFreshExprMVarAt i.lctx #[] type .syntheticOpaque n
  return m!"{← i.format ctx}\n{.ofGoal g.mvarId!}"

#check MetavarContext

def Lean.Elab.TacticInfo.lctxsBefore (i : TacticInfo) : List LocalContext :=
  i.goalsBefore.map fun g => i.mctxBefore.getDecl g |>.lctx

def Lean.Elab.TacticInfo.lctxsAfter (i : TacticInfo) : List LocalContext :=
  i.goalsAfter.map fun g => i.mctxAfter.getDecl g |>.lctx


def Lean.Elab.TacticInfo.toMessageData (i : TacticInfo) (ctx : ContextInfo) : MetaM MessageData := do
  let type :=  mkConst ``NoType
  let n := i.elaborator
  Meta.withLCtx' i.lctxsBefore[0]! do
  let g ← mkFreshExprMVar type .syntheticOpaque n
  return ← addMessageContext m!"{← i.format ctx}\n{.ofGoal g.mvarId!}"

inductive ListTree where
| node (h : MessageData) (j : List ListTree)

def Lean.MessageData.indentBy (msg : MessageData) (i : Nat) : MessageData :=
  m!"{String.replicate (2 * i) ' '}{msg}"

def ListTree.toMessageData (t : ListTree) : MessageData :=
  go 0 t
where
  go (indent : Nat) : ListTree → MessageData
  | .node msg subMsgs => Id.run do
    let mut msg := MessageData.nest indent m!"• {msg}"
    for s in subMsgs do
      msg := msg ++ "\n" ++ .nest (indent + 1) (go (indent + 1) s)
    return msg

#check TermInfo

instance : ToMessageData ListTree where
  toMessageData := ListTree.toMessageData

elab tk:"#info_trees!" " in" cmd:command : command => do
    if ! (← getInfoState).enabled then
      logError "Info trees are disabled, can not use `#info_trees`."
    else
      elabCommand cmd
      let infoTrees := (← getInfoState).substituteLazy.get.trees
      liftTermElabM <| withRef tk do for t in infoTrees do
        let some (l : ListTree) ← t.visitM (postNode := fun ctx i _ch l => do
          let l := l.reduceOption
          match i with
          | .ofTermInfo i => return ListTree.node m!"{repr i.expr} {← i.toMessageData ctx}" l
          | .ofCommandInfo i => return ListTree.node m!"{i.elaborator}: {i.stx}" l
          | i => return ListTree.node m!"{← i.format ctx}" l
        )
          | continue
        logInfo l.toMessageData

variable {α} (q : α = α) {α} [inst:DecidableEq α]



#check Lean.Parser.Command.«include»
#info_trees! in
include inst in
theorem foo.{u} {α : Type u} : Nat → α = α
| n => by
  -- run_tac do
  --   logInfo m!"{(← getLCtx).decls.toArray.reduceOption.map (·.isImplementationDetail)}"
  exact go n
where
  go (n : Nat) : α = α := rfl

structure FooRel (i j : Nat) where
  le : j ≤ 2 * i
  ge : i < j


#info_trees! in
theorem bar (i : Nat) (h : i ≠ 0) : FooRel i (i+1) where
  le := by grind
  ge := by? grind


run_cmd do
  let e := wasOriginallyTheorem (← getEnv) `foo.go
  logInfo m!"{e}"

#info_trees! in
mutual

theorem b : True := True.intro

theorem f : False := sorry

end

/-
# Support
- get syntax of declarations; need this for body + good logging
- can do this by looking at `elabMutual`/`elabDeclaration` nodes. I like that personally? but how to associate with names? well, get the range of the decl from infotrees first. or, could find the first declarations in the body syntax that match our ranges. maybe a bit more uniform, fewer infotree excursions.
- Okay, so we're just going to use the ref of the declId to search for appropriate declarations.
- `Parser.Term.whereDecls` then `letRecDecl` for let recs.
- support just `theorem` for now, but eventually `def` and `instance`...
- support `∀` and `→` in type signature to the right of `:` eventually, but not now.
-/

#check expandDeclSig

#check Parser.Term.whereDecls

/-- Searches for some part `result` of `stx` such that `getPiece? result` has the same range as
`piece`. For example, `getPiece?` might be of the form ``fun | `(term|by $tac) => tac | _ => none``,
and `stx.findByRangeOfComponent piece getPiece?` would return the first syntax of the form
`by $tac` such that `tac` had the same range as `piece`.

Returns `.undef` if `piece` itself has no position info.

Note: by default, we ask that the syntax returned by `getPiece?` is canonical.
-/
def Lean.Syntax.findByRangeOfComponent? (stx piece : Syntax) (getPiece? : Syntax → Option Syntax)
    (canonicalOnly := true) : LOption Syntax := Id.run do
  let some range := piece.getRange? | return .undef
  (·.toLOption) <| stx.find? fun stx =>
    if
      let some range' := (getPiece? stx).bind (·.getRange? canonicalOnly)
    then
      range == range'
    else
      false

-- TODO: grab the `declSig` and `declVal` here?

#check Syntax.structRangeEq

def Lean.Syntax.findTheoremByDeclIdRef? (cmd declId : Syntax) : LOption Syntax :=
  cmd.findByRangeOfComponent? declId fun
    | `(Parser.Command.theorem| theorem $declId:declId $_:declSig $_:declVal) => declId
    | _ => none

def Lean.Syntax.rangeEq? (stx₁ stx₂ : Syntax) (canonicalOnly₁ canonicalOnly₂ := true) :
    Option Bool :=
  match stx₁.getRange? canonicalOnly₁, stx₂.getRange? canonicalOnly₂ with
  | some r₁, some r₂ => r₁ == r₂
  | _, _ => none

def Lean.Syntax.hasRange (stx : Syntax) (range : String.Range) (canonicalOnly := true) : Bool :=
  stx.getRange? canonicalOnly |>.map (· == range) |>.getD false

#check Parser.Command.declVal

open Parser Command Term in
/-- Ideally, this is expanded to handle all binders. -/
structure InstanceBinderStx where
  ref : Syntax
  id : Option Ident
  type : Term

/- Note that `DefView` is both too course for our purposes (we need to extract the bodies and let
recs, whereas `DefView` puts these all in the `value` field and processes them later) and has extra
information that is irrelevant to us (regarding incrementality). -/
structure TheoremSyntaxView where
  decl : Name
  cmd : Syntax
  tk : Syntax
  id : Ident
  instanceBinders : Array InstanceBinderStx -- Should, ideally, be simply `binders`.
  type : Term
  bodies : Array Term
  -- TODO: process into array of `TheoremSyntaxView`s
  whereDecls? : Option (Array (TSyntax ``Parser.Term.letRecDecl))

partial def Lean.Syntax.findSomeAux {α} (p : Syntax → Option α) : Syntax → Option α
  | stx@(.node _ _ args) => p stx <|> args.findSome? (findSomeAux p)
  | stx                        => p stx

def Lean.Syntax.findSome? {α} (stx : Syntax) (p : Syntax → Option α) : Option α :=
  findSomeAux p stx

#check Parser.Command.declBody




open Parser Command Term in
def getTheoremSyntaxView (decl : Name) (idRef : Syntax) (cmd : Syntax) :
    LOption TheoremSyntaxView := Id.run do
  let some idRange := idRef.getRange? | return .undef
  (·.toLOption) <| cmd.findSome? fun
    /- Note: modifiers are taken care of outside of `Parser.Command.theorem`, so this match is
    exhaustive. -/
    | `(Parser.Command.theorem|
        theorem%$tk $id:ident$[.{$_,*}]? $binders* : $type:term $val:declVal) => do
      guard <| id.raw.hasRange idRange
      let instanceBinders := binders.filterMap fun
        | ref@`(instBinder| [$[$id:ident :]? $type:term]) => some { ref, id, type }
        | _ => none
      let (bodies, whereDecls?) :=
        -- See also `elabHeaders.getBodyTerm` in `Lean.Elab.MutualDef`.
        -- See also `declValToTerm` and `expandMatchAltsWhereDecls`.
        match val with
        -- Note: this match still works despite complications in `declBody`.
        | `(declValSimple| := $body:term $_ $[where $[$whereDecls?:letRecDecl];*]?) =>
          (#[body], whereDecls?)
        | `(declValEqns| $[ | $_:term,* => $bodies:term ]*
              $_ $[where $[$whereDecls?:letRecDecl];*]?) =>
          (bodies, whereDecls?)
        | `(whereStructInst| where $[$lval:structInstLVal $[$[$binders]* $[: $ty?]?
              $fields:structInstFieldDecl]?];* $[where $[$whereDecls?:letRecDecl];*]?) =>
          let bodies := fields.flatMap fun
            | some field => match field with
              | `(structInstFieldDef| := $body) => #[body]
              | `(structInstFieldEqns| $[ | $_:term,* => $body:term ]*) => body
              -- currently unreachable (may change if recursive `where` notation is added)
              | _ => #[⟨.missing⟩]
            -- field is given by an abbreviation, e.g. `x` where `x` is in the local context
            | none => #[]
          (bodies, whereDecls?)
        | _ => (#[⟨.missing⟩], none) -- unreachable
      return {
        decl, id, tk, cmd, instanceBinders, type, bodies, whereDecls?
      }
    | _ => none

/--
Gets the indices `i` of the binders of a nested `.forallE`, `(x₀ : A₀) → (x₁ : A₁) → ⋯ → X`,
such that
- `[xᵢ : Aᵢ]` has `instImplicit` `binderInfo`
-  `p Aᵢ` is `true`
- `Aᵢ₊₁ → ⋯ → X` does not depend on `xᵢ`. (It's in this sense that `xᵢ : Aᵢ` is "unused".)

Note that the argument to `p` may have loose bvars.

This function runs `cleanupAnnotations` on each expression before examining it.

For performance, we test dependence via   loose bound variables instead of creating intermediate
telescopes.
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

partial def findSome? (p : Info → Option α) (t : InfoTree) : Option α :=
  match t with
  | .context _ t => findSome? p t
  | .node i ts   => p i <|> ts.findSome? (findSome? p)
  | _ => none

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

/-
# Next up:

- extract the fvarids from the local context of the node
- head back up the tree and get the instance type syntax via cursed infotree traversal
- compare ranges in the `TheoremViewSyntax` to find syntax and/or realize that it's to the right of the `:`, or elsewhere entirely
- adjust body as appropriate, matching on `by` or not, and checking for `classical`/`open scoped Calssical in` before inserting it

-/

end Lean.Elab.InfoTree

namespace Mathlib.Linter.UnusedDecidable

/--
Returns `true` if `type` is an application of a `Decidable*` constant, or a forall with return type
a of the same form (i.e. of the form `∀ (x₀ : X₀) (x₁ : X₁) ⋯, Decidable* ..`). Specifically,
checks if the constant is one of: `DecidableEq`, `DecidableLE`, `DecidableLT`, `DecidableRel`,
`DecidablePred`, or `Decidable`.


Runs `cleanupAnnotations` on `type` and `forallE` bodies, and ignores metadata in applications.
-/
@[inline] partial def isAppOrForallOfDecidable (type : Expr) : Bool :=
    match type.cleanupAnnotations.getAppFn' with
    | .const n _ =>
      n == ``DecidableEq   ||
      n == ``DecidableLE   ||
      n == ``DecidableLT   ||
      n == ``DecidableRel  ||
      n == ``DecidablePred ||
      n == ``Decidable
    | .forallE _ _ body _ => isAppOrForallOfDecidable body
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
    instances in the hypotheses of theorems which are not used in the type, and can therefore be \
    replaced with a use of `classical` in the proof."
}

/-- The linter for unused `Decidable*` hypotheses in proposition declarations. -/
def unusedDecidable : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.unusedDecidable (← getLinterOptions) do
      return
    for t in ← getInfoTrees do
      let decls := t.getDecls
      -- For now, only handle `theorem`s.
      -- TODO: handle `def` propositions too; requires re-running `withHeaderSecVars`
      let decls := decls.filter <| wasOriginallyTheorem (← getEnv)
      liftTermElabM do for decl in decls do
        let some val := (← getEnv).findConstVal? decl | continue
        let unusedDecidableHyps :=
          val.type.getUnusedForallInstanceBinderIdxsWhere isAppOrForallOfDecidable
        unless unusedDecidableHyps.isEmpty do
          -- TODO: get syntax from infotrees for logging and Try This suggestion
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
