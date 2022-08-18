/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Arthur Paulino, Gabriel Ebner
-/
import Mathlib.Tactic.Lint.Basic
import Mathlib.Data.Array.Defs

open Lean Meta

namespace Mathlib.Tactic.Lint

/-!
# Various linters

This file defines several small linters.
-/

/-- A linter for checking whether a declaration has a namespace twice consecutively in its name. -/
@[mathlibLinter] def dupNamespace : Linter where
  noErrorsFound := "No declarations have a duplicate namespace."
  errorsFound := "DUPLICATED NAMESPACES IN NAME:"
  test declName := do
    if isGlobalInstance (← getEnv) declName then
      return none
    let nm := declName.components
    let some (dup, _) := nm.zip nm.tail! |>.find? fun (x, y) => x == y
      | return none
    return m!"The namespace {dup} is duplicated in the name"

/-- A linter object for checking for unused arguments.
We skip all declarations that contain `sorry` in their value. -/
@[mathlibLinter] def unusedArguments : Linter where
  noErrorsFound := "No unused arguments."
  errorsFound := "UNUSED ARGUMENTS."
  test declName := do
    if ← isAutoDecl declName then return none
    if ← isProjectionFn declName then return none
    let info ← getConstInfo declName
    let ty := info.type
    let some val := info.value? | return none
    forallTelescope ty fun args ty => do
      let mut e := (mkAppN val args).headBeta
      e := mkApp e ty
      for arg in args do
        let ldecl ← getFVarLocalDecl arg
        e := mkApp e ldecl.type
        if let some val := ldecl.value? then
          e := mkApp e val
      let unused := args.zip (.range args.size) |>.filter fun (arg, _) =>
        !e.containsFVar arg.fvarId!
      if unused.isEmpty then return none
      addMessageContextFull <| .joinSep (← unused.toList.mapM fun (arg, i) =>
          return m!"argument {i+1} {arg} : {← inferType arg}") m!", "

/-- A linter for checking definition doc strings -/
@[mathlibLinter] def docBlame : Linter where
  noErrorsFound := "No definitions are missing documentation."
  errorsFound := "DEFINITIONS ARE MISSING DOCUMENTATION STRINGS:"
  test declName := do
    if (← isAutoDecl declName) || isGlobalInstance (← getEnv) declName then
      return none
    if declName matches .str _ "parenthesizer" | .str _ "formatter" then
      return none
    let kind ← match ← getConstInfo declName with
      | .axiomInfo .. => pure "axiom"
      | .opaqueInfo .. => pure "constant"
      | .defnInfo .. => pure "definition"
      | .inductInfo .. => pure "inductive"
      | _ => return none
    let (none) ← findDocString? (← getEnv) declName | return none
    return m!"{kind} missing documentation string"

/-- A linter for checking theorem doc strings -/
def docBlameThm : Linter where
  noErrorsFound := "No theorems are missing documentation."
  errorsFound := "THEOREMS ARE MISSING DOCUMENTATION STRINGS:"
  test declName := do
    if ← isAutoDecl declName then
      return none
    let kind ← match ← getConstInfo declName with
      | .thmInfo .. => pure "theorem"
      | _ => return none
    let (none) ← findDocString? (← getEnv) declName | return none
    return m!"{kind} missing documentation string"

/-- A linter for checking whether the correct declaration constructor (definition or theorem)
has been used. -/
@[mathlibLinter] def defLemma : Linter where
  noErrorsFound := "All declarations correctly marked as def/lemma."
  errorsFound := "INCORRECT DEF/LEMMA:"
  test declName := do
    if (← isAutoDecl declName) || isGlobalInstance (← getEnv) declName then
      return none
    if ← isProjectionFn declName then return none
    let info ← getConstInfo declName
    let isThm ← match info with
      | .defnInfo .. => pure false
      | .thmInfo .. => pure true
      | _ => return none
    match isThm, ← isProp info.type with
    | true, false => pure "is a lemma/theorem, should be a def"
    | false, true => pure "is a def, should be lemma/theorem"
    | _, _ => return none

/-- A linter for missing checking whether statements of declarations are well-typed. -/
@[mathlibLinter] def checkType : Linter where
  noErrorsFound :=
    "The statements of all declarations type-check with default reducibility settings."
  errorsFound := "THE STATEMENTS OF THE FOLLOWING DECLARATIONS DO NOT TYPE-CHECK."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    if ← isTypeCorrect (← getConstInfo declName).type then return none
    return m!"the statement doesn't type check."

/--
`univParamsGrouped e` computes for each `level` `u` of `e` the parameters that occur in `u`,
and returns the corresponding set of lists of parameters.
In pseudo-mathematical form, this returns `{ { p : parameter | p ∈ u } | (u : level) ∈ e }`
FIXME: We use `Array Name` instead of `HashSet Name`, since `HashSet` does not have an equality instance.
It will ignore `nm₀.proof_i` declarations.
-/
private def univParamsGrouped (e : Expr) (nm₀ : Name) : BaseIO (Std.HashSet (Array Name)) := do
  let res ← IO.mkRef {}
  e.forEach fun
    | e@(Expr.sort ..) =>
      res.modify (·.insert (collectLevelParams {} e).params)
    | e@(Expr.const n ..) => do
      if let .str n s .. := n then
        if n == nm₀ && s.startsWith "proof_" then
          return
      res.modify (·.insert (collectLevelParams {} e).params)
    | _ => pure ()
  res.get

/--
The good parameters are the parameters that occur somewhere in the set as a singleton or
(recursively) with only other good parameters.
All other parameters in the set are bad.
-/
private partial def badParams (l : Array (Array Name)) : Array Name :=
  let goodLevels := l.filterMap fun
    | #[u] => some u
    | _ => none
  if goodLevels.isEmpty then
    l.flatten.toList.eraseDups.toArray
  else
    badParams <| l.map (·.filter (!goodLevels.contains ·))

/-- A linter for checking that there are no bad `max u v` universe levels.
Checks whether all universe levels `u` in the type of `d` are "good".
This means that `u` either occurs in a `level` of `d` by itself, or (recursively)
with only other good levels.
When this fails, usually this means that there is a level `max u v`, where neither `u` nor `v`
occur by themselves in a level. It is ok if *one* of `u` or `v` never occurs alone. For example,
`(α : Type u) (β : Type (max u v))` is a occasionally useful method of saying that `β` lives in
a higher universe level than `α`.
-/
@[mathlibLinter] def checkUnivs : Linter where
  noErrorsFound :=
    "All declarations have good universe levels."
  errorsFound := "THE STATEMENTS OF THE FOLLOWING DECLARATIONS HAVE BAD UNIVERSE LEVELS. " ++
"This usually means that there is a `max u v` in the type where neither `u` nor `v` " ++
"occur by themselves. Solution: Find the type (or type bundled with data) that has this " ++
"universe argument and provide the universe level explicitly. If this happens in an implicit " ++
"argument of the declaration, a better solution is to move this argument to a `variables` " ++
"command (then it's not necessary to provide the universe level).
It is possible that this linter gives a false positive on definitions where the value of the " ++
"definition has the universes occur separately, and the definition will usually be used with " ++
"explicit universe arguments. In this case, feel free to add `@[nolint check_univs]`."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    let bad := badParams (← univParamsGrouped (← getConstInfo declName).type declName).toArray
    if bad.isEmpty then return none
    return m!"universes {bad} only occur together."

/-- A linter for checking that declarations aren't syntactic tautologies.
Checks whether a lemma is a declaration of the form `∀ a b ... z, e₁ = e₂`
where `e₁` and `e₂` are identical exprs.
We call declarations of this form syntactic tautologies.
Such lemmas are (mostly) useless and sometimes introduced unintentionally when proving basic facts
with rfl when elaboration results in a different term than the user intended. -/
@[mathlibLinter] def synTaut : Linter where
  noErrorsFound :=
    "No declarations are syntactic tautologies."
  errorsFound := "THE FOLLOWING DECLARATIONS ARE SYNTACTIC TAUTOLOGIES. " ++
"This usually means that they are of the form `∀ a b ... z, e₁ = e₂` where `e₁` and `e₂` are " ++
"identical expressions. We call declarations of this form syntactic tautologies. " ++
"Such lemmas are (mostly) useless and sometimes introduced unintentionally when proving " ++
"basic facts using `rfl`, when elaboration results in a different term than the user intended. " ++
"You should check that the declaration really says what you think it does."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    forallTelescope (← getConstInfo declName).type fun _ ty => do
      let some (lhs, rhs) := ty.eq?.map (fun (_, l, r) => (l, r)) <|> ty.iff?
        | return none
      if lhs == rhs then
        return m!"LHS equals RHS syntactically"
      return none

attribute [nolint synTaut] rfl


/--
Return a list of unused have/suffices/let_fun terms in an expression.
This actually finds all beta-redexes.
-/
def findUnusedHaves (e : Expr) : MetaM (Array MessageData) := do
  let res ← IO.mkRef #[]
  forEachExpr e fun e => do
    let some e := letFunAnnotation? e | return
    let Expr.app (Expr.lam n t b ..) _ .. := e | return
    if n.getRoot == `_fun_discr then return
    if b.hasLooseBVars then return
    let msg ← addMessageContextFull m!"unnecessary have {n.eraseMacroScopes} : {t}"
    res.modify (·.push msg)
  res.get

/-- A linter for checking that declarations don't have unused term mode have statements. We do not
tag this as `@[mathlibLlinter]` so that it is not in the default linter set as it is slow and an
uncommon problem. -/
@[mathlibLinter] def unusedHavesSuffices : Linter where
  noErrorsFound := "No declarations have unused term mode have statements."
  errorsFound := "THE FOLLOWING DECLARATIONS HAVE INEFFECTUAL TERM MODE HAVE/SUFFICES BLOCKS. " ++
    "In the case of `have` this is a term of the form `have h := foo, bar` where `bar` does not " ++
    "refer to `foo`. Such statements have no effect on the generated proof, and can just be " ++
    "replaced by `bar`, in addition to being ineffectual, they may make unnecessary assumptions " ++
    "in proofs appear as if they are used. " ++
    "For `suffices` this is a term of the form `suffices h : foo, proof_of_goal, proof_of_foo` where" ++
    " `proof_of_goal` does not refer to `foo`. " ++
    "Such statements have no effect on the generated proof, and can just be replaced by " ++
    "`proof_of_goal`, in addition to being ineffectual, they may make unnecessary assumptions in " ++
    "proofs appear as if they are used. "
  test declName := do
    if ← isAutoDecl declName then return none
    let info ← getConstInfo declName
    let mut unused ← findUnusedHaves info.type
    if let some value := info.value? then
      unused := unused ++ (← findUnusedHaves value)
    unless unused.isEmpty do
      return some <| .joinSep unused.toList ", "
    return none

/--
A linter for checking if variables appearing on both sides of an iff are explicit. Ideally, such
variables should be implicit instead.
-/
def explicitVarsOfIff : Linter where
  noErrorsFound := "No explicit variables on both sides of iff"
  errorsFound := "EXPLICIT VARIABLES ON BOTH SIDES OF IFF"
  test declName := do
    if ← isAutoDecl declName then return none
    forallTelescope (← getConstInfo declName).type fun args ty => do
      let some (lhs, rhs) := ty.iff? | return none
      let explicit ← args.filterM fun arg =>
        return (← getFVarLocalDecl arg).binderInfo.isExplicit &&
          lhs.containsFVar arg.fvarId! && rhs.containsFVar arg.fvarId!
      if explicit.isEmpty then return none
      addMessageContextFull m!"should be made implicit: {
        MessageData.joinSep (explicit.toList.map (m!"{·}")) ", "}"
