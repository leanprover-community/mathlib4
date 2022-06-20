/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
import Lean
import Lean.Parser
import Mathlib.Data.String.Defs
open Lean Elab Command Term Tactic
open Lean.Parser.Term
open Lean.Parser.Command
open Lean.Elab.Deriving

/-!

# Deriving optics from inductive datatypes.

This file defines the `derive_optics T` command where `T` is an inductive datatype.
For each constructor `𝑐` of `T` and each field `𝑎 : α` of `𝑐`, this will create the following definitions:

1. `T.𝑐.𝑎? : T → Option α`
2. `T.𝑐.𝑎! : T → α`
3. `T.𝑐.with𝑎 : α → T → T`
4. `T.𝑐.modify𝑎 : (α → α) → T → T`
5. `T.𝑐.modifyM𝑎 : (α → M α) → T → M T`

## Future work

[todo] Extending to many other patterns:

- `T.children : T → List T`
- `T.traverseChildren [Applicative M]: (T → M T) → (T → M T)`
- `T.Base : Type → Type` is the base functor type such that `T = Fix T.Base`
- `T.Free : Type → Type`
- `T.Zipper`
- `T.Pos` -- analogous to `Expr.SubExpr.Pos`.
- Build an optics library and have full-fledged optics.

-/

namespace Lean.Elab.Deriving.Optics

initialize registerTraceClass `derive_optics

-- [todo] this must already exist?
def Name.mapHead (f : String →String) : Name →Name
  | Name.str p s _ => Name.mkStr p (f s)
  | n => n

def mkDocComment (s : String) : Syntax :=
  mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

variable {M} [MonadControlT MetaM M] [MonadLiftT MetaM M] [Monad M] [MonadEnv M] [MonadError M]

structure IndField :=
  (ctor : Name)
  (name : Name)
  (index : Nat)
  /-- Abstracted on params. Use `type.instantiateRev params` to reinstantiate. -/
  (type : Expr)

/-- Maps a field name to the constructors which include that field name and the type.
It's none if the field exists on constructors but the types are incompatible.-/
abbrev FieldCollections := NameMap (Option (NameMap Nat × Expr))

def getAllFields (decl : Name) : TermElabM (Array IndField) := do
  let indVal ← getConstInfoInduct decl
  indVal.ctors.foldlM (fun acc ctor => do
    let ctorInfo ← Lean.getConstInfoCtor ctor
    Lean.Meta.forallTelescopeReducing ctorInfo.type fun xs type => do
      let xsdecls ← liftM $ xs.mapM Lean.Meta.getFVarLocalDecl
      let params := xs[:ctorInfo.numParams].toArray
      let fields := xsdecls[ctorInfo.numParams:].toArray
      let field_idxs : Array (Nat × _) := fields.mapIdx fun i x => (i,x)
      field_idxs.foldlM (fun acc (fieldIdx, field) => do
        let fieldName := field.userName
        if fieldName.isNum then
          return acc
        let type := Expr.abstract field.type params
        return acc.push ⟨ctor, fieldName, fieldIdx, type⟩
      ) acc
  ) #[]

/-- Given inductive datatype `decl`, makes a map from field names to a
map from constructor names to field index and type. -/
def getFieldCollections
  (decl : Name) : TermElabM FieldCollections := do
  let fields ← getAllFields decl
  return fields.foldl add ∅
  where
    add (n : FieldCollections) (f : IndField) : FieldCollections :=
      match n.find? f.name with
      | some x => x.bind (fun (ctors, t) => if t == f.type && not (ctors.contains f.ctor) then some (ctors.insert f.ctor f.index, t) else none) |> n.insert f.name
      | none => n.insert f.name (some (NameMap.insert ∅ f.ctor f.index, f.type))

private def mkAlt (mkRhs : (fieldVars: Array Syntax) → TermElabM Syntax) (ctor : Name) : TermElabM (Syntax × Syntax) := do
  let ctorInfo ← Lean.getConstInfoCtor ctor
  let fieldVars ←
    List.range ctorInfo.numFields
    |>.mapM (fun _ => mkIdent <$> mkFreshUserName `a)
  let fieldVars := fieldVars.toArray
  let lhs ← `($(mkIdent ctorInfo.name):ident $fieldVars:term*)
  let rhs ← mkRhs fieldVars
  return (lhs, rhs)

private def mkAlts (ctors : NameMap Nat) (mkRhs : (ctorName : Name) → (fieldIdx : Nat) → (fieldVars : Array Syntax) → TermElabM Syntax) : TermElabM ((Array Syntax) × (Array Syntax)) := do
  let cs ← ctors.toList.toArray.mapM (fun (n,i) => mkAlt (mkRhs n i) n)
  return Array.unzip cs

private def ctorNameOrList (ctors : NameMap α) : String :=
  ctors.toList |>.map Prod.fst |>.map (fun | Name.str _ x _ => s!"`{x}`" | _ => "????") |> String.andList "or"

private def isExhaustive (ctors : NameMap α) (indName : Name) : M Bool := do
  let indVal ← getConstInfoInduct indName
  return indVal.ctors.all (fun a => ctors.contains a)

def mkGetOptional (baseName indName fieldName : Name) (indType : Syntax) (implicitBinders : Array Syntax) (fieldType : Syntax) (ctors : NameMap Nat) : TermElabM Syntax := do
  if (← isExhaustive ctors indName) then
    throwError "expected non-exhautive ctor list"
  let defname := mkIdent <| baseName ++ Name.mapHead (· ++ "?") fieldName
  let (lhs, rhs) ← mkAlts ctors (fun _ i fvs => `(some $(fvs[i])))
  let docstring := mkDocComment <| s!"If the given `{indName}` is a {ctorNameOrList ctors}; returns the value of the `{fieldName}` field, otherwise returns `none`."
  `(
        $docstring:docComment
        def $defname:ident $implicitBinders:explicitBinder*
          : $indType → Option $fieldType
          $[| $lhs => $rhs]*
          | _ => none
  )

def mkGetBang (baseName indName fieldName : Name) (indType : Syntax) (implicitBinders : Array Syntax) (fieldType : Syntax) (ctors : NameMap Nat) : TermElabM Syntax := do
  if (← isExhaustive ctors indName) then
    throwError "expected non-exhautive ctor list"
  let defname : Name := baseName ++ Name.mapHead (· ++ "!") fieldName
  let docstring := mkDocComment <| s!"If the given `{indName}` is a {ctorNameOrList ctors},
    returns the value of the `{fieldName}` field, otherwise panics."
  let (lhs, rhs) ← mkAlts ctors (fun _ i fvs => pure fvs[i])
  `(
    $docstring:docComment
    def $(mkIdent defname):ident $implicitBinders:explicitBinder* [Inhabited $fieldType]
      : $indType → $fieldType
      $[| $lhs => $rhs]*
      | x =>
        let n := $(quote (ctorNameOrList ctors))
        panic! s!"expected constructor {n}"
  )

def mkGet (baseName indName fieldName : Name) (indType : Syntax) (implicitBinders : Array Syntax) (fieldType : Syntax) (ctors : NameMap Nat) : TermElabM Syntax := do
  if not (← isExhaustive ctors indName) then
    throwError "expected exhaustive ctor list"
  let defname : Name := baseName ++ fieldName
  let docstring := mkDocComment <| s!"Returns the value of the `{fieldName}` field."
  let (lhs, rhs) ← mkAlts ctors (fun _ i fvs => pure fvs[i])
  `(
    $docstring:docComment
    def $(mkIdent defname):ident $implicitBinders:explicitBinder* [Inhabited $fieldType]
      : $indType → $fieldType
      $[| $lhs => $rhs]*
  )


def mkWith (baseName indName fieldName : Name) (indType : Syntax) (implicitBinders : Array Syntax) (fieldType : Syntax) (ctors : NameMap Nat) : TermElabM Syntax := do
  let defname : Name := baseName ++ Name.mapHead (fun n => s!"with{n.capitalize}") fieldName
  let x ← mkIdent <$> mkFreshUserName `x
  let (lhs, rhs) ← mkAlts ctors (fun ctorName i fvs => `($(mkIdent ctorName) $(fvs.modify i (fun _ => x)):term*))
  if ← isExhaustive ctors indName then
    `(
      $(mkDocComment <| s!"Replaces the value of the `{fieldName}` field with the given value."):docComment
      def $(mkIdent defname):ident $implicitBinders:explicitBinder*
        ($x : $fieldType)
        : $indType → $indType
        $[| $lhs => $rhs]*
    )
  else
    `(
      $(mkDocComment <| s!"If the given `{indName}` is a {ctorNameOrList ctors},
          replaces the value of the `{fieldName}` field with the given value.
          Otherwise acts as the identity function."):docComment
      def $(mkIdent defname):ident $implicitBinders:explicitBinder*
        ($x : $fieldType)
        : $indType → $indType
        $[| $lhs => $rhs]*
        | y => y
    )

def mkModify (baseName indName fieldName : Name) (indType : Syntax) (implicitBinders : Array Syntax) (fieldType : Syntax) (ctors : NameMap Nat) : TermElabM Syntax := do
  let defname : Name := baseName ++ Name.mapHead (fun n => s!"modify{n.capitalize}") fieldName
  let x ← mkIdent <$> mkFreshUserName `visit
  let (lhs, rhs) ← mkAlts ctors (fun ctorName i fvs => do
    let outFields ← fvs.modifyM i (fun q => `(($x <| $q)))
    `($(mkIdent ctorName) $outFields:term*))
  if ← isExhaustive ctors indName then
    `(
      $(mkDocComment <| s!"Modifies the value of the `{fieldName}` field with the given `visit` function."):docComment
      def $(mkIdent defname):ident $implicitBinders:explicitBinder*
        ($x :$fieldType → $fieldType )
        : $indType → $indType
        $[| $lhs => $rhs]*
    )
  else
    `(
      $(mkDocComment <| s!"If the given `{indName}` is a {ctorNameOrList ctors};
          modifies the value of the `{fieldName}` field with the given `visit` function."):docComment
      def $(mkIdent defname):ident $implicitBinders:explicitBinder*
        ($x :$fieldType → $fieldType )
        : $indType → $indType
        $[| $lhs => $rhs]*
        | y => y
    )


def mkModifyM (baseName indName fieldName : Name) (indType : Syntax) (implicitBinders : Array Syntax) (fieldType : Syntax) (ctors : NameMap Nat) : TermElabM Syntax := do
  let visit ← mkIdent <$> mkFreshUserName `visit
  let x ← mkIdent <$> mkFreshUserName `x
  let (lhs, rhs) ← mkAlts ctors (fun ctorName i fvs => do
    let outFields := fvs.modify i (fun q => x)
    `((fun $x => $(mkIdent ctorName) $outFields:term*) <$> $visit $(fvs[i])))
  let defname : Name := baseName ++ Name.mapHead (fun n => s!"modifyM{n.capitalize}") fieldName
  if ← (isExhaustive ctors indName) then
    let docstring := mkDocComment <|  s!"Runs the given `visit` function on the `{fieldName}` field."
    `(
      $docstring:docComment
      def $(mkIdent defname):ident
        {M} [Functor M]
        $implicitBinders:explicitBinder*
        ($visit : $fieldType → M $fieldType)
        :  $indType → M $indType
        $[| $lhs => $rhs]*
    )
  else
    let docstring := mkDocComment <|  s!"Runs the given `visit` function on the `{fieldName}` field if present.
            Performing the pure op if the given `{indName}` is not a {ctorNameOrList ctors}."
    `(
      $docstring:docComment
      def $(mkIdent defname):ident
        {M} [Pure M] [Functor M]
        $implicitBinders:explicitBinder*
        ($visit : $fieldType → M $fieldType)
        :  $indType → M $indType
        $[| $lhs => $rhs]*
        | y => pure y
    )

def opticMakers := [mkGet, mkGetOptional, mkGetBang, mkWith, mkModify, mkModifyM]

def mkOpticsCore (indVal : InductiveVal) : TermElabM (Array Syntax) :=
  Lean.Meta.forallTelescopeReducing indVal.type fun params indType => do
    let paramDecls ← liftM $ params.mapM Lean.Meta.getFVarLocalDecl
    let paramStx := paramDecls |>.map (fun x => mkIdent x.userName)
    let indType ← `($(mkIdent indVal.name):ident $paramStx:term*)
    let implicitBinders ← paramDecls |>.mapM (fun x => `(implicitBinderF| { $(mkIdent x.userName) }))
    let mut cmds := #[]
    let fcs ← getFieldCollections indVal.name
    have : ForIn TermElabM FieldCollections (_ × _) := Std.RBMap.instForInRBMapProd
    have : ForIn TermElabM (NameMap Nat) (_ × _) := Std.RBMap.instForInRBMapProd
    for (field, cne?) in fcs do
      if let some (ctors, fieldType) := cne? then
        let isEx := if ← isExhaustive ctors indVal.name then "exhaustive" else "non-exhaustive"
        trace[derive_optics] "Deriving optic functions for {isEx} field {field} with constructors {ctors.toList}. "
        let fieldType ← PrettyPrinter.delab <| fieldType.instantiateRev params
        for mk in opticMakers do
          try
            let cmd ← mk indVal.name indVal.name field indType implicitBinders fieldType ctors
            cmds := cmds.push cmd
          catch
            | x => continue
    let fields ← getAllFields indVal.name
    for field in fields do
      let fieldType ← PrettyPrinter.delab <| field.type.instantiateRev params
      let ctors := mkNameMap Nat |>.insert field.ctor field.index
      for mk in opticMakers do
        try
          let cmd ← mk field.ctor indVal.name field.name indType implicitBinders fieldType ctors
          cmds := cmds.push cmd
        catch
          | e => continue
    return cmds

def mkOptics (decl : Name) : CommandElabM Unit := do
  if not (← isInductive decl) then
    throwError "{decl} must be an inductive datatype."
  let indVal ← getConstInfoInduct decl
  if isStructure (← getEnv) indVal.name then
    throwError "{decl} structures have projectors already"
  if indVal.numIndices > 0 then
    -- It should be possible to auto-derive some optics using the method as below
    -- But the result is usually confusing so it's better to not support it and
    -- get the users to make bespoke optics.
    throwError "getters and setters derivation not supported for indexed inductive datatype {decl}."
  if indVal.ctors.length <= 1 then
    -- [todo] add lens def here.
    throwError "single constructor inductive types should be structures."

  let cmds : Array Syntax ← liftTermElabM none <| mkOpticsCore indVal
  trace[derive_optics] "Created {cmds.size} definitions."
  for cmd in cmds do
    let pp ← liftCoreM $ PrettyPrinter.ppCommand cmd
    trace[derive_optics] "Creating definition:\n{pp}"
    elabCommand cmd

elab "derive_optics" decl:ident : command =>
  mkOptics decl.getId

end Lean.Elab.Deriving.Optics
