/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
import Lean
import Lean.Parser
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

-- [todo] this must already exist.
def Name.mapHead (f : String →String) : Name →Name
  | Name.str p s _ => Name.mkStr p (f s)
  | n => n

def NameMap.modifyCol [EmptyCollection α] (visit: α → α) (n : NameMap α) (k : Name) : NameMap α :=
  n.find? k |>.getD ∅ |> visit |> n.insert k

def mkDocComment (s : String) : Syntax :=
  mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

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
    throwError "single constructor inductive types are not supported yet."
  for ctor in indVal.ctors do
    let ctorInfo ← Lean.getConstInfoCtor ctor
    let cmds ← liftTermElabM none <| Lean.Meta.forallTelescopeReducing ctorInfo.type fun xs type => do
      let mut cmds := #[]
      -- [todo] I think you have to do some macro hygeine here with eraseMacroScopes and mkFreshUserName but idk
      let xsdecls ← liftM <| xs.mapM Lean.Meta.getFVarLocalDecl
      let params := xsdecls[:ctorInfo.numParams].toArray
      let fields := xsdecls[ctorInfo.numParams:].toArray
      let fieldPatterns ← fields.mapM (fun f => mkIdent <$> mkFreshUserName f.userName)
      let implicitBinders ← params |>.mapM (fun x => `(implicitBinderF| { $(mkIdent x.userName) }))
      let ctorPattern ← `($(mkIdent ctorInfo.name):ident $fieldPatterns:term*)
      for fieldIdx in List.range ctorInfo.numFields do
        let field := fields[fieldIdx]
        let fieldPat := fieldPatterns[fieldIdx]
        let outType ← PrettyPrinter.delab type
        let fieldType ← PrettyPrinter.delab field.type
        -- [todo] check that field has friendly userName. If it doesn't then don't derive the optics.
        -- [todo] if there are no clashes, then you can drop the constructor name.
        -- [todo] if the same field name appears on multiple ctors, we can make a multi-ctor version of the optics where we drop the ctor name prefix.
        --        additionally, if the field name appears on all constructors we can produce a Lens version and drop the `?`.

        -- ①: T.𝑐.𝑎? : T → Option α
        let defname  := mkIdent <| ctorInfo.name ++ Name.mapHead (· ++ "?") field.userName
        let docstring := mkDocComment <| s!"If the given `{indVal.name}` is a `{ctorInfo.name}`,
          returns the value of the `{field.userName}` field, otherwise returns `none`."
        cmds := cmds.push <|← `(
          $docstring:docComment
          def $defname:ident $implicitBinders:explicitBinder*
          : $outType → Option $fieldType
          | $ctorPattern => some $fieldPat
          | x => none
        )

        -- ②: T.𝑐.𝑎! : T → α
        let defname : Name := ctorInfo.name ++ Name.mapHead (· ++ "!") field.userName
        let docstring := mkDocComment <| s!"If the given `{indVal.name}` is a `{ctorInfo.name}`,
          returns the value of the `{field.userName}` field, otherwise panics."
        cmds := cmds.push <|← `(
          $docstring:docComment
          def $(mkIdent defname):ident $implicitBinders:explicitBinder* [Inhabited $fieldType]
          : $outType → $fieldType
          | $ctorPattern => $fieldPat
          | x =>
            let n := $(quote ctor)
            panic! s!"expected constructor {n}")

        -- ③: T.𝑐.with𝑎 : α → T → T
        let defname : Name := ctorInfo.name ++ Name.mapHead (fun n => s!"with{n.capitalize}") field.userName
        let docstring := mkDocComment <| s!"If the given `{indVal.name}` is a `{ctorInfo.name}`,
          replaces the value of the `{field.userName}` field with the given value.
          Otherwise acts as the identity function."
        let a ← mkIdent <$> mkFreshUserName `a
        cmds := cmds.push <|← `(
          $docstring:docComment
          def $(mkIdent defname):ident $implicitBinders:explicitBinder*
          : $fieldType → $outType → $outType
          | $a, $ctorPattern => $(mkIdent ctorInfo.name):ident $(fieldPatterns.modify fieldIdx (fun _ => a)):term*
          | _, x => x
        )

        -- ④: T.𝑐.modify𝑎 : (α → α) → T → T
        let defname : Name := ctorInfo.name ++ Name.mapHead (fun n => s!"modify{n.capitalize}") field.userName
        let docstring := mkDocComment <| s!"If the given `{indVal.name}` is a `{ctorInfo.name}`,
          modifies the value of the `{field.userName}` field with the given `visit` function."
        let a ← mkIdent <$> mkFreshUserName `a
        let outPat ← fieldPatterns.modifyM fieldIdx (fun q => `( ($a <| $q) ))
        cmds := cmds.push <|← `(
          $docstring:docComment
          def $(mkIdent defname):ident $implicitBinders:explicitBinder*
          : (visit : $fieldType → $fieldType) → $outType → $outType
          | $a, $ctorPattern => $(mkIdent ctorInfo.name):ident $outPat:term*
          | _, x => x
        )

        -- ⑤: T.𝑐.modifyM𝑎 : (α → M α) → T → M T
        let defname : Name := ctorInfo.name ++ Name.mapHead (fun n => s!"modifyM{n.capitalize}") field.userName
        let docstring := mkDocComment <| s!"Runs the given `visit` function on the `{field.userName}` argument of `{ctorInfo.name}`.
          Performing the pure op if the given `{indVal.name}` is not a `{ctorInfo.name}`.

          This is also known as the affine traversal of the field in the van Laarhoven representation."
        let visit ← mkIdent <$> mkFreshUserName `visit
        let x ← mkIdent <$> mkFreshUserName `x
        let outPat := fieldPatterns.modify fieldIdx (fun _ => x)
        cmds := cmds.push <|← `(
          $docstring:docComment
          def $(mkIdent defname):ident $implicitBinders:explicitBinder*
            {M} [Pure M] [Functor M]
            : (visit : $fieldType → M $fieldType) → $outType → M $outType
            | $visit, $ctorPattern => (fun $x => $(mkIdent ctorInfo.name):ident $outPat:term*) <$> $visit $fieldPat
            | _, x => pure x
        )

      return cmds
    cmds.forM elabCommand

elab "derive_optics" decl:ident : command =>
  mkOptics decl.getId
