/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Util.FoldConsts

open Lean Parser.Tactic Elab Command

namespace Lean

def Meta.collectPrivateIn [Monad m] [MonadEnv m] [MonadError m]
  (n : Name) (set := NameSet.empty) : m NameSet := do
  let c ← getConstInfo n
  pure $ Expr.foldConsts c.value! set fun c a =>
    if isPrivateName c then a.insert c else a

namespace Elab.Command

def elabOpenPrivateLike (ids tgts : Array Syntax)
  (f : (priv full user : Name) → CommandElabM Name) : CommandElabM Unit := do
  let mut names := NameSet.empty
  for tgt in tgts do
    let n ← resolveGlobalConstNoOverload tgt.getId
    names ← Meta.collectPrivateIn n names
  let appendNames (msg : String) : String := do
    let mut msg := msg
    for c in names do
      if let some name := privateToUserName? c then
        msg := msg ++ s!"{name}\n"
    msg
  if ids.isEmpty && !names.isEmpty then
    logInfo (appendNames "found private declarations:\n")
  let mut decls := #[]
  for n in ids do
    let n := n.getId
    let mut found := []
    for c in names do
      if n.isSuffixOf c then
        found := c::found
    match found with
    | [] => throwError (appendNames s!"'{n}' not found in the provided declarations:\n")
    | [c] =>
      if let some name := privateToUserName? c then
        let new ← f c name n
        decls := decls.push (OpenDecl.explicit n new)
      else unreachable!
    | _ => throwError s!"provided name is ambiguous: found {found.map privateToUserName?}"
  modifyScope fun scope => do
    let mut openDecls := scope.openDecls
    for decl in decls do
      openDecls := decl::openDecls
    { scope with openDecls := openDecls }

syntax (name := openPrivate) "open private " ident* " in " ident* : command

/--
The command `open private a b c in foo bar` will look for private definitions named `a`, `b`, `c`
in declarations `foo` and `bar` and open them in the current scope. This does not make the
definitions public, but rather makes them accessible in the current section by the short name `a`
instead of the (unnameable) internal name for the private declaration, something like
`_private.Other.Module.0.Other.Namespace.foo.a`, which cannot be typed directly because of the `0`
name component.
-/
@[commandElab openPrivate] def elabOpenPrivate : CommandElab
| `(open private $ids* in $tgts*) =>
  elabOpenPrivateLike ids tgts fun c _ _ => c
| _ => throwUnsupportedSyntax

syntax (name := exportPrivate) "export private " ident* " in " ident* : command

/--
The command `export private a b c in foo bar` is similar to `open private`, but instead of opening
them in the current scope it will create public aliases to the private definition. The definition
will exist at exactly the original location and name, as if the `private` keyword was not used
originally.

It will also open the newly created alias definition under the provided short name, like
`open private`.
-/
@[commandElab exportPrivate] def elabExportPrivate : CommandElab
| `(export private $ids* in $tgts*) =>
  elabOpenPrivateLike ids tgts fun c name _ => do
    let cinfo ← getConstInfo c
    if (← getEnv).contains name then
      throwError s!"'{name}' has already been declared"
    let decl := Declaration.defnDecl {
      name := name,
      levelParams := cinfo.levelParams,
      type := cinfo.type,
      value := mkConst c (cinfo.levelParams.map mkLevelParam),
      hints := ReducibilityHints.abbrev,
      safety := if cinfo.isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe
    }
    addDecl decl
    compileDecl decl
    name
| _ => throwUnsupportedSyntax

end Elab.Command
end Lean
