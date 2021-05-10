import Mathlib.Tactic.Split
import Lean.Elab.Command
import Lean.Elab.Match
import Lean.Util.FoldConsts
import Lean.Data.OpenDecl

open Lean Parser.Tactic Elab Command

namespace Lean

def Meta.collectPrivateIn [Monad m] [MonadEnv m] [MonadError m]
  (n : Name) (set := NameSet.empty) : m NameSet := do
  let c ← getConstInfo n
  let tgt := `elabMatchAux
  pure $ Expr.foldConsts c.value! set fun c a =>
    if isPrivateName c && tgt.isSuffixOf c then a.insert c else a

namespace Elab.Command

def elabOpenPrivateLike (ids tgts : Array Syntax)
  (a : α) (f : (priv full user : Name) → α → CommandElabM α) : CommandElabM α := do
  let mut names := NameSet.empty
  for tgt in tgts do
    let n ← resolveGlobalConstNoOverload tgt.getId
    names ← Meta.collectPrivateIn n names
  let mut a := a
  for n in ids do
    let n := n.getId
    let mut found := []
    for c in names do
      if n.isSuffixOf c then
        found := c::found
    match found with
    | [] =>
      let mut msg := s!"'{n}' not found in the provided declarations:\n"
      for c in names do
        if let some name := privateToUserName? c then
          msg := msg ++ s!"{name}\n"
      throwError msg
    | [c] =>
      if let some name := privateToUserName? c then
         a ← f c name n a
      else unreachable!
    | _ => throwError s!"provided name is ambiguous: found {found.map privateToUserName?}"
  a

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
| `(open private $ids* in $tgts*) => do
  let decls ← elabOpenPrivateLike ids tgts #[] fun c _ n decls =>
    decls.push (OpenDecl.explicit n c)
  modifyScope fun scope => do
    let mut openDecls := scope.openDecls
    for decl in decls do
      openDecls := decl::openDecls
    { scope with openDecls := openDecls }
| _ => throwUnsupportedSyntax

syntax (name := exportPrivate) "export private " ident* " in " ident* : command

/--
The command `export private a b c in foo bar` is similar to `open private`, but instead of opening
them in the current scope it will create public aliases to the private definition. The definition
will exist at exactly the original location and name, as if the `private` keyword was not used
originally.
-/
@[commandElab exportPrivate] def elabExportPrivate : CommandElab
| `(export private $ids* in $tgts*) =>
  elabOpenPrivateLike ids tgts () fun c name _ _ => do
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
| _ => throwUnsupportedSyntax

end Elab.Command
end Lean