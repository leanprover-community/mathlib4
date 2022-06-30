/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw
-/
import Lean.Elab.Command
import Lean.Elab.Term
import Lean

/-!
# The `alias` command

This file defines an `alias` command, which can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.
-/

namespace Tactic
namespace Alias

open Lean

/-- Adds some copies of a theorem or definition. -/
syntax (name := alias) "alias " ident " ← " ident* : command

/-- Adds one-way implication declarations. -/
syntax (name := aliasLR) "alias " ident " ↔ " binderIdent binderIdent : command

/-- Adds one-way implication declarations, inferring names for them. -/
syntax (name := aliasLRDots) "alias " ident " ↔ " ".." : command

/-- Like `++`, except that if the right argument starts with `_root_` the namespace will be
ignored.
```
appendNamespace `a.b `c.d = `a.b.c.d
appendNamespace `a.b `_root_.c.d = `c.d
```

TODO: Move this declaration to a more central location.
-/
def appendNamespace (ns : Name) : Name → Name
| Name.str Name.anonymous s _ => if s = "_root_" then Name.anonymous else Name.mkStr ns s
| Name.str p s _              => Name.mkStr (appendNamespace ns p) s
| Name.num p n _              => Name.mkNum (appendNamespace ns p) n
| Name.anonymous              => ns

/-- Elaborates an `alias ←` command. -/
@[commandElab «alias»] def elabAlias : Elab.Command.CommandElab
| `(alias $name:ident ← $aliases:ident*) => do
  let resolved ← resolveGlobalConstNoOverload name
  let constant ← getConstInfo resolved
  let ns ← getCurrNamespace

  for a in aliases do
    let decl ← match constant with
    | Lean.ConstantInfo.defnInfo d =>
      pure $ .defnDecl {
        d with name := (appendNamespace ns a.getId)
               value := mkConst resolved (d.levelParams.map mkLevelParam)
      }
    | Lean.ConstantInfo.thmInfo t =>
      pure $ .thmDecl {
        t with name := (appendNamespace ns a.getId)
               value := mkConst resolved (t.levelParams.map mkLevelParam)
      }
    | _ => throwError "alias only works with def or theorem"

    -- TODO add @alias attribute
    Lean.addDecl decl

| _ => Lean.Elab.throwUnsupportedSyntax


/--
  Given a possibly forall-quantified iff expression `prf`, produce a value for one
  of the implication directions (determined by `mp`).
-/
def mkIffMpApp (mp : Bool) (prf : Expr) : MetaM Expr := do
  Meta.forallTelescope (← Meta.inferType prf) fun xs ty => do
    let some (lhs, rhs) := ty.iff?
        | throwError "Target theorem must have the form `∀ x y z, a ↔ b`"
    Meta.mkLambdaFVars xs <|
      mkApp3 (mkConst (if mp then ``Iff.mp else ``Iff.mpr)) lhs rhs (mkAppN prf xs)

/--
  Given a constant representing an iff decl, adds a decl for one of the implication
  directions.
-/
def aliasIff (ci : ConstantInfo) (al : Name) (isForward : Bool) : MetaM Unit := do
  let ls := ci.levelParams
  let v ← mkIffMpApp isForward ci.value!
  let t' ← Meta.inferType v
  -- TODO add @alias attribute
  addDecl $ .thmDecl {
      name := al
      value := v
      type := t'
      levelParams := ls
  }

/-- Elaborates an `alias ↔` command. -/
@[commandElab aliasLR] def elabAliasLR : Lean.Elab.Command.CommandElab
| `(alias $name:ident ↔ $left:binderIdent $right:binderIdent ) => do
   let resolved ← resolveGlobalConstNoOverload name
   let constant ← getConstInfo resolved
   let ns ← getCurrNamespace

   Lean.Elab.Command.liftTermElabM none do
     if let `(binderIdent| $x:ident) := left
     then aliasIff constant (appendNamespace ns x.getId) true

     if let `(binderIdent| $x:ident) := right
     then aliasIff constant (appendNamespace ns x.getId) false

| _ => Lean.Elab.throwUnsupportedSyntax

/-- Elaborates an `alias ↔ ..` command. -/
@[commandElab aliasLRDots] def elabAliasLRDots : Lean.Elab.Command.CommandElab
| `(alias $name:ident ↔ ..) => do
  let resolved ← resolveGlobalConstNoOverload name
  let constant ← getConstInfo resolved

  let (parent, base) ← match resolved with
                       | Name.str n s _ => pure (n,s)
                       | _ => throwError "alias only works for string names"

  let components := base.splitOn "_iff_"
  if components.length != 2 then throwError "LHS must be of the form *_iff_*"
  let forward := String.intercalate "_of_" components.reverse
  let backward := String.intercalate "_of_" components
  let forwardName := Name.mkStr parent forward
  let backwardName := Name.mkStr parent backward

  Lean.Elab.Command.liftTermElabM none do
    aliasIff constant forwardName true
    aliasIff constant backwardName false

| _ => Lean.Elab.throwUnsupportedSyntax

end Alias
end Tactic
