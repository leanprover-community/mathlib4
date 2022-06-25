/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
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

syntax (name := alias) "alias " ident " ← " ident* : command
syntax (name := aliasLR) "alias " ident " ↔ " binderIdent binderIdent : command
syntax (name := aliasLRDots) "alias " ident " ↔ " ".." : command

@[commandElab «alias»] def elabAlias : Elab.Command.CommandElab
| `(alias $name:ident ← $aliases:ident*) => do
  let resolved ← resolveGlobalConstNoOverload name
  let constant ← match (← Lean.getEnv).constants.find? resolved with
                 | none => throwError "failed to resolve alias LHS"
                 | some c => pure c

  for a in aliases do
    let decl ← match constant with
    | Lean.ConstantInfo.defnInfo d =>
      pure $ Lean.Declaration.defnDecl {
        d with name := a.getId
               value := mkConst resolved
      }
    | Lean.ConstantInfo.thmInfo t =>
      pure $ Lean.Declaration.thmDecl {
        t with name := a.getId
               value := mkConst resolved
      }
    | _ => throwError "alias only works with def or theorem"

    -- TODO add @alias attribute
    Lean.addDecl decl

| _ => Lean.Elab.throwUnsupportedSyntax


/--
  Given the type of an iff decl, produce a value for one of the implication
  directions (determined by `iffmp`).
-/
def mkIffMpApp (iffmp: Name) : Expr → (Nat → Expr) → MetaM Expr
| (Expr.forallE n varType body d), f => do
     let rest ← mkIffMpApp iffmp body (λ n => mkApp (f (n+1)) (mkBVar n))
     pure $ mkLambda n d.binderInfo varType rest
| (Expr.app (Expr.app (Expr.const ``Iff _ _) e1 _) e2 _), f =>
  pure $ mkApp3 (mkConst iffmp) e1 e2 (f 0)
| _, _ => throwError "Target theorem must have the form `∀ x y z, a ↔ b`"

/--
  Given a constant represent an iff decl, adds a decl for one of the implication
  directions.
-/
def aliasIff (ci : ConstantInfo) (al : Name) (isForward : Bool) : MetaM Unit := do
  let ls := ci.levelParams
  let t := ci.type
  let iffmp := if isForward then ``Iff.mp else ``Iff.mpr
  let v ← mkIffMpApp iffmp t (λ _ => mkConst ci.name (lvls := (ls.map mkLevelParam)))
  let t' ← Meta.inferType v
  -- TODO add @alias attribute
  addDecl $ Lean.Declaration.thmDecl {
      name := al
      value := v
      type := t'
      levelParams := ls
  }

@[commandElab aliasLR] def elabAliasLR : Lean.Elab.Command.CommandElab
| `(alias $name:ident ↔ $left:binderIdent $right:binderIdent ) => do
   let resolved ← resolveGlobalConstNoOverload name
   let constant ← match (← Lean.getEnv).constants.find? resolved with
                  | none => throwError "failed to resolve alias LHS"
                  | some c => pure c

   Lean.Elab.Command.liftTermElabM none do
     match left with
     | `(binderIdent| $x:ident) =>
       aliasIff constant x.getId true

     | `(binderIdent| _) => pure ()

     | _ => Lean.Elab.throwUnsupportedSyntax

     match right with
     | `(binderIdent| $x:ident) =>
       aliasIff constant x.getId false

     | `(binderIdent| _) => pure ()
     | _ => Lean.Elab.throwUnsupportedSyntax

| _ => Lean.Elab.throwUnsupportedSyntax

@[commandElab aliasLRDots] def elabAliasLRDots : Lean.Elab.Command.CommandElab
| `(alias $name:ident ↔ ..) => do
  let resolved ← resolveGlobalConstNoOverload name
  let constant ← match (← Lean.getEnv).constants.find? resolved with
                 | none => throwError "failed to resolve alias LHS"
                 | some c => pure c

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
