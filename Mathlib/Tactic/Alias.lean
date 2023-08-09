/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw
-/
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

open Lean Elab Parser.Command

/-- Adds some copies of a theorem or definition. -/
syntax (name := alias) (docComment)? "alias " ident " ←" (ppSpace ident)* : command

/-- Adds one-way implication declarations. -/
syntax (name := aliasLR) (docComment)?
  "alias " ident " ↔ " binderIdent ppSpace binderIdent : command

/-- Adds one-way implication declarations, inferring names for them. -/
syntax (name := aliasLRDots) (docComment)? "alias " ident " ↔ " ".." : command

/-- Like `++`, except that if the right argument starts with `_root_` the namespace will be
ignored.
```
appendNamespace `a.b `c.d = `a.b.c.d
appendNamespace `a.b `_root_.c.d = `c.d
```

TODO: Move this declaration to a more central location.
-/
def appendNamespace (ns : Name) : Name → Name
  | .str .anonymous s => if s = "_root_" then Name.anonymous else Name.mkStr ns s
  | .str p s          => Name.mkStr (appendNamespace ns p) s
  | .num p n          => Name.mkNum (appendNamespace ns p) n
  | .anonymous        => ns

/-- An alias can be in one of three forms -/
inductive Target
  | plain : Name → Target
  | forward : Name → Target
  | backwards : Name → Target

/-- The name underlying an alias target -/
def Target.toName : Target → Name
  | Target.plain n => n
  | Target.forward n => n
  | Target.backwards n => n

/-- The docstring for an alias. -/
def Target.toString : Target → String
  | Target.plain n => s!"**Alias** of `{n}`."
  | Target.forward n => s!"**Alias** of the forward direction of `{n}`."
  | Target.backwards n => s!"**Alias** of the reverse direction of `{n}`."

/-- Elaborates an `alias ←` command. -/
@[command_elab «alias»] def elabAlias : Command.CommandElab
| `($[$doc]? alias $name:ident ← $aliases:ident*) => do
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let constant ← getConstInfo resolved
  let ns ← getCurrNamespace
  for a in aliases do withRef a do
    let declName := appendNamespace ns a.getId
    let decl ← match constant with
    | Lean.ConstantInfo.defnInfo d =>
      pure $ .defnDecl {
        d with name := declName
               value := mkConst resolved (d.levelParams.map mkLevelParam)
      }
    | Lean.ConstantInfo.thmInfo t =>
      pure $ .thmDecl {
        t with name := declName
               value := mkConst resolved (t.levelParams.map mkLevelParam)
      }
    | _ => throwError "alias only works with def or theorem"
    checkNotAlreadyDeclared declName
    addDeclarationRanges declName {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange a
    }
    -- TODO add @alias attribute
    Command.liftTermElabM do
      if isNoncomputable (← getEnv) resolved then
        addDecl decl
        setEnv $ addNoncomputable (← getEnv) declName
      else
        addAndCompile decl
      Term.addTermInfo' a (← mkConstWithLevelParams declName) (isBinder := true)
      let target := Target.plain resolved
      let docString := match doc with | none => target.toString
                                      | some d => d.getDocString
      addDocString declName docString
| _ => throwUnsupportedSyntax

/--
  Given a possibly forall-quantified iff expression `prf`, produce a value for one
  of the implication directions (determined by `mp`).
-/
def mkIffMpApp (mp : Bool) (ty prf : Expr) : MetaM Expr := do
  Meta.forallTelescope ty fun xs ty ↦ do
    let some (lhs, rhs) := ty.iff?
      | throwError "Target theorem must have the form `∀ x y z, a ↔ b`"
    Meta.mkLambdaFVars xs <|
      mkApp3 (mkConst (if mp then ``Iff.mp else ``Iff.mpr)) lhs rhs (mkAppN prf xs)

/--
  Given a constant representing an iff decl, adds a decl for one of the implication
  directions.
-/
def aliasIff (doc : Option (TSyntax `Lean.Parser.Command.docComment)) (ci : ConstantInfo)
  (ref : Syntax) (al : Name) (isForward : Bool) :
  TermElabM Unit := do
  let ls := ci.levelParams
  let v ← mkIffMpApp isForward ci.type ci.value!
  let t' ← Meta.inferType v
  -- TODO add @alias attribute
  addDeclarationRanges al {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange ref
  }
  addDecl $ .thmDecl {
    name := al
    value := v
    type := t'
    levelParams := ls
  }
  Term.addTermInfo' ref (← mkConstWithLevelParams al) (isBinder := true)
  let target := if isForward then Target.forward ci.name else Target.backwards ci.name
  let docString := match doc with | none => target.toString
                                  | some d => d.getDocString
  addDocString al docString

/-- Elaborates an `alias ↔` command. -/
@[command_elab aliasLR] def elabAliasLR : Command.CommandElab
| `($[$doc]? alias $name:ident ↔ $left:binderIdent $right:binderIdent) => do
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let constant ← getConstInfo resolved
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    if let `(binderIdent| $x:ident) := left then
      aliasIff doc constant x (appendNamespace ns x.getId) true
    if let `(binderIdent| $x:ident) := right then
      aliasIff doc constant x (appendNamespace ns x.getId) false
| _ => throwUnsupportedSyntax

/-- Elaborates an `alias ↔ ..` command. -/
@[command_elab aliasLRDots] def elabAliasLRDots : Command.CommandElab
| `($[$doc]? alias $name:ident ↔ ..%$tk) => do
  let resolved ← resolveGlobalConstNoOverloadWithInfo name
  let constant ← getConstInfo resolved
  let (parent, base) ← match resolved with
    | .str n s => pure (n, s)
    | _ => throwError "alias only works for string names"
  let components := base.splitOn "_iff_"
  if components.length != 2 then throwError "LHS must be of the form *_iff_*"
  let forward := String.intercalate "_of_" components.reverse
  let backward := String.intercalate "_of_" components
  let forwardName := Name.mkStr parent forward
  let backwardName := Name.mkStr parent backward
  Command.liftTermElabM do
    aliasIff doc constant tk forwardName true
    aliasIff doc constant tk backwardName false
| _ => throwUnsupportedSyntax

end Alias
end Tactic
