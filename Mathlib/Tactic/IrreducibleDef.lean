/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathlib.Data.Subtype
import Mathlib.Tactic.Eqns
import Mathlib.Util.TermReduce

/-!
# Irreducible definitions

This file defines an `irreducible_def` command,
which works almost like the `def` command
except that the introduced definition
does not reduce to the value.
Instead, the command
adds a `_def` lemma
which can be used for rewriting.

```
irreducible_def frobnicate (a b : Nat) :=
  a + b

example : frobnicate a 0 = a := by
  simp [frobnicate_def]
```

-/

namespace Lean.Elab.Command

open Term Meta

/-- `eta_helper f = (· + 3)` elabs to `∀ x, f x = x + 3` -/
local elab "eta_helper " t:term : term => do
  let t ← elabTerm t none
  let some (_, lhs, rhs) := t.eq? | throwError "not an equation: {t}"
  synthesizeSyntheticMVars
  let rhs ← instantiateMVars rhs
  lambdaTelescope rhs fun xs rhs ↦ do
    let lhs := (mkAppN lhs xs).headBeta
    mkForallFVars xs <|← mkEq lhs rhs

/-- `val_proj x` elabs to the *primitive projection* `@x.val`. -/
local elab "val_proj " e:term : term => do
  let e ← elabTerm (← `(($e : Subtype _))) none
  return mkProj ``Subtype 0 e

/--
Executes the commands,
and stops after the first error.
In short, S-A-F-E.
-/
local syntax "stop_at_first_error" (ppLine command)* : command
open Command in elab_rules : command
  | `(stop_at_first_error $[$cmds]*) => do
    for cmd in cmds do
      elabCommand cmd.raw
      if (← get).messages.hasErrors then break

syntax irredDefLemma := atomic(" (" &"lemma" " := ") ident ")"

/--
Introduces an irreducible definition.
`irreducible_def foo := 42` generates
a constant `foo : Nat` as well as
a theorem `foo_def : foo = 42`.
-/
elab mods:declModifiers "irreducible_def" n_id:declId n_def:(irredDefLemma)?
    declSig:ppIndent(optDeclSig) val:declVal :
    command => do
  let declSig : TSyntax ``Parser.Command.optDeclSig := ⟨declSig.raw⟩ -- HACK
  let (n, us) ← match n_id with
    | `(Parser.Command.declId| $n:ident $[.{$us,*}]?) => pure (n, us)
    | _ => throwUnsupportedSyntax
  let us' := us.getD { elemsAndSeps := #[] }
  let n_def ← match n_def.getD ⟨mkNullNode⟩ with
    | `(irredDefLemma| (lemma := $id)) => pure id
    | _ => pure <| mkIdentFrom n <| (·.review) <|
      let scopes := extractMacroScopes n.getId
      { scopes with name := scopes.name.appendAfter "_def" }
  let `(Parser.Command.declModifiersF|
      $[$doc:docComment]? $[@[$attrs,*]]?
      $[$vis]? $[$prot:protected]? $[$nc:noncomputable]? $[$uns:unsafe]?) := mods
    | throwError "unsupported modifiers {format mods}"
  let attrs := attrs.getD {}
  let priv := vis.filter (· matches `(Parser.Command.visibility| private))
  elabCommand <|<- `(stop_at_first_error
    $[$nc:noncomputable]? $[$uns]? def definition$[.{$us,*}]? $declSig:optDeclSig $val
    $[$nc:noncomputable]? $[$uns]? opaque wrapped$[.{$us,*}]? : Subtype (Eq @definition.{$us',*}) :=
      ⟨_, rfl⟩
    $[$doc:docComment]? $[private%$priv]? $[$nc:noncomputable]? $[$uns]?
    def $n:ident$[.{$us,*}]? :=
      val_proj @wrapped.{$us',*}
    $[private%$priv]? $[$uns:unsafe]? theorem $n_def:ident $[.{$us,*}]? :
        eta_helper Eq @$n.{$us',*} @(delta% @definition) := by
      intros
      delta $n:ident
      rw [show wrapped = ⟨@definition.{$us',*}, rfl⟩ from Subtype.ext wrapped.2.symm]
      rfl
    attribute [irreducible] $n definition
    attribute [eqns $n_def] $n
    attribute [$attrs:attrInstance,*] $n)
  if prot.isSome then
    modifyEnv (addProtected · ((← getCurrNamespace) ++ n.getId))

end Lean.Elab.Command
