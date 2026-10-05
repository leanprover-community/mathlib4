/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Util.AtLocation
public import Mathlib.Tactic.TryThis
public import Mathlib.Tactic.Hint
public meta import Lean.Elab.Tactic.Config
public meta import Lean.Elab.Tactic.Conv.Simp
public meta import Mathlib.Tactic.Conv
public meta import Lean.Meta.Sym.Simp.Main
public meta import Lean.Meta.Sym.Canon
public meta import Lean.Meta.Sym.Arith.Norm
public meta import Lean.Meta.Sym.Arith.Module

/-!
# The `abel` tactic

Evaluate expressions in the language of additive, commutative monoids and groups.

-/

public section

-- TODO: assert_not_exists NonUnitalNonAssociativeSemiring
assert_not_exists IsOrderedMonoid TopologicalSpace PseudoMetricSpace

namespace Mathlib.Tactic.Abel

meta section

open Lean Elab Meta Tactic

/--
`abel` solves equations in the language of *additive*, commutative monoids and groups.

`abel` and its variants work as both tactics and conv tactics.

* `abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `abel_nf` rewrites all group expressions into a normal form.
  * `abel_nf at h` rewrites in a hypothesis.
  * `abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
* `abel!`, `abel1!`, `abel_nf!` also unfold atoms at default transparency and local `let` variables.

Examples:
```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```
-/
syntax (name := abel) "abel" "!"? : tactic

/-- Configuration for `abel_nf`. -/
structure AbelNF.Config where
  /-- Unfold local let variables. -/
  zetaDelta := false
  /-- Transparency used to reduce atoms before normalization. -/
  red := TransparencyMode.reducible

/-- Elaborate `abel_nf` configuration. -/
declare_config_elab elabAbelNFConfig AbelNF.Config

/-- Normalize scalar arithmetic and additive expressions inside atoms. -/
private def simpAtom (cfg : AbelNF.Config) (e : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
  if !e.hasFVar && !e.hasMVar then
    let type ← inferType e
    if type.isConstOf ``Nat || type.isConstOf ``Int then
      return ← Sym.Arith.normalize? e (fun _ => pure .rfl)
  let e' ← if cfg.red == .reducible then pure e else withTransparency cfg.red <| whnf e
  let e' ← Sym.shareCommon (← Sym.canon e')
  -- Revisit only the children: an unsupported operation is also an atom.
  let methods ← Sym.Simp.getMethods
  let methods := { methods with pre := fun x => do
      if Sym.isSameExpr x e' then pure .rfl else methods.pre x }
  let r ← withReader (fun (_ : Sym.Simp.MethodsRef) => methods.toMethodsRef) <| Sym.Simp.simp e'
  if e == e' then return r
  match r with
  | .rfl _ cd => return .step e' (← mkEqRefl e') (done := true) (contextDependent := cd)
  | .step e'' proof _ cd => return .step e'' proof (done := true) (contextDependent := cd)

private def methods (cfg : AbelNF.Config) : Sym.Simp.Methods :=
  { pre := fun e => Sym.Arith.normalizeAdd? e (simpAtom cfg)
    post := fun e => do
      let_expr Eq _ a b := e | return .rfl
      unless ← withTransparency .default <| isDefEq a b do return .rfl
      return .step (← Sym.getTrueExpr) (← mkAppM ``eq_self #[a]) (done := true) }

/-- Normalize maximal additive expressions and recurse into their atoms. -/
private def normalize (cfg : AbelNF.Config) (e : Expr) : MetaM Simp.Result :=
    withConfig ({ · with zetaDelta := cfg.zetaDelta }) <| withNewMCtxDepth do
  let r ← Sym.SymM.run do
    Sym.Simp.SimpM.run' (Sym.Simp.simp (← Sym.shareCommon (← Sym.canon e))) (methods cfg)
  match r with
  | .rfl .. => return { expr := e }
  | .step e' proof .. =>
    if ← withTransparency .default <| isDefEq e e' then return { expr := e }
    return { expr := e', proof? := proof }

@[tactic_alt abel]
elab (name := abel1) "abel1" tk:"!"? : tactic => withMainContext do
  let type ← instantiateMVars (← getMainTarget)
  let cfg : AbelNF.Config :=
    if tk.isSome then { red := .default, zetaDelta := true } else { zetaDelta := true }
  let some proof ← withConfig ({ · with zetaDelta := cfg.zetaDelta }) <| Sym.SymM.run do
      Sym.Simp.SimpM.run'
        (Sym.Arith.proveAddEq?
          (← Sym.shareCommon (← Sym.canon type)) (simpAtom cfg)) (methods cfg)
    | throwError "`abel1` found that the two sides were not equal"
  let proof ← Lean.Meta.mkAuxTheorem type proof (zetaDelta := true) (kind? := `_abel)
  closeMainGoal `abel1 proof

@[tactic_alt abel]
macro (name := abel1!) "abel1!" : tactic => `(tactic| abel1 !)

open Parser.Tactic

@[tactic_alt abel]
elab (name := abelNF) "abel_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabAbelNFConfig cfg
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  transformAtLocation (fun e => normalize cfg e) "abel_nf" loc (ifUnchanged := .error) false

@[tactic_alt abel]
macro "abel_nf!" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| abel_nf ! $cfg:optConfig $(loc)?)

@[inherit_doc abel]
syntax (name := abelNFConv) "abel_nf" "!"? optConfig : conv

/-- Elaborator for the `abel_nf` tactic. -/
@[tactic abelNFConv]
def elabAbelNFConv : Tactic := fun stx ↦ match stx with
  | `(conv| abel_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabAbelNFConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    Conv.applySimpResult (← normalize cfg (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

@[inherit_doc abel]
macro "abel_nf!" cfg:optConfig : conv => `(conv| abel_nf ! $cfg:optConfig)

macro_rules
  | `(tactic| abel !) => `(tactic| first | abel1! | try_this abel_nf!)
  | `(tactic| abel) => `(tactic| first | abel1 | try_this abel_nf)

@[tactic_alt abel]
macro "abel!" : tactic => `(tactic| abel !)

@[inherit_doc abel]
macro (name := abelConv) "abel" : conv =>
  `(conv| first | discharge => abel1 | try_this abel_nf)

@[inherit_doc abelConv] macro "abel!" : conv =>
  `(conv| first | discharge => abel1! | try_this abel_nf!)

end

end Mathlib.Tactic.Abel

/-!
We register `abel` with the `hint` tactic.
-/

register_hint 950 abel
