import Mathlib.AutoIndPrincipleAttr

/-!

## TODOS

- check if variable name exists in `autoinduction` attribute

-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Lean Elab Tactic Meta

def foobar' (n : Nat := by simp) : Nat := n

@[autoinduction (foo := by omega) (bla := by simp)]
lemma foobar (foo bla : Nat) : foo = bla :=
  sorry

#autoindprinciples

syntax (name := autoinductiontac) "autoinduction" term : tactic

def AutoIndPrinciple.matches (_a : AutoIndPrinciple) (_e : Expr) : MetaM Bool :=
  pure true

def autoInductOn (e : Expr) : TacticM Unit := do
  let ty ← inferType e
  logInfo s!"Found expression {e} with inferred type {ty}."
  let ps ← getAutoIndPrinciples
  for principle in ps do
    if (← principle.matches ty) then
    logInfo s!"applying {principle.name}"
    -- ...

elab_rules : tactic
| `(tactic|autoinduction $t) => withMainContext do
  let e ← elabTerm t none
  autoInductOn e

example : True := by
  autoinduction 3
  trivial

--syntax (name := autoinductiontac) "autoinduction"
