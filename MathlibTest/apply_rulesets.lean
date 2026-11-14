module

public import MathlibTest.ApplyRuleSetsAttr
import Qq

open Mathlib.Tactic.ApplyRuleSets

open Lean
ruleproc proc1 {A : Sort*} : A := fun _ _ => do
  logInfo m!"calling `proc1` on {A}"
  return none

@[test_rules]
ruleproc sortTrue {A : Sort*} : A := fun _ _ => do
  return some (Lean.mkConst ``True.intro)

ruleproc proc2 {A : Prop} : A := fun _ _ => do
  logInfo m!"calling `proc2` on {A}"
  return none

ruleproc proc3 (param : Nat), {A : Prop} : A := fun _ _ => do
  logInfo m!"calling `proc3` on {A} with param := {param}"
  return none

set_option linter.unusedTactic false in
ruleproc run_tactic (a b : Int) : a < b := by grind

example : (1 : Int) < 2 := by
  apply_rulesets [run_tactic]

example (p q : Prop) : p → q → p ∧ q := by
  fail_if_success apply_rulesets [test_rules, -Add.intro]
  apply_rulesets [test_rules]

example : True := by
  apply_rulesets [sortTrue]

def applyRuleSetsBigConj : Nat → (Nat → Prop) → Prop
  | 0, _ => True
  | n + 1, p => p n ∧ applyRuleSetsBigConj n p

-- This is intentionally large enough to exercise repeated recursive rule application, local
-- forall-hypothesis instantiation, and the success cache without relying on timing thresholds.
-- set_option trace.profiler true in
#time example (p : Nat → Prop) (h : ∀ i, p i) : applyRuleSetsBigConj 64 p := by
  dsimp [applyRuleSetsBigConj]
  apply_rulesets (config := { maxDepth := 200, transparency := .reducible }) +profile [And.intro, True.intro, h]

#time example (p : Nat → Prop) (h : ∀ i, p i) : applyRuleSetsBigConj 64 p := by
  dsimp [applyRuleSetsBigConj]
  apply_rulesets (config := { maxDepth := 200 }) [And.intro, True.intro, h]

inductive ApplyRuleSetsProfileClassGoal (α : Type) : Prop where
  | intro [Inhabited α]

theorem applyRuleSetsProfileClassRule {α : Type} [Inhabited α] :
    ApplyRuleSetsProfileClassGoal α :=
  .intro

inductive ApplyRuleSetsProfileDischarged : Prop where
  | intro

theorem applyRuleSetsProfileDischargedRule (_ : (0 : Nat) ≤ 0) :
    ApplyRuleSetsProfileDischarged :=
  .intro

def applyRuleSetsProfileStress : Nat → (Nat → Prop) → Prop
  | 0, _ => True
  | n + 1, p =>
    (p n ∧ applyRuleSetsProfileStress n p) ∧
      (p n → p n) ∧
      ApplyRuleSetsProfileClassGoal Nat ∧
      ApplyRuleSetsProfileClassGoal Nat ∧
      ApplyRuleSetsProfileDischarged ∧
      True

-- This intentionally mixes explicit-rule failures and successes, ruleset lookup, repeated local
-- forall-hypothesis instantiation, narrow introductions, typeclass synthesis, discharger fallback, and
-- repeated identical goals that can hit the success cache.
#time example (p : Nat → Prop) (h : ∀ i, p i) : applyRuleSetsProfileStress 16 p := by
  dsimp [applyRuleSetsProfileStress]
  apply_rulesets (config := { maxDepth := 300 }) +profile
    [test_rules, @applyRuleSetsProfileClassRule Nat inferInstance,
      applyRuleSetsProfileDischargedRule,
      True.intro, h, by decide]

#time example (p : Nat → Prop) (h : ∀ i, p i) : applyRuleSetsProfileStress 16 p := by
  dsimp [applyRuleSetsProfileStress]
  apply_rulesets (config := { maxDepth := 300, useRefinedDiscrTree := false }) +profile
    [test_rules, @applyRuleSetsProfileClassRule Nat inferInstance,
      applyRuleSetsProfileDischargedRule,
      True.intro, h, by decide]

example (p : Prop) (hp : p) : p := by
  apply_rulesets

example (p : Prop) (hp : p) : p := by
  apply_rulesets []

example : True := by
  fail_if_success apply_rulesets [test_rules, -exactTrue, -sortTrue]
  apply True.intro

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply_rulesets [test_rules, hp, hq]

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  fail_if_success apply_rulesets [test_rules, -And.intro, hp, hq]
  exact ⟨hp, hq⟩

example : True := by
  apply_rulesets [test_rules]

example (p : Prop) (hp : p) : p := by
  apply_rulesets [hp]

example (p : Prop) (hp : p) : p := by
  apply_rulesets [test_rules]

example (p q : Prop) : p → q → p ∧ q := by
  apply_rulesets [test_rules]

example : True := by
  apply_rulesets [id, by trivial]

example : True := by
  apply_rulesets [id, by assumption, by trivial]

-- Explicit theorem/term rules are tried directly.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply_rulesets [fun (hp : p) (hq : q) => And.intro hp hq, hp, hq]

-- Local hypotheses are used for proposition goals by default.
example (p : Prop) (hp : p) : p := by
  apply_rulesets [test_rules]

-- The local-assumption step can be disabled.
example (p : Prop) (hp : p) : p := by
  fail_if_success apply_rulesets (config := { assumption := false }) [test_rules]
  exact hp

-- Leading binders are introduced by default.
example (p q : Prop) : p → q → p ∧ q := by
  apply_rulesets [test_rules]

-- The intro step can be disabled.
example (p q : Prop) : p → q → p ∧ q := by
  fail_if_success apply_rulesets (config := { intro := false }) [test_rules]
  intro hp hq
  exact ⟨hp, hq⟩

-- The tactic-level discharger is only needed after recursive search and assumption fail.
example : True := by
  apply_rulesets [id, by trivial]

-- `autoParam` arguments are solved by running their embedded tactic.
example : True := by
  apply_rulesets [autoParamRule]

-- Ruleprocs are filtered by their pattern before being run.
example : NeedOther := by
  apply_rulesets [test_rules]

-- Ruleprocs receive origin information for theorem side goals.
example : FromFirst := by
  apply_rulesets [test_rules]

-- Ruleprocs can recursively call `applyRuleSets`.
example : DelegatedFromFirst := by
  apply_rulesets [test_rules]

-- Ruleproc declaration binders are synthesized and exposed as local `Expr` aliases in the body.
example : (3 : Nat) = 3 := by
  apply_rulesets [test_rules]

-- Ruleproc priority is respected.
example : (by apply_rulesets [test_rules] : Nat) = 2 := by
  rfl

-- Removing a ruleproc by name excludes it from the active candidate set.
example : Nat := by
  apply_rulesets [test_rules, -highNat]

example : (by apply_rulesets [test_rules, -highNat] : Nat) = 1 := by
  rfl

-- Maximum depth applies to recursive theorem-rule search.
example (p q : Prop) : p → q → p ∧ q := by
  fail_if_success apply_rulesets (config := { maxDepth := 0 }) [test_rules]
  intro hp hq
  exact ⟨hp, hq⟩

structure HasDeriv (f : α → β) (f' : α × α → β × β) : Prop where


namespace HasDeriv

theorem congr_deriv {f : α → β} {f' f''} (_ : HasDeriv f f') (_ : f' = f'')  :
    HasDeriv f f'' := ⟨⟩

@[has_deriv]
theorem id : HasDeriv (fun x : α => x) (fun xdx => xdx) := ⟨⟩

local instance [Add α] [Add β] : Add (α × β) := ⟨fun (x,y) (x',y') => (x+x', y+y')⟩

@[has_deriv]
theorem add [Add β] (f g : α → β) (_ : HasDeriv f f') (_ : HasDeriv g g') :
    HasDeriv (fun x : α => f x + g x) (fun xdx => f' xdx + g' xdx) := ⟨⟩

@[has_deriv]
theorem mul [Add β] [Mul β] (f g : α → β) (_ : HasDeriv f f') (_ : HasDeriv g g') :
    HasDeriv (fun x : α => f x * g x) (fun xdx =>
      let (y,dy) := f' xdx
      let (z,dz) := g' xdx
      let y := y; let z := z
      (y * z, dy * z + y * dz)) := ⟨⟩

@[has_deriv high]
theorem div_bad [Div β] (f g : α → β) (_ : HasDeriv f f') (_ : HasDeriv g g')
    (_ : False) :
    HasDeriv (fun x : α => f x / g x) (fun xdx => f' xdx) := ⟨⟩

@[has_deriv]
theorem div_good [Add β] [Sub β] [Mul β] [Div β] [One β] (f g : α → β)
    (_ : HasDeriv f f') (_ : HasDeriv g g') :
    HasDeriv (fun x : α => f x / g x) (fun xdx =>
      let (y,dy) := f' xdx; let (z,dz) := g' xdx;
      let y := y; let z := z;
      let iz := 1/z
      (y*iz, (iz*iz)*(dy * z - y * dz))) := ⟨⟩

example : HasDeriv (fun x : Nat => x) (fun xdx => xdx) := by
  apply congr_deriv
  · apply_rulesets [has_deriv]
  · rfl

example : HasDeriv (fun x : Nat => x + x + x) (fun xdx => xdx + xdx + xdx) := by
  apply congr_deriv
  · apply_rulesets [has_deriv]
  · rfl

example : HasDeriv (fun x : Nat => x / x) (fun xdx =>
      have y := xdx.fst;
      have z := xdx.fst;
      have iz := 1 / z;
      (y * iz, iz * iz * (xdx.snd * z - y * xdx.snd))) := by
  apply congr_deriv
  · apply_rulesets [has_deriv]
  · simp -zeta []; rfl


example : HasDeriv (fun x : Nat => (x * x + x) / ((x + x)*(x + x))) sorry := by
  apply congr_deriv
  · apply_rulesets [has_deriv]
  · sorry

end HasDeriv

namespace Addition
open Lean Meta Qq

-- turn all Add instances to `test_rules`
run_meta
  let [u] ← mkFreshLevelMVars 1 | unreachable!
  let A ← mkFreshExprMVar (mkSort u)
  let e := Expr.app (.const ``Add [u]) A

  let globalInstances ← getGlobalInstancesIndex
  let candidates ← globalInstances.getUnify e
  for inst in candidates do
    let some name := inst.globalName? | continue
    addTheoremRule `test_rules name .global inst.priority

-- implement addition on structures
@[test_rules (low+1)]
ruleproc structure_add {A : Type _} : Add A := fun _ _ => do
  let .const fn _ := A.getAppFn' | return none
  let env ← getEnv
  unless isStructure env fn do return none

  let ctor := getStructureCtor env fn
  let parms := A.getAppArgs
  let ctorVal ← mkAppOptM ctor.name (parms.map some)

  let (xs, _, _) ← forallMetaTelescope (← inferType ctorVal)
  let r ←
    withLocalDeclD `a A fun a => do
    withLocalDeclD `b A fun b => do
      for x in xs, i in [0:xs.size] do
        let X ← inferType x
        let addCls ← mkAppM ``Add #[X]
        let addInst ← applyRuleSets default addCls
        let ci ← mkAppOptM ``Add.add #[X, addInst, a.proj fn i, b.proj fn i]
        x.mvarId!.assign ci

      mkLambdaFVars #[a,b] (mkAppN ctorVal xs)

  return ← mkAppM ``Add.mk #[r]

structure Vec3 (α : Type _) where
  (x y z : α)

example : Add (Vec3 (Vec3 Nat)) := by apply_rulesets [test_rules]

-- run_meta
--   let globalInstances ← getGlobalInstancesIndex
--   for inst in globalInstances.elements do
--     let some name := inst.globalName? | continue
--     addTheoremRule `tc_rules name .global inst.priority

-- #check (by apply_rulesets [tc_rules, structure_add] : Add (Vec3 (Vec3 Nat)))

end Addition
