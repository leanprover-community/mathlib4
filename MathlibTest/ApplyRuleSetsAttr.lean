module

public import MathlibTest.ApplyRuleSetsRegister
-- import Mathlib

open Mathlib.Tactic.ApplyRuleSets

public section

attribute [test_rules] And.intro

@[test_rules]
ruleproc exactTrue : True := fun _ _ => do
  return some (Lean.mkConst ``True.intro)

inductive NeedFirst : Prop where
  | intro

inductive NeedOther : Prop where
  | intro

inductive FromFirst : Prop where
  | intro (first : NeedFirst)

inductive DelegatedFromFirst : Prop where
  | intro (first : NeedFirst)

theorem fromFirstRule (first : NeedFirst) : FromFirst :=
  FromFirst.intro first

attribute [test_rules] fromFirstRule

@[test_rules]
ruleproc solveNeedFirst : NeedFirst := fun origin _ => do
  if origin.argName == some `first then
    return some (Lean.mkConst ``NeedFirst.intro)
  else
    return none

@[test_rules]
ruleproc solveNeedOther : NeedOther := fun _ _ => do
  return some (Lean.mkConst ``NeedOther.intro)

@[test_rules]
ruleproc solveDelegatedFromFirst : DelegatedFromFirst := fun _ _ => do
  let some first ← applyRuleSets
      { ruleName := `solveDelegatedFromFirst, argName := some `first } (Lean.mkConst ``NeedFirst)
    | return none
  return some (Lean.mkApp (Lean.mkConst ``DelegatedFromFirst.intro) first)

@[test_rules 100]
ruleproc lowNat : Nat := fun _ _ => do
  return some (Lean.mkNatLit 1)

@[test_rules 200]
ruleproc highNat : Nat := fun _ _ => do
  return some (Lean.mkNatLit 2)

@[test_rules]
ruleproc wrongPatternProc : NeedOther := fun _ _ => do
  return some (Lean.mkConst ``True.intro)

def autoParamSource (h : True := by trivial) : True := h

theorem autoParamRule (h : autoParam True autoParamSource._auto_1) : True := h

@[test_rules]
ruleproc reflByProc {A : Type} (a : A) : a = a := fun _ _ => do
  return some (← Lean.Meta.mkAppM ``Eq.refl #[a])
