module

public import MathlibTest.ApplyRuleSetsRegister

open Mathlib.Tactic.ApplyRuleSets

public section

attribute [test_rules] And.intro

ruleproc_decl exactTrue : True := fun _ _ => do
  return some (Lean.mkConst ``True.intro)

attribute [test_rules] exactTrue

inductive NeedFirst : Prop where
  | intro

inductive NeedOther : Prop where
  | intro

inductive FromFirst : Prop where
  | intro (first : NeedFirst)

theorem fromFirstRule (first : NeedFirst) : FromFirst :=
  FromFirst.intro first

attribute [test_rules] fromFirstRule

ruleproc_decl solveNeedFirst : NeedFirst := fun origin _ => do
  if origin.argName == some `first then
    return some (Lean.mkConst ``NeedFirst.intro)
  else
    return none

attribute [test_rules] solveNeedFirst

ruleproc_decl solveNeedOther : NeedOther := fun _ _ => do
  return some (Lean.mkConst ``NeedOther.intro)

attribute [test_rules] solveNeedOther

ruleproc_decl lowNat : Nat := fun _ _ => do
  return some (Lean.mkNatLit 1)

ruleproc_decl highNat : Nat := fun _ _ => do
  return some (Lean.mkNatLit 2)

attribute [test_rules 100] lowNat
attribute [test_rules 200] highNat

ruleproc_decl wrongPatternProc : NeedOther := fun _ _ => do
  return some (Lean.mkConst ``True.intro)

attribute [test_rules] wrongPatternProc

def autoParamSource (h : True := by trivial) : True := h

theorem autoParamRule (h : autoParam True autoParamSource._auto_1) : True := h

ruleproc_decl reflByProc {A : Type} (a : A) : a = a := fun _ _ => do
  return some (← Lean.Meta.mkAppM ``Eq.refl #[a])

attribute [test_rules] reflByProc
