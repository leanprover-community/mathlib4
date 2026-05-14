module

public import MathlibTest.ApplyRuleSetsAttr

open Mathlib.Tactic.ApplyRuleSets

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
  apply_rulesets (disch := trivial) [id]

-- Explicit theorem/term rules are tried directly.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply_rulesets [fun hp hq => And.intro hp hq, hp, hq]

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
  apply_rulesets (disch := trivial) [id]

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
