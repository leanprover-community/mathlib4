module

public import MathlibTest.ApplyRuleSetsAttr

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

example (p q : Prop) : p → q → p ∧ q := by
  fail_if_success apply_rulesets [test_rules, -Add.intro]
  apply_rulesets [test_rules]

example : True := by
  apply_rulesets [sortTrue]

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
  apply_rulesets (disch := trivial) [id]

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

structure HasDeriv (f : α → β) (f' : α × α → β × β) : Prop where


namespace HasDeriv

theorem congr_deriv {f : α → β} {f' f''} (hf : HasDeriv f f') (hf : f' = f'')  :
    HasDeriv f f'' := ⟨⟩

@[has_deriv]
theorem id : HasDeriv (fun x : α => x) (fun xdx => xdx) := ⟨⟩

local instance [Add α] [Add β] : Add (α × β) := ⟨fun (x,y) (x',y') => (x+x', y+y')⟩

@[has_deriv]
theorem add [Add β] (f g : α → β) (hf : HasDeriv f f') (hg : HasDeriv g g') :
    HasDeriv (fun x : α => f x + g x) (fun xdx => f' xdx + g' xdx) := ⟨⟩

@[has_deriv high]
theorem div_bad [Div β] (f g : α → β) (hf : HasDeriv f f') (hg : HasDeriv g g')
    (bad : False) :
    HasDeriv (fun x : α => f x / g x) (fun xdx => f' xdx) := ⟨⟩

@[has_deriv]
theorem div_good [Add β] [Sub β] [Mul β] [Div β] [One β] (f g : α → β)
    (hf : HasDeriv f f') (hg : HasDeriv g g') :
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

end HasDeriv
