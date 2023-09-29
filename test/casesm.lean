import Mathlib.Tactic.CasesM
import Std.Tactic.GuardExpr

set_option autoImplicit true

example (h : a ∧ b ∨ c ∧ d) (h2 : e ∧ f) : True := by
  casesm* _∨_, _∧_
  · clear ‹a› ‹b› ‹e› ‹f›; (fail_if_success clear ‹c›); trivial
  · clear ‹c› ‹d› ‹e› ‹f›; trivial

example (h : a ∧ b ∨ c ∧ d) : True := by
  fail_if_success casesm* _∧_ -- no match expected
  clear ‹a ∧ b ∨ c ∧ d›; trivial

example (h : a ∧ b ∨ c ∨ d) : True := by
  casesm* _∨_
  · clear ‹a ∧ b›; trivial
  · clear ‹c›; trivial
  · clear ‹d›; trivial

example (h : a ∧ b ∨ c ∨ d) : True := by
  casesm _∨_
  · clear ‹a ∧ b›; trivial
  · clear ‹c ∨ d›; trivial

example (h : a ∧ b ∨ c ∨ d) : True := by
  cases_type And Or
  · clear ‹a ∧ b›; trivial
  · clear ‹c ∨ d›; trivial

example (h : a ∧ b ∨ c ∨ d) : True := by
  fail_if_success cases_type* And -- no match expected
  · clear ‹a ∧ b ∨ c ∨ d›; trivial

example (h : a ∧ b ∨ c ∨ d) : True := by
  cases_type Or
  · clear ‹a ∧ b›; trivial
  · clear ‹c ∨ d›; trivial

example (h : a ∧ b ∨ c ∨ d) : True := by
  cases_type* Or
  · clear ‹a ∧ b›; trivial
  · clear ‹c›; trivial
  · clear ‹d›; trivial

example (h : a ∧ b ∨ c ∨ d) : True := by
  fail_if_success cases_type!* And Or -- no match expected
  · clear ‹a ∧ b ∨ c ∨ d›; trivial

example (h : a ∧ b ∧ (c ∨ d)) : True := by
  cases_type! And Or
  · clear ‹a› ‹b ∧ (c ∨ d)›; trivial

example (h : a ∧ b ∧ (c ∨ d)) : True := by
  cases_type!* And Or
  · clear ‹a› ‹b› ‹c ∨ d›; trivial

inductive Test : Nat → Prop
  | foo : Test 0
  | bar : False → Test (n + 1)

example (_ : Test n) (h2 : Test (m + 1)) : True := by
  cases_type!* Test
  · clear ‹Test n› ‹False›; trivial

example (_ : Test n) (h2 : Test (m + 1)) : True := by
  cases_type Test
  · clear ‹Test (m + 1)›; trivial
  · clear ‹False› ‹Test (m + 1)›; trivial

example (_ : Test n) (h2 : Test (m + 1)) : True := by
  cases_type* Test
  · clear ‹False›; trivial
  · clear ‹False›; clear ‹False›; trivial

example : True ∧ True ∧ True := by
  fail_if_success constructorm* True, _∨_ -- no match expected
  guard_target = True ∧ True ∧ True
  constructorm _∧_
  · guard_target = True; constructorm True
  · guard_target = True ∧ True; constructorm* True, _∧_

section AuxDecl
variable {p q r : Prop}
variable (h : p ∧ q ∨ p ∧ r)

-- Make sure that we don't try to work on auxiliary declarations.
-- In this case, there will be an auxiliary recursive declaration for
-- `foo` itself that `casesm (_ ∧ _)` could potentially match.
theorem foo : p ∧ p := by
  cases h
  · casesm (_ ∧ _)
    constructor <;> assumption
  · casesm (_ ∧ _)
    constructor <;> assumption

end AuxDecl
