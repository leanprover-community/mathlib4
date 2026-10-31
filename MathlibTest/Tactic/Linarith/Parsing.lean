module
public meta import Lean.Elab.Tactic
public meta import Mathlib.Tactic.Linarith.Parsing
import Mathlib.Algebra.Order.Ring.Rat

open Lean Meta Elab Tactic Mathlib.Tactic.Linarith

/-- Check equivalent formal polynomials independently of the numbering of their monomials. -/
elab "check_linarith_parser " a:ident b:ident : tactic => withMainContext do
  let pfs := [mkFVar (← getFVarId a), mkFVar (← getFVarId b)]
  let (comps, _) ← linearFormsAndMaxVar .reducible pfs
  unless comps[0]!.coeffs == comps[1]!.coeffs do
    throwError "different linear forms: {comps}"
  for c in comps do
    unless (c.coeffs.zip c.coeffs.tail).all (fun (a, b) ↦ a.1 > b.1) do
      throwError "linear indices are not descending: {c.coeffs}"
  (← getMainGoal).assign (mkConst ``True.intro)
  replaceMainGoal []

set_option linter.unusedVariables false

example (x y : ℤ) (h₁ : (x + y) * (x - y) + y ^ 2 < 0) (h₂ : x ^ 2 < 0) : True := by
  check_linarith_parser h₁ h₂

example (x y : ℚ) (h₁ : (y * 3) * x - 3 * (x * y) = 0) (h₂ : (0 : ℚ) = 0) : True := by
  check_linarith_parser h₁ h₂

-- The parser's formal subtraction is intentional even when the input type is not a ring.
example (x y : ℕ) (h₁ : x - y + y ≤ 0) (h₂ : x ≤ 0) : True := by
  check_linarith_parser h₁ h₂

-- Symbolic exponents and division remain atoms rather than requiring extra algebraic structure.
example (x y : ℚ) (n : ℕ) (h₁ : x ^ n + x / y - x ^ n = 0) (h₂ : x / y = 0) : True := by
  check_linarith_parser h₁ h₂

example (x : ℤ) (h₁ : (x : ℚ) + 3 - (x : ℚ) ≤ 0) (h₂ : (3 : ℚ) ≤ 0) : True := by
  check_linarith_parser h₁ h₂

-- A shared polynomial representation must not introduce the normalizer's default degree limit.
example (x : ℤ) (h₁ : x ^ 100 < 0) (h₂ : x ^ 50 * x ^ 50 < 0) : True := by
  check_linarith_parser h₁ h₂
