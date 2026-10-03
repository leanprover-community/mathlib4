/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Test cases for the ℕ/ℤ DIV/MOD enrichment of the integer frontend
(issues #24 and #45). Each goal contains `a / b` or `a % b` over ℕ
or ℤ; the lift pre-pass introduces witness equalities and bounds
before the SOS reifier runs. The leading block covers positive
literal divisors (issue #24); the trailing block (after the
non-literal-divisor section header) covers divisors whose positivity
is derived from in-scope hypotheses via `omega` (issue #45).
-/
import Mathlib.Tactic.SOS

-- Trivial ℕ div lower bound: `n / 2 + n / 2 ≤ n` follows from
-- `n = 2 * (n / 2) + n % 2` and `0 ≤ n % 2`.
example : ∀ n : ℕ, n / 2 + n / 2 ≤ n := by sos

-- Trivial ℕ mod upper bound: `n % 3 ≤ 2` follows from `n % 3 + 1 ≤ 3`.
example : ∀ n : ℕ, n % 3 ≤ 2 := by sos

-- ℕ div+mod identity: `2 * (n / 2) + n % 2 = n` is the witness itself.
example : ∀ n : ℕ, 2 * (n / 2) + n % 2 = n := by sos

-- ℤ remainder nonneg under ediv (the default `/` on ℤ).
example : ∀ n : ℤ, 0 ≤ n % 3 := by sos

-- ℤ remainder bound: `n % 5 ≤ 4`.
example : ∀ n : ℤ, n % 5 ≤ 4 := by sos

-- ℤ div+mod identity with sign-invariant statement.
example : ∀ n : ℤ, 2 * (n / 2) + n % 2 = n := by sos

-- `n / 2 ≤ n` over ℕ (the witness `n = 2*(n/2) + n%2` and `0 ≤ n%2`
-- give `n/2 ≤ n/2 + (n/2 + n%2) = n`).
example : ∀ n : ℕ, n / 2 ≤ n := by sos

-- Tight: `3 * (n / 3) ≤ n`.
example : ∀ n : ℕ, 3 * (n / 3) ≤ n := by sos

-- ℤ goal with a non-negativity precondition.
example : ∀ n : ℤ, 0 ≤ n → 2 * (n / 2) ≤ n := by sos

-- Larger divisor literal: `n / 7 + n / 7 ≤ n` (the search treats
-- `n/7` as an atom `q`; from `n = 7q + r` and `0 ≤ r` it gets
-- `2q ≤ 2q + 5q + r = n` requiring `5q ≥ 0`, which follows from
-- `0 ≤ q` introduced by `assertNatCastNonneg`).
example : ∀ n : ℕ, n / 7 + n / 7 ≤ n := by sos

-- Both divisor literals as distinct atoms in the conclusion.
example : ∀ n : ℕ, n / 2 + n / 3 ≤ n + n := by sos

-- DIV/MOD in a `0 ≤ …`-shape hypothesis is enriched too (the lift
-- scans hypothesis types in addition to the conclusion). Trivial
-- consequence of `0 ≤ n / 2` plus the witness `n = 2 * (n/2) + n%2`.
example : ∀ n : ℕ, 0 ≤ n / 2 → 0 ≤ n / 2 + n / 2 + n / 2 := by sos

-- Equality conclusion `liftToReal` splits via `le_antisymm` and
-- recurses on each ≤-subgoal; the second entry into `enrichDivMod`
-- must NOT re-enrich the same site by rediscovering its own
-- previously-introduced witness hypotheses.
example : ∀ n : ℕ, n % 2 + 2 * (n / 2) = n := by sos

-- Non-literal divisor with no positivity hypothesis in scope: the
-- unconditional witnesses (`n · (m/n) + m%n = m` and `m%n ≥ 0`) are
-- still introduced, but the strict bound `m%n < n` is skipped because
-- `omega` can't prove `0 < n`. The goal `m / n ≤ m` is false at the
-- real point `n := 0, m := 0, m/n := 1, m%n := 0` (consistent with
-- the unconditional witnesses), so the search correctly fails.
example : True := by
  fail_if_success
    (have : ∀ m n : ℕ, m / n ≤ m := by sos)
  trivial

/-! ### Non-literal divisor enrichment (issue #45)

When the divisor is not a positive literal, `enrichDivMod` introduces
the unconditional div/mod identity and remainder ≥ 0 witnesses, and
routes the strict bound `r < n` through `omega` on the divisor
positivity (over the source domain). Sites whose positivity is
derivable from the local context — a `n ≠ 0` / `0 < n` / `m < n`
hypothesis — get the full witness suite; sites whose positivity isn't
provable get only the unconditional facts. The omega-derived `0 < n`
is local to the `by` block: it's used to discharge `Nat.mod_lt` /
`Int.emod_lt_of_pos`, not added as a separate ℝ-cast hypothesis. -/

-- sos.ml:1729 — `n · (m / n) ≤ m`. Holds unconditionally over ℕ:
-- `n · (m/n) = m - m%n ≤ m`. The unconditional witnesses (div/mod
-- identity and `0 ≤ m%n`) give a direct Putinar cert.
example : ∀ m n : ℕ, n * (m / n) ≤ m := by sos

-- ℤ companion: with `0 < n` in scope, `omega` discharges the
-- divisor-positivity sides of `Int.emod_nonneg` / `Int.emod_lt_of_pos`
-- and the same cert closes the goal.
example : ∀ m n : ℤ, 0 < n → n * (m / n) ≤ m := by sos

-- Focused tests for the optional positivity-guarded witnesses.
-- Each one directly exercises the `omega`-derived bound that
-- `enrichSite` adds for non-literal divisors and would silently
-- regress if the soft-failed witness intros stopped firing.

-- ℕ strict bound from `n ≠ 0`: the witness `0 ≤ n - (m%n) - 1` is
-- precisely what's needed (the rest is `Nat.cast_lt` on the
-- conclusion).
example : ∀ m n : ℕ, n ≠ 0 → m % n < n := by sos

-- ℤ remainder ≥ 0 from `n ≠ 0`: directly the `hnn` witness.
example : ∀ m n : ℤ, n ≠ 0 → 0 ≤ m % n := by sos

-- ℤ strict bound from `0 < n`: directly the `hgap` witness.
example : ∀ m n : ℤ, 0 < n → m % n < n := by sos

/-! ### Shared DIV/MOD quotient and remainder atoms (issue #67) -/

open Lean Meta Elab Tactic in
private partial def containsRawNatDivMod (e : Expr) : MetaM Bool := do
  match_expr e with
  | Nat.div _ _ => return true
  | Nat.mod _ _ => return true
  | _ =>
    match e with
    | .app f a => return (← containsRawNatDivMod f) || (← containsRawNatDivMod a)
    | .lam _ t b _ | .forallE _ t b _ =>
      return (← containsRawNatDivMod t) || (← containsRawNatDivMod b)
    | .mdata _ b => containsRawNatDivMod b
    | _ => return false

set_option linter.unusedTactic false in
example : ∀ a b : ℕ, b ≠ 0 → (a * b) / b ≤ a := by
  intro a b hb
  run_tac do
    let st ← Lean.Elab.Tactic.saveState
    SOS.Lift.refuteToReal
    let some parsed ← SOS.Reify.parseGoalAtomic |
      throwError "issue #67 regression: refuted DIV/MOD goal did not reify"
    unless parsed.atoms.size == 4 do
      throwError "issue #67 regression: expected atoms a/b/q/r, got {parsed.atoms.size}"
    for atom in parsed.atoms do
      if ← containsRawNatDivMod atom then
        throwError "issue #67 regression: raw Nat.div/Nat.mod leaked into atom {atom}"
    st.restore
  have hpos : 0 < b := Nat.pos_of_ne_zero hb
  rw [Nat.mul_div_left _ hpos]

/-! ### Refutation with equality elimination (issue #54) -/

example : ∀ a b : ℕ, b ≠ 0 → (a * b) / b = a := by
  sos (config := { maxDepth := 0, maxSubsetCardinality := 2 })

example : ∀ n : ℕ, n / 2 + (n + 1) / 2 = n := by
  sos (config := { maxDepth := 0, maxSubsetCardinality := 2 })

example : ∀ a b c : ℕ, c ≠ 0 → a / c + b / c ≤ (a + b) / c := by
  sos (config := { maxDepth := 0, maxSubsetCardinality := 2 })
