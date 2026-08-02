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

-- Two distinct sites (different divisor literals) on the same `n`:
-- both `n / 2` and `n / 3` need witnesses, with non-shadowing names.
example : ∀ n : ℕ, 2 * (n / 2) ≤ n ∧ 3 * (n / 3) ≤ n → True := by
  intro _ _; trivial

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
`Int.emod_lt_of_pos`, not added as a separate ℝ-cast hypothesis.

Harrison's `sos.ml:1729` lands directly on the unconditional ℕ path
(no positivity hypothesis needed). The remaining `:1726`, `:1727`,
`:1730`, `:1731` examples enrich correctly but their natural
certificates require products of inequality constraints (e.g.
`n · (m/n) ≥ 0` derived from `n ≥ 0 ∧ m/n ≥ 0`), which is a
Schmüdgen-preordering certificate rather than a Putinar one — out of
scope until #38 lands. See the FIXME blocks below for the per-case
diagnoses. -/

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

-- FIXME sos.ml:1726 — `n ≠ 0 ⇒ 0 % n = 0`. With the strict bound
-- `n - (0%n) - 1 ≥ 0` in scope the cert needs `n · (0/n) ≥ 0`, a
-- product of two non-negative atoms, which Putinar can't form
-- without Schmüdgen preordering (#38).
-- example : ∀ n : ℕ, n ≠ 0 → 0 % n = 0 := by sos

-- FIXME sos.ml:1730 — `n ≠ 0 ⇒ 0 / n = 0`. Same preordering
-- obstruction as 1726.
-- example : ∀ n : ℕ, n ≠ 0 → 0 / n = 0 := by sos

-- FIXME sos.ml:1727 — `m < n ⇒ m / n = 0`. Refute path turns it
-- into `m/n ≥ 1 ∧ m + 1 ≤ n ⇒ False`, which needs the multiplicative
-- step `n · (m/n) ≥ n` (i.e. constraint product `n · (m/n - 1) ≥ 0`).
-- example : ∀ m n : ℕ, m < n → m / n = 0 := by sos

-- FIXME sos.ml:1731 — `p ≠ 0 ∧ m ≤ n ⇒ m / p ≤ n / p`. Two DIV
-- sites with the same non-literal divisor `p`; both get the full
-- witness suite from `omega`. The natural refutation chains
-- `p · (m/p - n/p - 1) ≥ p` against `m - n ≤ 0`, again a Schmüdgen
-- product.
-- example : ∀ m n p : ℕ, p ≠ 0 → m ≤ n → m / p ≤ n / p := by sos

/-! ### Refute + equality cofactor — CSDP numerical degeneracy (issue #54)

The three goals below all admit short Schmüdgen-style refutation
certificates with constant cofactors (computed by hand for each):

  * `(a*b)/b = a` (`b ≠ 0`): split by `le_antisymm` into two ≤-goals,
    each closes by refute against the witness `a·b = b·q + r` plus a
    single Schmüdgen product `b·(q − a − 1) ≥ 0` (one direction) or
    `b·(a − q − 1) ≥ 0` (the other). Cardinality 2.
  * `n/2 + (n+1)/2 = n`: pure Putinar from `2·(q₁+q₂ - n - 1) + r₁
    + r₂ - p_1 - p_2 = -1`.
  * `a/c + b/c ≤ (a+b)/c` (`c ≠ 0`): refute closes via Schmüdgen
    `c·(q_a + q_b - q_{ab} - 1) ≥ 0` against `a + b = c·q_{ab} +
    r_{ab}`, sum of the per-summand equalities.

All three certificates verify exactly under `Certificate.checks`
(`decide +kernel` on the polynomial identity). The blocker is at the
CSDP solve step, not at the certificate verifier or the cert search
space: when the goal goes through the refute / infeasibility arm
(target = −1, useTraceCost = false), the LP-encoded equality cofactor
block (`λ = x⁺ − x⁻` with `x⁺, x⁻ ≥ 0` and zero cost) leaves CSDP's
central path on the boundary of primal feasibility. CSDP returns
non-success codes (1/5/7) at the natural relaxation depth and only
much later — at extraDeg ≥ 1, cardinality ≥ 6 — produces a
numerically feasible solution, by which point the SDP has dozens of
extra σ blocks whose Gram matrices don't round to the natural cert.

The closed-positivity path uses `useTraceCost = true`, which gives
CSDP a well-defined central path; the LP cofactor block then behaves
fine. So the existing `n = 2·(n/2) + n%2` showcase test (which is
also an equality goal but doesn't need refute on either ≤-half)
closes cleanly, and the obstruction is specific to refute-arm goals
whose certificate genuinely needs the integer-discreteness step.

Harrison's HOL Light `sos.ml` avoids this problem by eliminating
ideal cofactor variables before the SDP solve:

  * `SOS_RULE` rewrites `NUM` goals to `INT` (`NUM_TO_INT_CONV`), then
    `INT_SOS` refutes the negation and calls `REAL_SOS`.
  * `REAL_SOS` runs `GEN_REAL_ARITH REAL_NONLINEAR_SUBST_PROVER`,
    which repeatedly substitutes any equation with a substitutable
    real variable into the rest of the system before the SDP solve
    (`Examples/sos.ml:1229-1252`).
  * The underlying Positivstellensatz at `Examples/sos.ml:1054` also
    runs `eliminate_all_equations` on the coefficient equations
    *symbolically* before building the CSDP problem; `mk_matrix`
    skips negative-tag blocks (the ideal cofactors) at
    `Examples/sos.ml:1058-1062`, and the CSDP objective is only ever
    populated on the surviving positive SDP block diagonals
    (`Examples/sos.ml:1063-1069`).

So Harrison's effective encoding is `a = b·q + r, 0 ≤ r, r ≤ b − 1`,
but the equality is used to substitute one variable away (typically
`r := a − b·q` for div/mod sites), leaving a pure quadratic-module
problem with no LP cofactor null direction. For our case B, after the
substitution `r := a·b − b·q`, the Schmüdgen-2 cert
`-1 = 2·(a·b − b·q) + (b − (a·b − b·q) − 1) + b·(q − a − 1)` lands
directly without ever instantiating an LP block.

The fix is to add an equality-elimination pre-pass to the search:
identify equalities of the form `var = poly_without_var` in `ps`,
substitute `var` out of every other constraint and the target, drop
the equality from `ps`. This mirrors `REAL_NONLINEAR_SUBST_PROVER`.
Surgical at the search level: drops `ps`-driven LP blocks, leaves the
certificate-verifier API unchanged because the eliminated variable
becomes part of the polynomial expression in the cert. A smaller
short-term mitigation (`-ε` cost on the LP split block) bounds the
null direction numerically; testing showed CSDP still returns return
codes 1/5 on these specific problems, so a numerical regulariser is
not by itself sufficient — the symbolic elimination is the right
solution.

-/

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

example : ∀ a b : ℕ, b ≠ 0 → (a * b) / b = a := by
  sos (config := { maxDepth := 0, maxSubsetCardinality := 2 })

example : ∀ n : ℕ, n / 2 + (n + 1) / 2 = n := by
  sos (config := { maxDepth := 0, maxSubsetCardinality := 2 })

example : ∀ a b c : ℕ, c ≠ 0 → a / c + b / c ≤ (a + b) / c := by
  sos (config := { maxDepth := 0, maxSubsetCardinality := 2 })
