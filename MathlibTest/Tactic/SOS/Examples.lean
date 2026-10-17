/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

`by sos` showcase — the primary entry point for evaluating this
package. The tactic discharges polynomial (in)equality goals over
ℝ (and ℤ / ℚ / ℕ, lifted automatically) by finding a Positivstellensatz
certificate: it shells out to CSDP, rounds the floating-point Gram
matrix to ℚ, then verifies the resulting sum-of-squares identity
inside the kernel.

Layout:

* §1–§7 walk through the supported fragment by capability, starting
  with one-line positivity goals and building up through constrained,
  strict, equality-hypothesis, infeasibility, and ℕ/ℤ/ℚ-lifted forms.
* §8 demonstrates the `sos?` → `sos_witness` workflow for inspecting
  and pinning certificates.
* §9 covers graceful failure (Motzkin, infimum-0 strict positivity)
  and the out-of-scope-input error messages.

Additional executable Harrison `Examples/sos.ml` ports live in
`MathlibTest.Tactic.SOS.Harrison`. The Mathlib-free package separately tests the
engine's internal invariants and exact-rational simplex implementation.

Speed contract: this file builds in under 60s wall-clock.
-/
import Mathlib.Tactic.SOS

open SOS CPoly

/-! ## §1. Positivity over ℝ -/

example (x : ℝ) : 0 ≤ x^2 + 1 := by sos
example (x : ℝ) : 0 ≤ x^4 + 1 := by sos

-- Perfect squares, single-variable and multivariate.
example (x : ℝ) : 0 ≤ x^2 + 2*x + 1 := by sos
example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by sos
example (x y : ℝ) : 0 ≤ x^2 + 2*x*y + y^2 := by sos
example (x : ℝ) : 0 ≤ x^4 - 2*x^2 + 1 := by sos

-- Explicit pure-SOS surface: no hypotheses may contribute constraints.
example (x y : ℝ) : 0 ≤ x^2 - 2*x*y + y^2 := by pure_sos

/-- error: pure_sos: constraint hypotheses are not allowed
-/
#guard_msgs in
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^2 := by pure_sos

-- Cyclic Schur, 3 variables.
example (a b c : ℝ) :
    0 ≤ a^2 + b^2 + c^2 - a*b - b*c - a*c := by sos

-- AM ≥ GM squared, 2 variables, degree 4.
example (x y : ℝ) : 0 ≤ (x^2 + y^2)^2 - 4*x^2*y^2 := by sos

/-! ## §2. General inequalities (`a ≤ b` / `a < b` form)

`by sos` reifies arbitrary (in)equality conclusions, not just the
`0 ≤ p` normal form — no manual rewrite required. -/

example (x : ℝ) : x ≤ x^2 + x + 1 := by sos
example (x : ℝ) : x < x^2 + x + 2 := by sos
example (x : ℝ) : -(x^2 + 1) ≤ 0 := by sos

/-! ## §3. Strict positivity

The strict-inequality path discovers a Putinar slack `λ*` via an LP
solve and descends through `ε = 2^-k` from there. Including
`polyDenom target` in the rounding schedule lets residuals with
non-power-of-two denominators land on the natural rational grid. -/

example (x : ℝ) : 0 < x^2 + 1 := by sos
example (x : ℝ) : 0 < x^4 + 1 := by sos
example (x y : ℝ) : 0 < x^2 + y^2 + 1 := by sos

-- Non-power-of-two denominator: the residual ends up at denom 3200
-- after ε = 1/128 against `1/100`, requiring polyDenom-aware rounding.
example (x : ℝ) : 0 < x^2 + 1/100 := by sos

-- Multivariate, non-power-of-two denominator.
example (x y : ℝ) : 0 < x^2 + y^2 + 1/500 := by sos

-- Small strict-positivity slack: `1/2^20`. Historically this was the
-- tightest the search could close because of an old `fourSquaresNat`
-- decomposition cap; now the limiting factor is CSDP's float rounding,
-- not the rationaliser.
example (x : ℝ) : 0 < x^2 + 1/1048576 := by sos

/-! ## §4. Constrained goals (Putinar quadratic module) -/

example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^3 + x := by sos
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^2 - x + 1/4 := by sos

example (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    0 ≤ x^2 + 2*x*y + y^2 := by sos

-- Strict-inequality constraint hypothesis: promoted to `0 ≤` in the
-- elaborator via `le_of_lt`.
example (x : ℝ) (_h : 0 < x) : 0 ≤ x^3 + x := by sos

-- Boundary-tight strict goal (issue #46). `runStrict`'s LP-slack pass
-- correctly fails — `x² → 0` as `x → 0⁺`, so no uniform `ε > 0`
-- admits `x² ≥ ε` for all `x > 0`. Closed via the strict-product
-- Positivstellensatz fallback: `pol = x`, `i = 2` gives
-- `−x² = 1 · (−x²)` against augmented `[x, −x²]`, with `x² > 0`
-- recovered structurally from `0 < x` via `mul_pos`.
example (x : ℝ) (_h : 0 < x) : 0 < x^2 := by sos

-- Nonpos hypothesis (`h : x ≤ 0`), driving the `.neg`-wrapping in
-- `recogniseConstraint` and the `aeval_nonneg_of_orig_neg` bridge in
-- `SOS/Verifier.lean`.
example (x : ℝ) (_h : x ≤ 0) : 0 ≤ -x := by sos

-- General `a ≤ b` / `a < b` hypotheses with non-zero literals: the
-- reifier converts `h : a ≤ b` to `0 ≤ b − a` via `sub_nonneg.mpr`
-- and `h : a < b` to `0 < b − a` via `sub_pos.mpr` (see issue #49).
example (x : ℝ) (_h : x ≤ 1) : 0 ≤ 1 - x := by sos
example (x : ℝ) (_h : 1 ≤ x) : 0 ≤ x - 1 := by sos
example (x : ℝ) (_h : -1 ≤ x) : 0 ≤ x + 1 := by sos
example (r t : ℝ) (_h1 : -1 ≤ t) (_h2 : t ≤ 1) :
    0 ≤ 1 + r^2 - 2*r*t := by sos
example (x y : ℝ) (_hx : 1 ≤ x) (_hy : 1 ≤ y) :
    0 ≤ x*y - (x + y - 1) := by sos
example (x : ℝ) (_h : x < 1) : 0 ≤ 1 - x := by sos
-- Strict variable-vs-variable form: `h : x < y → 0 ≤ y − x`.
example (x y : ℝ) (_h : x < y) : 0 ≤ y - x := by sos

/-! ## §5. Equality hypotheses

The certificate gains a free polynomial cofactor `qⱼ` per equality
`pⱼ = 0`. The verified identity becomes
`target = σ₀ + Σᵢ σᵢ · gᵢ + Σⱼ qⱼ · pⱼ`. The reifier maps `a = b` to
`pⱼ := a − b`; downstream the cofactor search is free to discover any
sign for `qⱼ`. -/

-- From `x*y = 1` conclude `0 ≤ x*y − 1`. Cofactor `q := 1`.
example (x y : ℝ) (_h : x*y = 1) : 0 ≤ x*y - 1 := by sos

-- Degree-1 cofactor: `x = 1 → 0 ≤ x² − 1`. Search must discover
-- `q := x + 1`. Load-bearing: the conclusion is false at `x := 0`
-- without the equality.
example (x : ℝ) (_h : x = 1) : 0 ≤ x^2 - 1 := by sos

-- Strict positivity with equality, exercising `runStrict`'s cofactor
-- path (both the λ-solve and the feasibility re-solve include cofactor
-- blocks). Load-bearing: `0 < x²` is false at `x := 0`.
example (x : ℝ) (_h : x = 1) : 0 < x^2 := by sos

/-! ## §6. Infeasibility (`¬ p ≤ 0` conclusions) -/

example (x : ℝ) : ¬ (x^2 + 1 ≤ 0) := by sos
example (x : ℝ) : ¬ (x^4 + 1 ≤ 0) := by sos

/-! ## §7. Lifting ℕ / ℤ / ℚ goals to ℝ

The lift pre-pass in `SOS/Lift.lean` runs before `parseGoalAtomic`.
It intros leading ℕ / ℤ / ℚ / ℝ universal binders, splits equality
conclusions via `le_antisymm`, rewrites ℕ / ℤ strict inequalities via
`lt_iff_add_one_le`, applies the cast bridge (`Nat.cast_le.mp`, etc.)
on the conclusion, runs `rify at *` to lift hypotheses, and adds a
`0 ≤ (↑a : ℝ)` hypothesis for every ℕ-typed cast atom now in the goal.

The user-visible tactic name does not change — `by sos` auto-dispatches
on the (in)equality type. Goals already over ℝ pay no overhead. -/

-- ℤ: `(a − b)² ≥ 0`.
example (a b : ℤ) : 2*a*b ≤ a^2 + b^2 := by sos

-- ℤ Schur: `(a−b)² + (b−c)² + (a−c)² ≥ 0` divided by two.
example (a b c : ℤ) : a*b + b*c + a*c ≤ a^2 + b^2 + c^2 := by sos

-- ℚ strict: routed through `Rat.cast_lt.mp` to the ℝ strict-positivity path.
example (x : ℚ) : 0 < x^2 + 1 := by sos

-- ℚ: `(x² − y²)² ≥ 0`.
example (x y : ℚ) : 4*x^2*y^2 ≤ (x^2 + y^2)^2 := by sos

-- Mixed ℕ + ℝ — ℕ binder lifted, ℝ atom preserved.
example : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x^2 + n := by sos

-- ℕ-cast atom appears only in a hypothesis (conclusion is over ℝ with
-- no ℕ casts). The lift pre-pass must scan local hypothesis types too,
-- otherwise the `0 ≤ ↑n` fact never reaches the SOS reifier.
example (n : ℕ) (x : ℝ) (_h : (n : ℝ) = x) : 0 ≤ x := by sos

-- Strict ℕ via `Nat.lt_iff_add_one_le`. `n < n+1` rewrites to
-- `n+1 ≤ n+1`, which the rewrite step closes reflexively before the
-- cast bridge is needed.
example : ∀ n : ℕ, n < n + 1 := by sos

-- ℕ equality via `le_antisymm` split (Harrison `sos.ml:1725`). After
-- the antisymmetric split both subgoals reduce to `0 ≤ 0`.
example : ∀ m n : ℕ, 2*m + n = (n + m) + m := by sos

/-! ## §8. `sos?` — inspect, then pin the witness

`sos?` runs the search and prints a `Try this:` suggestion of an
explicit `sos_witness`. The witness is then statically checked at
elaboration time, with no CSDP call — useful for committing a
certificate that you don't want re-derived on every build. -/

/-- info: Try this:
  [apply] sos_witness { sigmas := [([], { terms := [((1 : ℚ), CMvPolynomial.C (1 : ℚ)), ((1 : ℚ), CMvPolynomial.X 0)] })] }
-/
#guard_msgs in
example (x : ℝ) : 0 ≤ x^2 + 1 := by sos?

-- And the suggested replacement compiles:
example (x : ℝ) : 0 ≤ x^2 + 1 := by
  sos_witness { sigmas := [([], { terms := [((1 : ℚ), CMvPolynomial.C (1 : ℚ)), ((1 : ℚ), CMvPolynomial.X 0)] })] }

-- For strict positivity, the `Try this:` suggestion includes `with ε := …`.
/-- info: Try this:
  [apply] sos_witness { sigmas := [([], { terms := [((1 : ℚ), CMvPolynomial.X 0)] })] } with ε := (1 : ℚ)
-/
#guard_msgs in
example (x : ℝ) : 0 < x^2 + 1 := by sos?

example (x : ℝ) : 0 < x^2 + 1 := by
  sos_witness { sigmas := [([], { terms := [((1 : ℚ), CMvPolynomial.X 0)] })] } with ε := (1 : ℚ)

-- For boundary-tight strict goals (issue #46), `sos?` emits the
-- replayable `sos_witness <cert> with exponent := <n>` form. The
-- inline cert verifies `−pol^n` against the augmented inequality
-- list `gs ++ [−p]`. The exact CSDP-found cert isn't a stable
-- string (Gram entries depend on the SDP solver path), so we only
-- check that the hand-rolled minimal witness replays. The minimal
-- cert here is `σ_{[1]} = 1`, contributing `1 · (−x²) = −x²` against
-- `gs ++ [-p] = [x, -x²]`.
example (x : ℝ) (_h : 0 < x) : 0 < x^2 := by
  sos_witness
    { sigmas := [([1], { terms := [((1 : ℚ), CMvPolynomial.C (1 : ℚ))] })] }
    with exponent := 2

-- For equality goals the suggestion includes `eqCofs := …`.
/-- info: Try this:
  [apply] sos_witness { sigmas := [([], { terms := [] })], eqCofs := [CMvPolynomial.C (1 : ℚ)] }
-/
#guard_msgs in
example (x y : ℝ) (_h : x*y = 1) : 0 ≤ x*y - 1 := by sos?

-- Equality-elimination reconstruction with a two-step substitution chain.
example (x y : ℝ) (_hxy : x - y = 0) (_hy : y - 1 = 0) : 0 ≤ x - 1 := by
  sos

/-! ### `sos_witness` direct use

The witness elaborator also accepts certificates for constrained and
infeasibility goals. Sigma entries are subset-indexed; their indices
are bounds-checked against `gs.length` by `cert.checks`, but the
list itself is sparse (no entry needed for a constraint the witness
doesn't use). The `eqCofs` list, in contrast, is length-aligned with
the equality constraints. -/

-- Constrained — trivial witness, exercising the constraint structural check.
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^2 := by
  sos_witness
    { sigmas := [([], { terms := [((1 : ℚ), CMvPolynomial.X 0)] })] }

-- Infeasibility — `-1 = x² + 1·(-x² - 1)` proves the constraint set
-- `{x² + 1 ≤ 0}` is infeasible.
example (x : ℝ) : ¬ (x^2 + 1 ≤ 0) := by
  sos_witness
    { sigmas := [([], { terms := [((1 : ℚ), CMvPolynomial.X 0)] }),
                 ([0], { terms := [((1 : ℚ), CMvPolynomial.C (1 : ℚ))] })] }

-- Combined inequality + equality: from `0 ≤ x − 1` and `x = 0` derive
-- `False`. Certificate: `−1 = 0 + 1·(x − 1) + (−1)·x`.
example (x : ℝ) (_hx : 0 ≤ x - 1) (_hxz : x = 0) : False := by
  sos_witness
    { sigmas := [([0], { terms := [((1 : ℚ), CMvPolynomial.C (1 : ℚ))] })],
      eqCofs := [-CMvPolynomial.C (1 : ℚ)] }

-- Negative-coefficient guard. The polynomial identity `−x² = (−1) · x²`
-- holds exactly, but `coeffsNonneg` rejects the negative weight, so
-- `Certificate.checks` returns `false` and `sos_witness` does NOT
-- close this (false) goal. Without the `coeffsNonneg` check the
-- witness elaborator would happily prove `0 ≤ −x²`.
example : True := by
  fail_if_success
    (have : ∀ x : ℝ, 0 ≤ -x^2 := by
      intro x
      sos_witness
        { sigmas := [([], { terms := [((-1 : ℚ), CMvPolynomial.X 0)] })] })
  trivial

/-! ## §9. Graceful failure & out-of-scope guards -/

-- Motzkin is nonneg but not SOS, so the *default* search (no power
-- refutation) has no certificate to find and must fail gracefully.
example : True := by
  fail_if_success
    (have : ∀ x y : ℝ, 0 ≤ x^4*y^2 + x^2*y^4 + 1 - 3*x^2*y^2 := by sos)
  trivial

-- Infimum-0 strict positivity must also fail gracefully. `p = (x*y −
-- 1)² + x²` is strictly positive everywhere on ℝ² but its infimum is
-- 0 along `x → 0, y = 1/x`. No positive ε admits a Putinar certificate.
example : True := by
  fail_if_success
    (have : ∀ x y : ℝ, 0 < (x*y - 1)^2 + x^2 := by sos)
  trivial

-- Controls for the equality-hypothesis examples in §5: same conclusion
-- without the equality must fail, confirming the equality path was
-- genuinely exercised above.
example : True := by
  fail_if_success
    (have : ∀ x : ℝ, 0 ≤ x^2 - 1 := by sos)
  trivial

example : True := by
  fail_if_success
    (have : ∀ x : ℝ, 0 < x^2 := by sos)
  trivial

-- Truncated ℕ subtraction is refused with a hint.
/-- error: sos: `by sos` does not handle truncated ℕ subtraction in goals; cast to `Int.sub`, or rewrite via `Nat.sub_eq` with `m ≤ n` in context.
-/
#guard_msgs in
example : ∀ n : ℕ, n - 1 ≤ n := by sos

-- ℕ / ℤ DIV/MOD is supported via the enrichment witnesses introduced
-- by the lift pre-pass: literal divisors enrich unconditionally
-- (issue #24); non-literal divisors enrich when an in-scope positivity
-- hypothesis (`b ≠ 0`, `0 < b`, `m < b`, …) is discharged by `omega`
-- (issue #45). Here `b ≠ 0` lets the strict-bound witness fire, and
-- `(a/b)·b ≤ a` follows directly from the div/mod identity.
example : ∀ a b : ℕ, b ≠ 0 → a / b * b ≤ a := by sos

/-! ## §10. Boolean combinations in conclusions

`by sos` splits a conjunctive conclusion `p ∧ q` via `And.intro` and
runs the rest of the pipeline on each subgoal; for a disjunctive
conclusion `p ∨ q` it tries `Or.inl` first and falls back to `Or.inr`
on failure. Nesting is capped at depth 3.

Disjunctive *hypotheses* are out of scope. -/

-- Simple conjunction.
example (x : ℝ) : 0 ≤ x^2 ∧ 0 ≤ x^4 := by sos

-- Conjunction under a leading ∀.
example : ∀ x : ℝ, 0 ≤ x^2 ∧ 0 ≤ x^4 := by sos

-- Disjunction where the left disjunct succeeds.
example : ∀ x : ℝ, 0 ≤ x^2 ∨ 0 ≤ -(x^2 + 1) := by sos

-- Disjunction where the left disjunct fails (false at `x = 0`), forcing
-- the `Or.inr` retry to find the certificate.
example : ∀ x : ℝ, 0 ≤ -(x^2 + 1) ∨ 0 ≤ x^2 := by sos

-- Nested: `(p ∧ q) ∧ r` — depth 2.
example (x y : ℝ) : (0 ≤ x^2 ∧ 0 ≤ y^2) ∧ 0 ≤ x^2 + y^2 := by sos

-- Mixed nesting: conjunction inside disjunction.
example (x y : ℝ) : (0 ≤ -(x^2 + 1)) ∨ (0 ≤ x^2 ∧ 0 ≤ y^2) := by sos

-- Constrained conjunction: each conjunct uses the shared hypothesis.
example (x : ℝ) (_h : 0 ≤ x) : 0 ≤ x^3 + x ∧ 0 ≤ x^2 - x + 1/4 := by sos

-- ℤ conjunction — the lift pre-pass runs on each conjunct independently.
example (a b : ℤ) : 2*a*b ≤ a^2 + b^2 ∧ 0 ≤ a^2 + b^2 := by sos

-- A graceful failure: neither disjunct is true (both polynomials are
-- strictly negative), so both `Or.inl` and `Or.inr` arms fail.
example : True := by
  fail_if_success
    (have : ∀ x : ℝ, (0 ≤ -(x^2 + 1)) ∨ (0 ≤ -(x^4 + 1)) := by sos)
  trivial

-- Depth cap: exactly three nested splits is fine.
example (x : ℝ) : ((0 ≤ x^2 ∧ 0 ≤ x^2) ∧ 0 ≤ x^2) ∧ 0 ≤ x^2 := by sos

-- Depth cap: a left-nested chain of four `And`s exceeds the limit.
-- The check is a global preflight scan, so a too-deep subtree is
-- rejected even if some other branch would have closed easily.
/-- error: sos: boolean nesting in conclusion exceeds depth 3 (found 4); flatten the goal or split manually
-/
#guard_msgs in
example (x : ℝ) :
    (((0 ≤ x^2 ∧ 0 ≤ x^2) ∧ 0 ≤ x^2) ∧ 0 ≤ x^2) ∧ 0 ≤ x^2 := by sos
