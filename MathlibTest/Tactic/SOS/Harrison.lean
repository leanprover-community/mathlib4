/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Test cases ported from John Harrison's TPHOLs 2007 HOL Light
implementation (`Examples/sos.ml` in jrh13/hol-light, lines
1611–1894). The fragment we cover here is closed `0 ≤ p` / `0 < p` /
`¬ p ≤ 0` conclusions with Putinar-style `0 ≤ g`, `g ≤ 0`, `0 < g`,
and `g = 0` hypotheses. Harrison's examples that need preorderings,
disjunctive conclusions, `abs`, division, integer/natural arithmetic,
or Boolean combinations are out of the supported fragment and not
ported here.

Cases that close are listed inline. Cases marked `FIXME` were verified
by hand-running each through `by sos` in isolation (including with
`maxDepth ∈ {0, 1, 2}`); they're within the supported fragment but
don't yet produce a certificate post-Newton-polytope pruning (#23).
Diagnoses are kept beside each FIXME — the residual failures are
about rounding, preordering / Schmüdgen-style encodings, or the
cofactor-LP recession on equality-hypothesis goals.
-/
import Mathlib.Tactic.SOS

open SOS CPoly

/-! ### Direct SOS, no hypotheses (Harrison's `SOS_CONV` / `PURE_SOS`) -/

-- sos.ml:1789 — 2-variable degree-4
example (x y : ℝ) :
    0 ≤ 2*x^4 + 2*x^3*y - x^2*y^2 + 5*y^4 := by sos

-- sos.ml:1792 — 3-variable degree-4
example (x y z : ℝ) :
    0 ≤ x^4 - (2*y*z + 1)*x^2 + (y^2*z^2 + 2*y*z + 2) := by sos

-- sos.ml:1796 — 2-variable degree-4
example (x y : ℝ) :
    0 ≤ 4*x^4 + 4*x^3*y - 7*x^2*y^2 - 2*x*y^3 + 10*y^4 := by sos

-- sos.ml:1800 — 2-variable degree-10 sparse. Half-Newton-polytope
-- pruning (#23) closes the SDP that the dense `monomialsUpTo 2 5`
-- basis (21 monomials) cannot.
example (x y : ℝ) :
    0 ≤ 4*x^4*y^6 + x^2 - x*y^2 + y^2 := by sos

-- sos.ml:1802 — 2-variable degree-6, Motzkin-like form. Needs depth-2
-- iterative deepening; closes post-Newton with the explicit opt-in.
example (x z : ℝ) :
    0 ≤ 4096 * (x^4 + x^2 + z^6 - 3*x^2*z^2) + 729 := by
  sos (config := { maxDepth := 2 })

-- FIXME sos.ml:1805 — 2-variable degree-6 with linear `30*x*y` and
-- constants. Dense attempt misses on rounding. Newton pruning (#23)
-- doesn't fire — sparsity gate (`4·|support| ≥ C(n+D, D)`) skips
-- the target: 7 support monomials against a 10-monomial dense σ₀
-- basis. Confirmed failing through `maxDepth := 2`.
-- example (x y : ℝ) :
--     0 ≤ 120*x^2 - 63*x^4 + 10*x^6 + 30*x*y - 120*y^2 + 120*y^4 + 31 := by sos

-- sos.ml:1809 — 3-variable degree-6
example (x y z : ℝ) :
    0 ≤ 9*x^2*y^4 + 9*x^2*z^4 + 36*x^2*y^3 + 36*x^2*y^2
        - 48*x*y*z^2 + 4*y^4 + 4*z^4 - 16*y^3 + 16*y^2 := by sos

-- sos.ml:1814 — Motzkin × `(x²+y²+z²)` is SOS (Hilbert-17 style witness)
example (x y z : ℝ) :
    0 ≤ (x^2 + y^2 + z^2) *
        (x^4*y^2 + x^2*y^4 + z^6 - 3*x^2*y^2*z^2) := by sos

-- sos.ml:1819 — 3-variable degree-4 with linear+constant tail.
example (x y z : ℝ) :
    0 ≤ x^4 + y^4 + z^4 - 4*x*y*z + x + y + z + 3 := by sos

-- FIXME sos.ml:1829 — 100·sum-of-squares − 588. The unsubtracted form
-- is trivially SOS; subtracting 588 forces the search to find a
-- non-trivial decomposition that survives rounding. Confirmed failing
-- through `maxDepth := 2`.
-- example (x : ℝ) :
--     0 ≤ 100*((2*x - 2)^2 + (x^3 - 8*x - 2)^2) - 588 := by sos

-- FIXME sos.ml:1832 — Rearranged form of 1805, fails for the same
-- reason: not sparse enough for Newton pruning to fire, dense rounding
-- misses. Confirmed failing through `maxDepth := 2`.
-- example (x y : ℝ) :
--     0 ≤ x^2*(120 - 63*x^2 + 10*x^4) + 30*x*y
--         + 30*y^2*(4*y^2 - 4) + 31 := by sos

/-! ### Hard univariate `PURE_SOS` examples -/

-- sos.ml:1844 — degree-12 univariate
example (x : ℝ) :
    0 ≤ 98*x^12 - 980*x^10 + 3038*x^8 - 2968*x^6
        + 1022*x^4 - 84*x^2 + 2 := by sos

-- sos.ml:1853 — degree-14 univariate
example (x : ℝ) :
    0 ≤ 2*x^14 - 84*x^12 + 1022*x^10 - 2968*x^8
        + 3038*x^6 - 980*x^4 + 98*x^2 := by sos

-- sos.ml:1840 — strict `≥ 1/7` bound on the 1819 polynomial.
example (x y z : ℝ) :
    0 ≤ x^4 + y^4 + z^4 - 4*x*y*z + x + y + z + 3 - 1/7 := by sos

/-! ### Zeng et al. (JSC 37, 2004) — Harrison's PURE_SOS battery -/

-- sos.ml:1867 — 3-var degree-6 Schur-style
example (x y z : ℝ) :
    0 ≤ x^6 + y^6 + z^6 - 3*x^2*y^2*z^2 := by sos

-- sos.ml:1870
example (x y z : ℝ) :
    0 ≤ x^4 + y^4 + z^4 + 1 - 4*x*y*z := by sos

-- sos.ml:1872
example (x y z : ℝ) :
    0 ≤ x^4 + 2*x^2*z + x^2 - 2*x*y*z + 2*y^2*z^2
        + 2*y*z^2 + 2*z^2 - 2*x + 2*y*z + 1 := by sos

-- sos.ml:1879 — Harrison's flagged hard Zeng case. Harrison notes
-- "REAL_SOS does finally converge on the second run at level 12";
-- after Newton-polytope pruning (#23) we close it at the default
-- relaxation level — no `config` opt-in needed.
example (x y z : ℝ) :
    0 ≤ x^4*y^4 - 2*x^5*y^3*z^2 + x^6*y^2*z^4
        + 2*x^2*y^3*z - 4*x^3*y^2*z^3 + 2*x^4*y*z^5
        + z^2*y^2 - 2*z^4*y*x + z^6*x^2 := by sos

-- sos.ml:1886 — 4-variable degree-4, with `Z₂×Z₂` symmetry.
example (x y z w : ℝ) :
    0 ≤ x^4 + 4*x^2*y^2 + 2*x*y*z^2 + 2*x*y*w^2 + y^4 + z^4 + w^4
        + 2*z^2*w^2 + 2*x^2*w + 2*y^2*w + 2*x*y + 3*w^2 + 2*z^2 + 1 := by sos

-- sos.ml:1891 — 4-variable degree-6
example (x y z w : ℝ) :
    0 ≤ w^6 + 2*z^2*w^3 + x^4 + y^4 + z^4 + 2*x^2*w + 2*x^2*z
        + 3*x^2 + w^2 + 2*z*w + z^2 + 2*z + 2*w + 1 := by sos

/-! ### `REAL_SOS` with Putinar-style hypotheses -/

-- sos.ml:1623 shape (issue #50) — linear strict-strict goal. The exact
-- affine strict path closes this before the SDP search.
example (x a : ℝ) (_h1 : 3*x + 7*a < 4) (_h2 : 3 < 2*x) :
    a < 0 := by sos

-- sos.ml:1718 — `0 ≤ x ∧ 0 ≤ y ⇒ x*y*(x+y)² ≤ (x²+y²)²`
example (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    0 ≤ (x^2 + y^2)^2 - x*y*(x + y)^2 := by sos

-- sos.ml:1654 — `x ≥ 1 ∧ y ≥ 1 ⇒ x*y ≥ x + y - 1`. The natural
-- certificate is `(x-1)(y-1) = 1·g₁·g₂`, i.e. a *product* of the two
-- inequality multipliers — a preordering term, not a quadratic-module
-- term `σ₀ + Σ σᵢ·gᵢ`. Closed via Schmüdgen-style enumeration of
-- constraint products (issue #38); the search tries Putinar first
-- (which fails here) and falls back to the preordering monoid.
example (x y : ℝ) (_hx : 0 ≤ x - 1) (_hy : 0 ≤ y - 1) :
    0 ≤ x*y - (x + y - 1) := by sos

-- sos.ml:1657 — strict version of the above. Boundary-tight at
-- `x = y = 1`, so `runStrict`'s LP-slack pass finds no uniform ε.
-- Closes via the strict-product Positivstellensatz fallback (issue
-- #46), which finds the certificate `(x−1)(y−1) > 0` structurally
-- from the strict hypotheses and an SOS identity over the augmented
-- constraint list `[x−1, y−1, −(xy − (x+y−1))]`.
example (x y : ℝ) (_hx : 0 < x - 1) (_hy : 0 < y - 1) :
    0 < x*y - (x + y - 1) := by sos

-- sos.ml:1643 — `0 ≤ x,y,z ∧ x+y+z ≤ 3 ⇒ xy+xz+yz ≥ 3xyz`. Closes
-- via the Schmüdgen-style preordering enumeration (issue #38).
example (x y z : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) (_hz : 0 ≤ z)
    (_hs : x + y + z - 3 ≤ 0) :
    0 ≤ x*y + x*z + y*z - 3*x*y*z := by sos

-- FIXME sos.ml:1682 — interval `[2,4]³` Schur. The preordering
-- enumeration from issue #38 is in place: 6 linear constraints produce
-- 6 singleton + 15 pair σ-blocks (triples and above are degree-filtered).
-- The SDP solves but rounding doesn't validate at any depth ≤ 1 with
-- the default denominator schedule. Probably needs targeted denominator
-- tuning or a smaller `maxSubsetCardinality` to recover. Left as FIXME.
-- example (x y z : ℝ)
--     (_hx1 : 0 ≤ x - 2) (_hx2 : 0 ≤ 4 - x)
--     (_hy1 : 0 ≤ y - 2) (_hy2 : 0 ≤ 4 - y)
--     (_hz1 : 0 ≤ z - 2) (_hz2 : 0 ≤ 4 - z) :
--     0 ≤ 2*(x*z + x*y + y*z) - (x^2 + y^2 + z^2) := by sos

-- FIXME sos.ml:1672 — dodecahedral, intervals to `125841/50000`. Same
-- shape as 1682; same residual rounding issue under issue #38's
-- preordering enumeration.
-- example (x y z : ℝ)
--     (_hx1 : 0 ≤ x - 2) (_hx2 : 0 ≤ 125841/50000 - x)
--     (_hy1 : 0 ≤ y - 2) (_hy2 : 0 ≤ 125841/50000 - y)
--     (_hz1 : 0 ≤ z - 2) (_hz2 : 0 ≤ 125841/50000 - z) :
--     0 ≤ 2*(x*z + x*y + y*z) - (x^2 + y^2 + z^2) := by sos

-- FIXME sos.ml:1690 — sharp `≥ 12` bound on the same interval.
-- Harrison reports needing depth 12 with his Schmüdgen encoding;
-- our preordering machinery from issue #38 is in place but the depth
-- cap plus per-attempt cost makes the full sweep impractical at default
-- settings.
-- example (x y z : ℝ)
--     (_hx1 : 0 ≤ x - 2) (_hx2 : 0 ≤ 4 - x)
--     (_hy1 : 0 ≤ y - 2) (_hy2 : 0 ≤ 4 - y)
--     (_hz1 : 0 ≤ z - 2) (_hz2 : 0 ≤ 4 - z) :
--     0 ≤ 2*(x*z + x*y + y*z) - (x^2 + y^2 + z^2) - 12 := by sos

/-! ### Equality-hypothesis ports

The default `maxDepth := 1` is enough to close both the spherical
constraint forms (1647, 1650) and the discriminant identity (1629).
For Harrison's `xy = 1` form (1714) the natural certificate has a
degree-1 cofactor; that case closes too. -/

-- sos.ml:1647 — `x²+y²+z² = 1 → 0 ≤ 3 − (x+y+z)²`. Cofactor `q := −3`
-- (degree 0, within the search's basis bound) and SOS residual
-- `(x−y)² + (y−z)² + (z−x)²`.
example (x y z : ℝ) (_h : x^2 + y^2 + z^2 = 1) :
    0 ≤ 3 - (x + y + z)^2 := by sos

-- Control: same conclusion without the equality fails (false at
-- `x := y := z := 2`).
example : True := by
  fail_if_success
    (have : ∀ x y z : ℝ, 0 ≤ 3 - (x + y + z)^2 := by sos)
  trivial

-- sos.ml:1650 — `w²+x²+y²+z² = 1 → (w+x+y+z)² ≤ 4`. Four-variable
-- analogue of 1647. Search finds σ₀ = Σ_{i<j} (vᵢ - vⱼ)² and q = -4.
example (w x y z : ℝ) (_h : w^2 + x^2 + y^2 + z^2 = 1) :
    0 ≤ 4 - (w + x + y + z)^2 := by sos

-- Control: false at `w = x = y = z := 10`.
example : True := by
  fail_if_success
    (have : ∀ w x y z : ℝ, 0 ≤ 4 - (w + x + y + z)^2 := by sos)
  trivial

-- sos.ml:1629 — discriminant: `a·x²+b·x+c = 0 → 0 ≤ b² − 4ac`.
-- Identity: `b² − 4ac = (2ax + b)² + (−4a)·(ax² + bx + c)`. The
-- cofactor `−4a` has degree 1, so the default `maxDepth := 1` is
-- enough — pre-Newton this took ~2.5 min, now closes in ~10s.
example (a b c x : ℝ) (_h : a*x^2 + b*x + c = 0) :
    0 ≤ b^2 - 4*a*c := by sos

-- Control: false at `a = c := 1, b := 0`.
example : True := by
  fail_if_success
    (have : ∀ a b c : ℝ, 0 ≤ b^2 - 4*a*c := by sos)
  trivial

-- sos.ml:1714 — `x*y = 1 → 0 ≤ x² + y² − x*y*(x+y)`. Working modulo
-- `xy − 1` leaves the residual `x² + y² − x − y`, which is only
-- nonneg on the variety `V(xy = 1)` and needs degree-≥-2 SOS work to
-- certify globally; the default `maxDepth := 1` finds that certificate.
example (x y : ℝ) (_h : x*y = 1) :
    0 ≤ x^2 + y^2 - x*y*(x + y) := by sos

-- sos.ml:1710 — `0 ≤ x ∧ 0 ≤ y ∧ x*y = 1 ⇒ x + y ≤ x² + y²`. Harrison's
-- original form; the companion 1714 above drops the `0 ≤ x, 0 ≤ y`
-- hypotheses. Conclusion is written in the natural `a ≤ b` shape; the
-- reifier rewrites it as `0 ≤ b − a` via the sub-bridge.
example (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) (_h : x*y = 1) :
    x + y ≤ x^2 + y^2 := by sos

/-! ### Negate-and-refute path (Harrison's `INT_SOS` trick)

ℕ/ℤ goals whose polynomial inequality is *not* a Putinar consequence of
the constraints over ℝ — they hold only because the variables are
restricted to the integer points of the cone. The lift pre-pass tries
the direct Putinar path first; on failure it negates the conclusion,
applies the integer discreteness rewrite `¬ (a ≤ b) ⟺ b + 1 ≤ a`, and
hands the resulting system to the existing `.infeasible` SOS arm. See
`SOS.Lift.refuteToReal` and `sos.ml:1336`. -/

-- sos.ml:1728 — Harrison's canonical example for `INT_SOS`. The
-- Putinar relaxation over ℝ fails: at `n = 0.5` (admissible, `n ≥ 0`)
-- the polynomial `n² − n = −0.25 < 0`. Refute path finds the rational
-- infeasibility cert `(5·↑n − 3)²/16 + (5/16)·↑n + (25/16)·(↑n − ↑n² −
-- 1) = −1`.
example : ∀ n : ℕ, n ≤ n * n := by sos

-- ℤ analogue with explicit non-negativity precondition.
example : ∀ n : ℤ, 0 ≤ n → n ≤ n * n := by sos

-- ℕ with a strict precondition `0 < n`. The discreteness rewrite
-- applied at every hypothesis turns `0 < n` into `1 ≤ n`; the
-- `0 ≤ ↑n` fact from `Nat.cast_nonneg` carries the search.
example : ∀ n : ℕ, 0 < n → n ≤ n * n := by sos

-- Control: the inequality goes the other way for almost all `n`,
-- so the search shouldn't find a refutation certificate.
example : True := by
  fail_if_success
    (have : ∀ n : ℕ, n * n ≤ n := by sos)
  trivial

-- sos.ml:1725 — `∀ m n : ℕ. 2·m + n = (n + m) + m`. Pure ring identity
-- over ℕ; exercises the ℕ-lift pre-pass on a degenerate (no SOS work
-- needed) equality goal.
example : ∀ m n : ℕ, 2*m + n = (n + m) + m := by sos
