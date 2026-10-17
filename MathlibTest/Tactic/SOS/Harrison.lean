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
-/
import Mathlib.Tactic.SOS

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

-- sos.ml:1809 — 3-variable degree-6
example (x y z : ℝ) :
    0 ≤ 9*x^2*y^4 + 9*x^2*z^4 + 36*x^2*y^3 + 36*x^2*y^2
        - 48*x*y*z^2 + 4*y^4 + 4*z^4 - 16*y^3 + 16*y^2 := by sos

-- sos.ml:1819 — 3-variable degree-4 with linear+constant tail.
example (x y z : ℝ) :
    0 ≤ x^4 + y^4 + z^4 - 4*x*y*z + x + y + z + 3 := by sos

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

-- sos.ml:1886 — 4-variable degree-4, with `Z₂×Z₂` symmetry.
example (x y z w : ℝ) :
    0 ≤ x^4 + 4*x^2*y^2 + 2*x*y*z^2 + 2*x*y*w^2 + y^4 + z^4 + w^4
        + 2*z^2*w^2 + 2*x^2*w + 2*y^2*w + 2*x*y + 3*w^2 + 2*z^2 + 1 := by sos

-- sos.ml:1891 — 4-variable degree-6
example (x y z w : ℝ) :
    0 ≤ w^6 + 2*z^2*w^3 + x^4 + y^4 + z^4 + 2*x^2*w + 2*x^2*z
        + 3*x^2 + w^2 + 2*z*w + z^2 + 2*z + 2*w + 1 := by sos

/-! ### `REAL_SOS` with Putinar-style hypotheses -/

-- sos.ml:1718 — `0 ≤ x ∧ 0 ≤ y ⇒ x*y*(x+y)² ≤ (x²+y²)²`
example (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    0 ≤ (x^2 + y^2)^2 - x*y*(x + y)^2 := by sos

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

/-! ### Equality-hypothesis ports

The four-variable spherical constraint (1650) and Harrison's `xy = 1`
forms (1714, 1710) exercise nonconstant equality cofactors. -/

-- Control for the three-variable spherical launch example: the same
-- conclusion without the equality fails at `x := y := z := 2`.
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

-- Control for the discriminant launch example: false at
-- `a = c := 1, b := 0` without the equality hypothesis.
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
