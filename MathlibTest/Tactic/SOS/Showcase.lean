/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A curated selection of `by sos` examples for the launch post.
-/
import Mathlib.Tactic.SOS

-- Cauchy-Schwarz.
example (a b c d : ℝ) :
    0 ≤ (a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 := by sos

-- The discriminant of a real-rooted quadratic. The search discovers
-- the cofactor `-4a` for `b^2 - 4ac = (2ax + b)^2 + (-4a)(ax^2 + bx + c)`.
example (a b c x : ℝ) (_h : a*x^2 + b*x + c = 0) :
    0 ≤ b^2 - 4*a*c := by sos

-- `n ≤ n^2` is false over ℝ at `n = 1/2`; closed by negating the
-- conclusion and refuting over ℝ via `Nat.lt_iff_add_one_le`.
example : ∀ n : ℕ, n ≤ n * n := by sos

-- Schur's inequality on the unit sphere.
example (x y z : ℝ) (_h : x^2 + y^2 + z^2 = 1) :
    0 ≤ 3 - (x + y + z)^2 := by sos

-- Motzkin's polynomial is non-negative but not SOS (Hilbert 1888);
-- multiplying by `x^2 + y^2 + z^2` makes it SOS -- a polynomial-case
-- witness for Hilbert's 17th problem.
example (x y z : ℝ) :
    0 ≤ (x^2 + y^2 + z^2) *
        (x^4*y^2 + x^2*y^4 + z^6 - 3*x^2*y^2*z^2) := by sos

-- The *bare* Motzkin polynomial, with no multiplier supplied. Being
-- non-negative but not SOS, it has no direct certificate; `maxRefutationPower`
-- opts into the Positivstellensatz power refutation (Harrison's
-- `REAL_NONLINEAR_PROVER`): negate to `0 < -M`, find `-M = σ₀ + σ₁·(-M)`,
-- and recover the exact rational certificate by facial reduction. Off by
-- default because each power is a family of growing-degree CSDP solves.
example (x y : ℝ) :
    0 ≤ x^4*y^2 + x^2*y^4 + 1 - 3*x^2*y^2 := by
  sos (config := { maxRefutationPower := 1 })

-- Zeng et al., JSC vol 37 (2004), p83-99 (Harrison `sos.ml:1879`).
example (x y z : ℝ) :
    0 ≤ x^4*y^4 - 2*x^5*y^3*z^2 + x^6*y^2*z^4
        + 2*x^2*y^3*z - 4*x^3*y^2*z^3 + 2*x^4*y*z^5
        + z^2*y^2 - 2*z^4*y*x + z^6*x^2 := by sos

-- The Euclidean-division equation. The lift introduces the witness
-- `b * (a/b) + a%b = a` from `b ≠ 0`; the equality conclusion splits
-- into ≤-pair via `le_antisymm` and each side trivialises.
example : ∀ a b : ℕ, b ≠ 0 → a = b * (a / b) + a % b := by sos

-- A "slightly tedious lemma" Harrison highlights from his own workflow
-- (TPHOLs 2007 paper, p.11). The witness `(r-t)^2 + (1-t)(1+t)` uses
-- the product of the two interval hypotheses.
example (r t : ℝ) (_h1 : 0 ≤ t + 1) (_h2 : 0 ≤ 1 - t) :
    0 ≤ 1 + r^2 - 2*r*t := by sos

-- Natural witness `(x-1)(y-1) ≥ 0` -- a product of the two hypotheses
-- (Harrison `sos.ml:1654`).
example (x y : ℝ) (_hx : 0 ≤ x - 1) (_hy : 0 ≤ y - 1) :
    0 ≤ x*y - (x + y - 1) := by sos
