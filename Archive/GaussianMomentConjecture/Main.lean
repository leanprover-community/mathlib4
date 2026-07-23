/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKOmegaWiring
import Mathlib

set_option linter.minImports true

/-!
# The Gaussian moment conjecture in dimension two

This module is the front door of the formalization: `lake build
Archive.GaussianMomentConjecture.Main` compiles the entire proof.

The Gaussian moment conjecture asserts that the kernel of the Gaussian (Wick) expectation is a
Mathieu–Zhao subspace of the polynomial ring; it implies the Jacobian conjecture, by
[Derksen, van den Essen and Zhao][derksen-vandenessen-zhao2017]. This file proves the case of two
variables.

## Statement

For `P Q : ℂ[X₀, X₁]`, if every central power `E (P ^ m)` vanishes for `m ≥ 1`, then
`E (Q * P ^ m)` vanishes for all sufficiently large `m`. Here `E P = ∑ s, P.coeff s * wt s` is the
Gaussian (Wick) expectation, with `wt s = (s 0)!` when `s 0 = s 1` and `0` otherwise; its kernel is
the Mathieu–Zhao object in two variables.

## Architecture of the proof

```
GMC(2)  ⇐  NC2  ⇐  DvdK1  ⇐  SinglePolyCrux  (the small-root packet product is c * t)
```

* the charge reduction `NC2 ⇒ GMC(2)` and the step `DvdK1 ⇒ NC2` are elementary;
* `SinglePolyCrux` is discharged by the Weierstrass small-root-product identity `Π = c * t`, whose
  analytic core is `d_t h(0, t) = 0` under the vanishing hypothesis of
  [Duistermaat and van der Kallen][duistermaat-vanderkallen1998]. This is proved in the unified
  `(F⸨x⸩)⟦t⟧` frame: writing `Φ = xᴹ - t * R = P * h`, one has
  `[x⁰](-R/Φ) = [x⁰](P_t/P) + d_t h(0, t)/h(0, t)`, the disk/annulus split of `[x⁰]`;
* the packet product is transported to the splitting field through
  `Ω = AlgebraicClosure (LaurentSeries ℂ)` by a valuation-free algebraic embedding together with
  Vieta's formulas, and there the Galois orbit-product yields the contradiction.

## Verification

The whole transitive dependency is `sorry`-free, and `#print axioms` on the capstone below reports
`[propext, Classical.choice, Quot.sound]` — no `native_decide` and no additional axioms.
-/

namespace GMC2

/-- **The Gaussian moment conjecture in dimension two.** For `P Q : ℂ[X₀, X₁]`, if every central
power `E (P ^ m)` vanishes for `m ≥ 1`, then `E (Q * P ^ m)` vanishes for all large `m`. -/
theorem gmc2 (P Q : MvPolynomial (Fin 2) ℂ)
    (hnull : ∀ m : ℕ, 1 ≤ m → E (P ^ m) = 0) :
    ∃ N : ℕ, ∀ m ≥ N, E (Q * P ^ m) = 0 :=
  GMC2DvdKOmegaWiring.gmc2_unconditional P Q hnull

end GMC2

