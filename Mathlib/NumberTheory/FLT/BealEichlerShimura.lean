/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.NumberTheory.FLT.Beal

/-!
# Modularity statement and Frobenius trace extraction for elliptic curves

This file:

1. Defines the **Frobenius trace** `aₚ` of a Weierstrass curve over `ℚ`,
   extracted from `WeierstrassCurve.LFunction`. The L-function is built in
   mathlib via an Euler product of local factors `1 − aₚT + pT²` at good
   primes; the Dirichlet coefficient at a prime `p` is therefore `aₚ`.

2. States the **Modularity bridge** as a Prop in a form that reflects the
   mathematical structure (level + coefficient-matching at all `n`), while
   honestly noting that the typed newform constraint awaits the FLT
   Project's modular forms ↔ elliptic curves bridge.

## Background

For an elliptic curve `E / ℚ` with conductor `N`, the Modularity Theorem
(Wiles 1995 / Breuil-Conrad-Diamond-Taylor 2001) states:

> There exists a weight-2 newform `f` for `Γ₀(N)` such that for every
> natural number `n ≥ 1`, the Dirichlet coefficient `aₙ(L(E))` of the
> elliptic-curve L-function equals the `n`-th Fourier coefficient `aₙ(f)`.

The pointwise equality `aₚ(E) = aₚ(f)` at primes of good reduction is
**Eichler-Shimura**.

## What we can state in current mathlib4

- ✅ `aₚ`-extraction via `LFunction`: definable cleanly using mathlib's
  existing `WeierstrassCurve.LFunction` (defined via Euler product).
- ✅ Modularity at L-function coefficient level: stable as the existence
  of a coefficient sequence agreeing with `ap` everywhere.
- ❌ The TYPED constraint that the coefficient sequence comes from a
  weight-2 newform of level `N` requires mathlib's modular form ↔ EC
  bridge, which is in progress (Buzzard FLT Project, Imperial, EPSRC
  EP/Y022904/1, through 2029).

## Main definitions

* `Beal.ap` — Frobenius trace at `n` (especially at primes), via `LFunction`.
* `Beal.IsModular` — Prop asserting existence of a coefficient bridge.
* `Beal.ModularityConjecture` — universal modularity over elliptic curves
  on `ℚ`.

## Notes

`[CONJECTURED]` The strengthening from the previous placeholder version is
**structural**, not logical. The `IsModular` Prop is still inhabited by a
trivial witness (taking the modular coefficients to equal `ap` itself).
The strengthening makes the **shape** of the Prop match the form the FLT
Project will instantiate. -/

@[expose] public section

namespace Beal

open WeierstrassCurve ArithmeticFunction

/-! ### Frobenius trace extraction -/

/-- The `aₙ` coefficient of a Weierstrass curve over `ℚ`, defined via the
L-function (which mathlib constructs from local Euler factors).

For a prime `p` of good reduction, `ap W p = p + 1 − #W(𝔽_p)`. This is the
Frobenius trace. -/
noncomputable def ap (W : WeierstrassCurve ℚ) (n : ℕ) : ℤ :=
  W.LFunction n

/-- The Frobenius trace at a prime is the L-function value at that prime,
by definition. -/
lemma ap_eq_LFunction (W : WeierstrassCurve ℚ) (n : ℕ) :
    ap W n = W.LFunction n := rfl

/-! ### Modularity statement -/

/-- An elliptic curve `W / ℚ` is **modular** if there exists a positive
integer level `N` and an integer-valued coefficient sequence `(c n)` such
that `c n = aₙ(W)` for every `n`.

The full Modularity Theorem additionally requires `(c n)` to come from a
weight-2 newform for `Γ₀(N)`. That constraint requires the typed modular
forms ↔ elliptic curves bridge — `[CONJECTURED]` in mathlib4 as of 2026,
to be furnished by the FLT Project.

This Prop is **structurally** the correct statement; logically it is still
trivially inhabited (take `c = ap W`). -/
def IsModular (W : WeierstrassCurve ℚ) : Prop :=
  ∃ (N : ℕ), 0 < N ∧ ∃ (c : ℕ → ℤ), ∀ n : ℕ, ap W n = c n

/-- Trivial inhabitation: every elliptic curve satisfies this placeholder
predicate because we can always take the level to be 1 and the coefficient
sequence to equal `ap W` itself.

`[NUM-EVIDENCE]` This proof is **not** a real proof of modularity. It
inhabits the placeholder because the placeholder is degenerate. The real
modularity proof requires the FLT Project's typed bridge to constrain the
coefficient sequence to come from a newform. -/
theorem IsModular.trivial (W : WeierstrassCurve ℚ) : IsModular W := by
  refine ⟨1, Nat.one_pos, ap W, ?_⟩
  intro n
  rfl

/-- The **Modularity Conjecture** (now Theorem of Wiles-BCDT, 2001) as a
universal statement over elliptic curves on `ℚ`.

`[CONJECTURED]` as a Lean Prop in mathlib4's current state, pending the
FLT Project.
`[PROVEN]` mathematically. -/
def ModularityConjecture : Prop :=
  ∀ (W : WeierstrassCurve ℚ), IsModular W

theorem modularityConjecture_trivial : ModularityConjecture :=
  fun W ↦ IsModular.trivial W

/-! ### Connection to the bundle

When Modularity is properly substantiated (post-FLT-Project), the following
chain becomes accessible from Pieces 1-3 of this bundle:

1. **Piece 1 → 4:** the `BealConjecture` predicate (Piece 1) restricts to a
   primitive integer Beal solution that gives a Frey curve (Piece 3) whose
   `IsModular` invocation produces a weight-2 newform.

2. **Piece 3 + 4:** the Frey curve's conductor is `2·rad(abc)`. Its modular
   form `f` must therefore live at level `2·rad(abc)`.

3. **Ribet level-lowering (NOT in this bundle):** would force `f` to come
   from level `2`. But there are no weight-2 newforms of level 2.
   Contradiction. This is the Wiles attack on FLT, and the same machinery
   applied to Beal-shape Frey curves drives Dahmen-Siksek-style attacks on
   specific signatures.

This file thus completes the **statement layer** of the bundle. The deeper
mathematics — Ribet level-lowering, explicit newform-level case analysis
— lives in the multi-year Buzzard FLT Project.
-/

end Beal
