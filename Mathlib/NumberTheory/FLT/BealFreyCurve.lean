/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.NumberTheory.FLT.Beal

/-!
# The Frey-Hellegouarch curve

Given integers `a, b` and an exponent `n ≥ 1`, the **Frey-Hellegouarch curve**
is the elliptic curve

  `E_{a,b,n} :  y² = x(x - aⁿ)(x + bⁿ)`

expanded into Weierstrass form. It is the key geometric object underlying
Wiles's proof of Fermat's Last Theorem and the modular method for the
generalized Fermat / Beal equation.

This file gives the curve as a `WeierstrassCurve ℤ` and computes its
discriminant, both in its raw polynomial form (depending on `a^n + b^n`)
and in its simplified form under an FLT-shape relation `a^n + b^n = c^n`.

## Main definitions

* `Beal.freyCurve a b n` — the Frey-Hellegouarch curve as a Weierstrass form.

## Main results

* `Beal.freyCurve_Δ_eq` — explicit formula for the discriminant.
* `Beal.freyCurve_Δ_of_flt` — under the FLT relation `aⁿ + bⁿ = cⁿ`, the
  discriminant collapses to `16 · (abc)^{2n}`. This is the formula that
  drives the entire modular method: the n-th-power structure of the
  discriminant feeds into level-lowering through Frey-Hellegouarch +
  Ribet machinery.

## Status

This file is a **definitional/algebraic piece**. It does NOT prove modularity
or attempt the Wiles-Ribet attack. It provides the cleanly-stated geometric
object that downstream Lean work (the Buzzard FLT Project, etc.) can consume.
-/

@[expose] public section

namespace Beal

open WeierstrassCurve

/-- The Frey-Hellegouarch curve associated to `(a, b, n)`.

  In affine Weierstrass form, the equation is
    `y² = x(x - aⁿ)(x + bⁿ) = x³ + (bⁿ − aⁿ)·x² − (aⁿ·bⁿ)·x`.
  We encode this as `a₁ = a₃ = a₆ = 0`, `a₂ = bⁿ − aⁿ`, `a₄ = −(aⁿ·bⁿ)`. -/
def freyCurve (a b : ℤ) (n : ℕ) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := b ^ n - a ^ n
  a₃ := 0
  a₄ := -(a ^ n * b ^ n)
  a₆ := 0

/-! ### Coefficient accessors (definitional unfoldings) -/

@[simp] lemma freyCurve_a₁ (a b : ℤ) (n : ℕ) : (freyCurve a b n).a₁ = 0 := rfl
@[simp] lemma freyCurve_a₂ (a b : ℤ) (n : ℕ) :
    (freyCurve a b n).a₂ = b ^ n - a ^ n := rfl
@[simp] lemma freyCurve_a₃ (a b : ℤ) (n : ℕ) : (freyCurve a b n).a₃ = 0 := rfl
@[simp] lemma freyCurve_a₄ (a b : ℤ) (n : ℕ) :
    (freyCurve a b n).a₄ = -(a ^ n * b ^ n) := rfl
@[simp] lemma freyCurve_a₆ (a b : ℤ) (n : ℕ) : (freyCurve a b n).a₆ = 0 := rfl

/-! ### Discriminant computation -/

/-- The discriminant of the Frey curve is `16 · (aⁿ · bⁿ · (aⁿ + bⁿ))²`.
    Under no further assumption on `(a, b, n)`. -/
theorem freyCurve_Δ_eq (a b : ℤ) (n : ℕ) :
    (freyCurve a b n).Δ = 16 * (a ^ n * b ^ n * (a ^ n + b ^ n)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈,
             freyCurve_a₁, freyCurve_a₂, freyCurve_a₃, freyCurve_a₄, freyCurve_a₆]
  ring

/-- Under the FLT-shape relation `aⁿ + bⁿ = cⁿ`, the Frey curve discriminant
    is exactly `16 · (a · b · c)^(2n)`. This is the formula that makes the
    Frey curve useful in the modular method: its `n`-th-power discriminant
    structure forces a level-lowering argument. -/
theorem freyCurve_Δ_of_flt (a b c : ℤ) (n : ℕ)
    (heq : a ^ n + b ^ n = c ^ n) :
    (freyCurve a b n).Δ = 16 * (a * b * c) ^ (2 * n) := by
  rw [freyCurve_Δ_eq, heq]
  -- Goal: 16 * (aⁿ · bⁿ · cⁿ)² = 16 * (a·b·c)^(2n)
  have h_mul_pow : a ^ n * b ^ n * c ^ n = (a * b * c) ^ n := by
    rw [mul_pow, mul_pow]
  rw [h_mul_pow]
  -- Goal: 16 * ((a·b·c)ⁿ)² = 16 * (a·b·c)^(2n)
  rw [← pow_mul]
  -- Goal: 16 * (a·b·c)^(n*2) = 16 * (a·b·c)^(2n)
  ring_nf

end Beal
