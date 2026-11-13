/-
Copyright (c) 2026 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas, Pedro Saccomani, Sarah Pereira
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Sign

/-!
# The sign of a polynomial immediately to the right of a point

A nonzero real polynomial has finitely many roots, so its sign is constant on a small interval
`(x, x + ε)` to the right of any point `x`. This file defines that sign, `Polynomial.signRight x p`,
as the sign of the trailing coefficient of the taylor polynomial of `p` around `x`, and develops
its basic properties: it vanishes only for `p = 0`, it is multiplicative, and it is computed by the
recursion `signRight x p = sign (p.eval x)` if `p.eval x ≠ 0` and `signRight x p = signRight x
(derivative p)` otherwise.

This is the local invariant behind Sturm's theorem, where it determines the direction in which the
sign of a Sturm sequence changes across a root.

## Main definitions

* `Polynomial.signRight x p`: the sign of `p` immediately to the right of `x`.

## Main results

* `Polynomial.eventually_sign_eq_signRight`, `Polynomial.signRight_eq_iff`: the defining property,
  `sign (p.eval y) = signRight x p` for all `y` in some interval `(x, x + ε)`.
* `Polynomial.signRight_eq_zero_iff`: `signRight x p = 0` if and only if `p = 0`.
* `Polynomial.signRight_mul`, `Polynomial.signRight_neg`, `Polynomial.signRight_C`:
  `signRight x` is multiplicative and compatible with negation and constants.
* `Polynomial.signRight_of_eval_ne_zero`: away from the roots of `p`, `signRight x p` is the sign of
  `p.eval x`.
* `Polynomial.signRight_of_eval_eq_zero`: at a root of `p`, `signRight x p` is `signRight x` of the
  derivative of `p`.

-/

open Polynomial Set Filter SignType Topology

public noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R] [LinearOrder R]

def signRight (x : R) (p : R[X]) : SignType :=
  SignType.sign (taylor x p).trailingCoeff

theorem signRight_zero (x : R) : signRight x (0 : Polynomial R) = 0 := by
  rw [signRight, map_zero, trailingCoeff_zero, sign_zero]

theorem signRight_ne_zero {x : R} {p : R[X]} (hp : p ≠ 0) : signRight x p ≠ 0 := by
  rw [signRight, ne_eq, sign_eq_zero_iff, trailingCoeff_eq_zero, taylor_eq_zero]
  exact hp

/-- `signRight x p` can only be `0` if `p` is `0`. -/
@[simp]
theorem signRight_eq_zero_iff {x : R} {p : R[X]} : signRight x p = 0 ↔ p = 0 :=
  ⟨fun h => by_contra fun hp => signRight_ne_zero hp h, fun h => by rw [h, signRight_zero]⟩

/-- `signRight` of a constant equals the sign of the constant. -/
@[simp]
theorem signRight_C (x c : R) : signRight x (C c) = sign c := by
  rw [signRight, trailingCoeff, taylor_C, natTrailingDegree_C, coeff_C_zero]

/-- `signRight` commutes with negation. -/
theorem signRight_neg [IsOrderedRing R] (x : R) (p : R[X]) : signRight x (-p) = -signRight x p := by
  rw [signRight, signRight, map_neg, trailingCoeff_neg, Left.sign_neg]

theorem signRight_X_sub_C_pow [IsOrderedRing R] [Nontrivial R] (a : R) (n : ℕ) :
    signRight a ((X - C a) ^ n) = 1 := by
  rw [signRight, taylor_pow, taylor_X_sub_C, trailingCoeff_X_pow, sign_one]

/-- `signRight` is a multiplicative function. -/
theorem signRight_mul [IsStrictOrderedRing R] (x : R) (p q : R[X]) :
    signRight x (p * q) = signRight x p * signRight x q := by
  rw [signRight, signRight, signRight, taylor_mul, trailingCoeff_mul, sign_mul]

theorem signRight_C_mul [IsStrictOrderedRing R] (x c : R) (p : R[X]) :
    signRight x (C c * p) = sign c * signRight x p := by
  rw [signRight_mul, signRight_C]

theorem signRight_mul_self [IsStrictOrderedRing R] {x : R} {p : R[X]} (hp : p ≠ 0) :
    signRight x (p * p) = 1 := by
  rw [signRight_mul]
  have := signRight_ne_zero (x := x) hp
  cases h : signRight x p <;> simp_all

/-- Away from its roots, the sign of `p` to the right of `x` is the sign of `p x`. -/
theorem signRight_of_eval_ne_zero {x : R} {p : R[X]} (h : eval x p ≠ 0) :
    signRight x p = sign (eval x p) := by
  rw [signRight, trailingCoeff_eq_coeff_zero (by rwa [taylor_coeff_zero]), taylor_coeff_zero]

/-- At a root of `p`, the sign of `p` to the right of `x` is that of `derivative p`. -/
theorem signRight_of_eval_eq_zero [IsStrictOrderedRing R] {x : R} {p : R[X]} (h : p.eval x = 0) :
    signRight x p = signRight x (derivative p) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have ht : 0 < (taylor x p).natTrailingDegree := by
    rw [Nat.pos_iff_ne_zero, Ne, natTrailingDegree_eq_zero, taylor_eq_zero, taylor_coeff_zero]
    simp [hp, h]
  rw [signRight, signRight, taylor_derivative, trailingCoeff_derivative ht.ne', sign_mul,
    sign_pos (Nat.cast_pos.mpr ht), mul_one]

theorem signRight_derivative_mul [IsStrictOrderedRing R] {x : R} {p : R[X]} (hp : p ≠ 0)
    (hev : eval x p = 0) : signRight x (derivative p * p) = 1 := by
  rw [signRight_mul, ← signRight_of_eval_eq_zero hev]
  have := signRight_ne_zero (x := x) hp
  cases h : signRight x p <;> simp_all

theorem signRight_add {x : R} {p q : R[X]} (hp : eval x p = 0) (hq : eval x q ≠ 0) :
    signRight x (p + q) = signRight x q := by
  have h : eval x (p + q) ≠ 0 := by rw [eval_add, hp, zero_add]; exact hq
  rw [signRight_of_eval_ne_zero h, signRight_of_eval_ne_zero hq, eval_add, hp, zero_add]

theorem signRight_mod {K : Type*} [Field K] [LinearOrder K] {x : K} {p q : K[X]}
    (hp : p.eval x = 0) (hq : q.eval x ≠ 0) : signRight x (q % p) = signRight x q := by
  have h : (q % p).eval x = q.eval x := eval_mod_eq_self_of_root hp
  rw [signRight_of_eval_ne_zero (h ▸ hq), signRight_of_eval_ne_zero hq, h]

section OrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [TopologicalSpace R]
  [OrderTopology R]

/-- The equation `sign (eval y p) = signRight x p` holds for all `y` in some interval
`(x, x + ε)`. -/
theorem eventually_sign_eq_signRight (x : R) (p : R[X]) :
    ∀ᶠ y in 𝓝[>] x, sign (eval y p) = signRight x p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [signRight]
  -- write `p = (X - C x) ^ m * g` with `g` not vanishing at `x`
  set m := rootMultiplicity x p
  set g := p /ₘ (X - C x) ^ m
  have hg : g.eval x ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero x hp
  have hpg : p = (X - C x) ^ m * g := (pow_mul_divByMonic_rootMultiplicity_eq p x).symm
  -- algebraically, `signRight x p` is the sign of `g` at `x`
  have hsign : signRight x p = sign (g.eval x) := by
    rw [signRight, hpg, taylor_mul, taylor_pow, taylor_X_sub_C, trailingCoeff_mul,
      trailingCoeff_X_pow, one_mul, trailingCoeff_eq_coeff_zero (by rwa [taylor_coeff_zero]),
      taylor_coeff_zero]
  -- near `x`, `g` keeps the sign it has at `x`
  have hg_near := (continuousAt_sign_of_ne_zero hg).tendsto.comp (g.continuous.tendsto x)
  rw [nhds_discrete SignType, tendsto_pure] at hg_near
  -- and to the right of `x`, `(y - x) ^ m` is positive
  filter_upwards [hg_near.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hxy
  rw [hsign, hpg, eval_mul, sign_mul, eval_pow, eval_sub, eval_X, eval_C,
    sign_pos (pow_pos (sub_pos.mpr hxy) m), one_mul]
  exact hy

/-- Immediately to the right of `x`, a polynomial has a constant sign. -/
theorem exists_eventually_sign_eq (x : R) (p : R[X]) :
    ∃ s : SignType, ∀ᶠ y in 𝓝[>] x, sign (eval y p) = s :=
  ⟨_, eventually_sign_eq_signRight x p⟩

theorem signRight_eq_of_eventually {x : R} {p : R[X]} {s : SignType}
    (h : ∀ᶠ y in 𝓝[>] x, sign (eval y p) = s) : signRight x p = s := by
  obtain ⟨y, hy1, hy2⟩ := ((eventually_sign_eq_signRight x p).and h).exists
  rw [← hy1, hy2]

/-- `signRight x p` is the unique sign `s` such that `sign (eval y p) = s` for all `y` in some
interval `(x, x + ε)`. -/
theorem signRight_eq_iff {x : R} {p : R[X]} {s : SignType} :
    signRight x p = s ↔ ∀ᶠ y in 𝓝[>] x, sign (eval y p) = s :=
  ⟨fun h => h ▸ eventually_sign_eq_signRight x p, signRight_eq_of_eventually⟩

end OrderedField

end Polynomial
