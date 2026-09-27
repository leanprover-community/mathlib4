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
as the limit of `sign (p.eval y)` as `y → x` from the right, and develops its basic properties:
it vanishes only for `p = 0`, it is multiplicative, and it is computed by the recursion
`signRight x p = sign (p.eval x)` if `p.eval x ≠ 0` and `signRight x p = signRight x (derivative p)`
otherwise.

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

## Implementation notes

The definition and all results are stated over `ℝ`, but they hold over any real closed field, and
should eventually be generalised to `IsRealClosed`. Two ingredients stand in the way: the
intermediate value theorem for polynomials over a real closed field, which Mathlib does not have
yet and which is needed for `exists_eventually_sign_eq` (the proof here uses connectedness of
intervals in `ℝ`), and the mean value theorem, used in `signRight_of_eval_eq_zero`, which can be
replaced by an algebraic argument factoring the root out of `p`.
-/

open Polynomial Set Filter SignType Topology

public section

namespace Polynomial

/-- Immediately to the right of `x`, a polynomial has a constant sign. -/
theorem exists_eventually_sign_eq (x : ℝ) (p : ℝ[X]) :
    ∃ s : SignType, ∀ᶠ y in 𝓝[>] x, sign (eval y p) = s := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, Eventually.of_forall fun y => by simp⟩
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    ((eventually_eval_ne_zero_codiscrete hp).filter_mono
      ((nhdsGT_le_nhdsNE x).trans (nhdsNE_le_codiscrete x)))
  have hb : x < b := hb
  refine ⟨sign (eval ((x + b) / 2) p), mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨b, hb, fun y hy => ?_⟩⟩
  exact isPreconnected_Ioo.sign_eq_of_continuousOn p.continuousOn (fun z hz => hsub hz) hy
    ⟨by linarith, by linarith⟩

/-- The sign of `p` immediately to the right of `x`: the eventual value of `sign (eval y p)` as
`y → x` from the right. -/
noncomputable def signRight (x : ℝ) (p : ℝ[X]) : SignType :=
  limUnder (𝓝[>] x) fun y => sign (eval y p)

/-- The equation `sign (eval y p) = signRight x p` holds for all `y` in some interval
`(x, x + ε)`. -/
theorem eventually_sign_eq_signRight (x : ℝ) (p : ℝ[X]) :
    ∀ᶠ y in 𝓝[>] x, sign (eval y p) = signRight x p := by
  obtain ⟨s, hs⟩ := exists_eventually_sign_eq x p
  have ht : Tendsto (fun y => sign (eval y p)) (𝓝[>] x) (𝓝 s) := by
    rw [nhds_discrete SignType, tendsto_pure]; exact hs
  rw [signRight, ht.limUnder_eq]
  exact hs

theorem signRight_eq_of_eventually {x : ℝ} {p : ℝ[X]} {s : SignType}
    (h : ∀ᶠ y in 𝓝[>] x, sign (eval y p) = s) : signRight x p = s := by
  obtain ⟨y, hy1, hy2⟩ := ((eventually_sign_eq_signRight x p).and h).exists
  rw [← hy1, hy2]

/-- `signRight x p` is the unique sign `s` such that `sign (eval y p) = s` for all `y` in some
interval `(x, x + ε)`. -/
theorem signRight_eq_iff {x : ℝ} {p : ℝ[X]} {s : SignType} :
    signRight x p = s ↔ ∀ᶠ y in 𝓝[>] x, sign (eval y p) = s :=
  ⟨fun h => h ▸ eventually_sign_eq_signRight x p, signRight_eq_of_eventually⟩

@[simp]
theorem signRight_zero (x : ℝ) : signRight x 0 = 0 :=
  signRight_eq_of_eventually (Eventually.of_forall fun _ => by simp)

theorem signRight_ne_zero {x : ℝ} {p : ℝ[X]} (hp : p ≠ 0) : signRight x p ≠ 0 := by
  obtain ⟨y, hy1, hy2⟩ := ((eventually_sign_eq_signRight x p).and
    ((eventually_eval_ne_zero_codiscrete hp).filter_mono
      ((nhdsGT_le_nhdsNE x).trans (nhdsNE_le_codiscrete x)))).exists
  rw [← hy1]
  exact sign_ne_zero.mpr hy2

/-- `signRight x p` can only be `0` if `p` is `0`. -/
@[simp]
theorem signRight_eq_zero_iff {x : ℝ} {p : ℝ[X]} : signRight x p = 0 ↔ p = 0 :=
  ⟨fun h => by_contra fun hp => signRight_ne_zero hp h, fun h => by rw [h, signRight_zero]⟩

/-- `signRight` is a multiplicative function. -/
theorem signRight_mul (x : ℝ) (p q : ℝ[X]) :
    signRight x (p * q) = signRight x p * signRight x q :=
  signRight_eq_of_eventually <|
    ((eventually_sign_eq_signRight x p).and (eventually_sign_eq_signRight x q)).mono
      fun y ⟨h1, h2⟩ => by rw [eval_mul, sign_mul, h1, h2]

/-- `signRight` commutes with negation. -/
theorem signRight_neg (x : ℝ) (p : ℝ[X]) : signRight x (-p) = -signRight x p :=
  signRight_eq_of_eventually <|
    (eventually_sign_eq_signRight x p).mono fun y hy => by rw [eval_neg, Left.sign_neg, hy]

/-- `signRight` of a constant equals the sign of the constant. -/
@[simp]
theorem signRight_C (x c : ℝ) : signRight x (C c) = sign c :=
  signRight_eq_of_eventually (Eventually.of_forall fun y => by rw [eval_C])

theorem signRight_C_mul (x c : ℝ) (p : ℝ[X]) : signRight x (C c * p) = sign c * signRight x p := by
  rw [signRight_mul, signRight_C]

theorem signRight_X_sub_C_pow (a : ℝ) (n : ℕ) : signRight a ((X - C a) ^ n) = 1 :=
  signRight_eq_of_eventually <| eventually_mem_nhdsWithin.mono fun y hy => by
    rw [eval_pow, eval_sub, eval_X, eval_C]
    exact sign_pos (pow_pos (sub_pos.mpr hy) n)

theorem signRight_mul_self {x : ℝ} {p : ℝ[X]} (hp : p ≠ 0) : signRight x (p * p) = 1 := by
  rw [signRight_mul]
  have := signRight_ne_zero (x := x) hp
  exact (mul_eq_one_iff_inv_eq₀ this).mpr rfl

/-- Away from its roots, the sign of `p` to the right of `x` is the sign of `p x`. -/
theorem signRight_of_eval_ne_zero {x : ℝ} {p : ℝ[X]} (h : eval x p ≠ 0) :
    signRight x p = sign (eval x p) := by
  apply signRight_eq_of_eventually
  have := (continuousAt_sign_of_ne_zero h).tendsto.comp (p.continuous.tendsto x)
  rw [nhds_discrete SignType, tendsto_pure] at this
  exact this.filter_mono nhdsWithin_le_nhds

/-- At a root of `p`, the sign of `p` to the right of `x` is that of `derivative p`. -/
theorem signRight_of_eval_eq_zero {x : ℝ} {p : ℝ[X]} (hev : eval x p = 0) :
    signRight x p = signRight x (derivative p) := by
  apply signRight_eq_of_eventually
  obtain ⟨b, hb, hb2⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (eventually_sign_eq_signRight x (derivative p))
  refine mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨b, hb, fun y hy => ?_⟩
  -- mean value theorem: `eval y p = (y - x) * eval c (derivative p)` for some `c ∈ (x, y)`
  obtain ⟨c, ⟨hc1, hc2⟩, hc3⟩ :=
    exists_deriv_eq_slope (fun y => eval y p) hy.1 p.continuousOn p.differentiableOn
  rw [Polynomial.deriv, hev, sub_zero, eq_div_iff (sub_pos.mpr hy.1).ne'] at hc3
  have hc : sign (eval c (derivative p)) = signRight x (derivative p) :=
    hb2 ⟨hc1, lt_trans hc2 hy.2⟩
  change sign (eval y p) = _
  rw [← hc3, sign_mul, sign_pos (sub_pos.mpr hy.1), mul_one, hc]

theorem signRight_derivative_mul {x : ℝ} {p : ℝ[X]} (hp : p ≠ 0) (hev : eval x p = 0) :
    signRight x (derivative p * p) = 1 := by
  rw [signRight_mul, ← signRight_of_eval_eq_zero hev]
  have := signRight_ne_zero (x := x) hp
  exact (mul_eq_one_iff_inv_eq₀ this).mpr rfl

theorem signRight_add {x : ℝ} {p q : ℝ[X]} (hp : eval x p = 0) (hq : eval x q ≠ 0) :
    signRight x (p + q) = signRight x q := by
  have h : eval x (p + q) ≠ 0 := by rw [eval_add, hp, zero_add]; exact hq
  rw [signRight_of_eval_ne_zero h, signRight_of_eval_ne_zero hq, eval_add, hp, zero_add]

theorem signRight_mod {x : ℝ} {p q : ℝ[X]} (hp : eval x p = 0) (hq : eval x q ≠ 0) :
    signRight x (q % p) = signRight x q := by
  have h : eval x (q % p) ≠ 0 := by rw [eval_mod_eq_self_of_root hp]; exact hq
  rw [signRight_of_eval_ne_zero h, signRight_of_eval_ne_zero hq, eval_mod_eq_self_of_root hp]

end Polynomial
