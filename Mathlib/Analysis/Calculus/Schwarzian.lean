/-
Copyright (c) 2026 Woomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Woomou
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Schwarzian Derivative

This file defines the Schwarzian derivative of a real-valued function `f : ℝ → ℝ` at `x`,
`S(f)(x) = f'''(x) / f'(x) - (3 / 2) * (f''(x) / f'(x)) ^ 2`, and establishes its fundamental
algebraic and analytic properties: the cocycle chain rule, closure of negative Schwarzian
derivative under composition, vanishing on affine maps, and the explicit formula for the
logistic family.

## Main definitions

* `schwarzianVal`: the algebraic Schwarzian expression
  `d3 / d1 - (3 / 2) * (d2 / d1) ^ 2` in terms of first, second, and third derivative values.
* `schwarzian`: the Schwarzian derivative of `f : ℝ → ℝ` at `x : ℝ`,
  defined via `deriv` and `iteratedDeriv`.

## Main results

* `schwarzianVal_comp`: the algebraic cocycle identity for the Schwarzian expression under
  composition.
* `schwarzian_comp_of_contDiffAt`: the chain rule
  `schwarzian (f ∘ g) x = schwarzian f (g x) * (deriv g x) ^ 2 + schwarzian g x` for functions
  that are `ContDiffAt ℝ 3` with nonvanishing first derivatives.
* `schwarzian_comp_neg`: closure of negative Schwarzian derivative under composition of
  `ContDiffAt ℝ 3` functions.
* `schwarzian_affine`: affine maps `x ↦ a * x + b` have identically zero Schwarzian derivative.
* `schwarzian_logistic` and `schwarzian_logistic_neg`: the logistic map `x ↦ μ * x * (1 - x)`
  satisfies `schwarzian (fun y ↦ μ * y * (1 - y)) x = -6 / (1 - 2 * x) ^ 2 < 0` away from
  `x = 1 / 2`.

## Implementation notes

We define `schwarzian f x` in terms of `schwarzianVal`, `deriv f x`, `iteratedDeriv 2 f x`, and
`iteratedDeriv 3 f x`, and provide bridging lemmas `schwarzian_eq_iteratedDeriv` and
`schwarzian_eq_deriv` to rewrite directly in terms of `iteratedDeriv` or nested `deriv`.
The analytic chain rule `schwarzian_comp_of_contDiffAt` is proved from `ContDiffAt ℝ 3` hypotheses
by reducing to the algebraic cocycle identity `schwarzianVal_comp`.

## References

* D. Singer, *Stable orbits and bifurcation of maps of the interval*, SIAM J. Appl. Math. 35
  (1978), no. 2, 260–267.
* W. de Melo and S. van Strien, *One-Dimensional Dynamics*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3), vol. 25, Springer-Verlag, Berlin, 1993.

## Tags

Schwarzian derivative, chain rule, cocycle, logistic map
-/

@[expose] public section

open scoped Topology

/-- The algebraic Schwarzian expression `d3 / d1 - (3 / 2) * (d2 / d1) ^ 2` evaluated on the
first, second, and third derivative values `(d1, d2, d3)`. -/
noncomputable def schwarzianVal (d1 d2 d3 : ℝ) : ℝ :=
  d3 / d1 - (3 / 2 : ℝ) * (d2 / d1) ^ 2

/-- The Schwarzian derivative of `f : ℝ → ℝ` at `x : ℝ`, defined as
`iteratedDeriv 3 f x / deriv f x - (3 / 2) * (iteratedDeriv 2 f x / deriv f x) ^ 2`. -/
noncomputable def schwarzian (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  schwarzianVal (deriv f x) (iteratedDeriv 2 f x) (iteratedDeriv 3 f x)

/-- Unfolding `schwarzian f x` directly in terms of `deriv` and `iteratedDeriv`. -/
theorem schwarzian_eq_iteratedDeriv (f : ℝ → ℝ) (x : ℝ) :
    schwarzian f x =
      iteratedDeriv 3 f x / deriv f x - (3 / 2 : ℝ) * (iteratedDeriv 2 f x / deriv f x) ^ 2 :=
  rfl

/-- Expressing `schwarzian f x` in terms of nested `deriv` applications. -/
theorem schwarzian_eq_deriv (f : ℝ → ℝ) (x : ℝ) :
    schwarzian f x =
      schwarzianVal (deriv f x) (deriv (deriv f) x) (deriv (deriv (deriv f)) x) := by
  simp only [schwarzian, iteratedDeriv_succ, iteratedDeriv_zero]

/-- The algebraic cocycle identity for the Schwarzian derivative under composition.
Given the first three derivatives `(f1, f2, f3)` of `f` at `g x` and `(g1, g2, g3)` of `g` at `x`,
the chain rule yields derivatives `(f1 * g1, f2 * g1 ^ 2 + f1 * g2,
f3 * g1 ^ 3 + 3 * f2 * g1 * g2 + f1 * g3)` for `f ∘ g`, whose Schwarzian value equals
`schwarzianVal f1 f2 f3 * g1 ^ 2 + schwarzianVal g1 g2 g3`. -/
theorem schwarzianVal_comp {f1 f2 f3 g1 g2 g3 : ℝ} (hf1 : f1 ≠ 0) (hg1 : g1 ≠ 0) :
    schwarzianVal
      (f1 * g1)
      (f2 * g1 ^ 2 + f1 * g2)
      (f3 * g1 ^ 3 + 3 * f2 * g1 * g2 + f1 * g3) =
    schwarzianVal f1 f2 f3 * g1 ^ 2 + schwarzianVal g1 g2 g3 := by
  unfold schwarzianVal
  field_simp [hf1, hg1]
  ring

/-- Algebraic closure of negative Schwarzian values under composition. -/
theorem schwarzianVal_comp_neg {f1 f2 f3 g1 g2 g3 : ℝ}
    (hf1 : f1 ≠ 0) (hg1 : g1 ≠ 0)
    (hSf : schwarzianVal f1 f2 f3 < 0)
    (hSg : schwarzianVal g1 g2 g3 < 0) :
    schwarzianVal
      (f1 * g1)
      (f2 * g1 ^ 2 + f1 * g2)
      (f3 * g1 ^ 3 + 3 * f2 * g1 * g2 + f1 * g3) < 0 := by
  rw [schwarzianVal_comp hf1 hg1]
  have hsq : 0 < g1 ^ 2 := sq_pos_of_ne_zero hg1
  nlinarith

/-- The algebraic Schwarzian expression vanishes whenever the second and third derivatives are
zero. -/
@[simp]
theorem schwarzianVal_affine (a : ℝ) : schwarzianVal a 0 0 = 0 := by
  unfold schwarzianVal
  simp

/-- Low-level analytic chain rule for the Schwarzian derivative from explicit `HasDerivAt`
and neighborhood derivative hypotheses. See `schwarzian_comp_of_contDiffAt` for the version
requiring only `ContDiffAt ℝ 3`. -/
theorem schwarzian_comp {f g : ℝ → ℝ} {x : ℝ}
    (hg1 : HasDerivAt g (deriv g x) x)
    (hg2 : HasDerivAt (deriv g) (deriv (deriv g) x) x)
    (hg3 : HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) x) x)
    (hf1 : HasDerivAt f (deriv f (g x)) (g x))
    (hf2 : HasDerivAt (deriv f) (deriv (deriv f) (g x)) (g x))
    (hf3 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) (g x)) (g x))
    (h_d1_eq : ∀ᶠ y in 𝓝 x, deriv (f ∘ g) y = deriv f (g y) * deriv g y)
    (h_d2_eq : ∀ᶠ y in 𝓝 x,
      deriv (deriv (f ∘ g)) y =
        deriv (deriv f) (g y) * (deriv g y) ^ 2 + deriv f (g y) * deriv (deriv g) y)
    (hf1_ne : deriv f (g x) ≠ 0) (hg1_ne : deriv g x ≠ 0) :
    schwarzian (f ∘ g) x = schwarzian f (g x) * (deriv g x) ^ 2 + schwarzian g x := by
  have hd1 : deriv (f ∘ g) x = deriv f (g x) * deriv g x :=
    (hf1.comp x hg1).deriv
  have hd2_has : HasDerivAt (fun y ↦ deriv f (g y) * deriv g y)
      (deriv (deriv f) (g x) * (deriv g x) ^ 2 + deriv f (g x) * deriv (deriv g) x) x := by
    have h := (hf2.comp x hg1).mul hg2
    convert h using 1
    · funext y; rfl
    · simp only [Function.comp_apply]; ring
  have hd2 : deriv (deriv (f ∘ g)) x =
      deriv (deriv f) (g x) * (deriv g x) ^ 2 + deriv f (g x) * deriv (deriv g) x := by
    rw [Filter.EventuallyEq.deriv_eq h_d1_eq]
    exact hd2_has.deriv
  have hd3_has : HasDerivAt
      (fun y ↦ deriv (deriv f) (g y) * (deriv g y) ^ 2 + deriv f (g y) * deriv (deriv g) y)
      (deriv (deriv (deriv f)) (g x) * (deriv g x) ^ 3 +
        3 * deriv (deriv f) (g x) * deriv g x * deriv (deriv g) x +
        deriv f (g x) * deriv (deriv (deriv g)) x) x := by
    have hpow : HasDerivAt (fun y ↦ (deriv g y) ^ 2)
        (2 * deriv g x ^ (2 - 1) * deriv (deriv g) x) x :=
      hg2.pow 2
    have hterm1 := (hf3.comp x hg1).mul hpow
    have hterm2 := (hf2.comp x hg1).mul hg3
    have hsum := hterm1.add hterm2
    convert hsum using 1
    · funext y; rfl
    · simp only [Function.comp_apply]; ring
  have hd3 : deriv (deriv (deriv (f ∘ g))) x =
      deriv (deriv (deriv f)) (g x) * (deriv g x) ^ 3 +
      3 * deriv (deriv f) (g x) * deriv g x * deriv (deriv g) x +
      deriv f (g x) * deriv (deriv (deriv g)) x := by
    rw [Filter.EventuallyEq.deriv_eq h_d2_eq]
    exact hd3_has.deriv
  simp only [schwarzian_eq_deriv, hd1, hd2, hd3]
  exact schwarzianVal_comp hf1_ne hg1_ne

/-- **Chain rule (cocycle identity) for the Schwarzian derivative**:
if `f` is `C³` at `g x` and `g` is `C³` at `x` with nonvanishing first derivatives, then
`schwarzian (f ∘ g) x = schwarzian f (g x) * (deriv g x) ^ 2 + schwarzian g x`. -/
theorem schwarzian_comp_of_contDiffAt {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 3 f (g x)) (hg : ContDiffAt ℝ 3 g x)
    (hf' : deriv f (g x) ≠ 0) (hg' : deriv g x ≠ 0) :
    schwarzian (f ∘ g) x = schwarzian f (g x) * (deriv g x) ^ 2 + schwarzian g x := by
  have h1 : ContDiffAt ℝ 2 (deriv g) x := hg.derivWithin (by norm_num)
  have h2 : ContDiffAt ℝ 1 (deriv (deriv g)) x := h1.derivWithin (by norm_num)
  have hf1_cd : ContDiffAt ℝ 2 (deriv f) (g x) := hf.derivWithin (by norm_num)
  have hf2_cd : ContDiffAt ℝ 1 (deriv (deriv f)) (g x) := hf1_cd.derivWithin (by norm_num)
  have hg1 : HasDerivAt g (deriv g x) x :=
    (hg.differentiableAt (by norm_num)).hasDerivAt
  have hg2 : HasDerivAt (deriv g) (deriv (deriv g) x) x :=
    (h1.differentiableAt (by norm_num)).hasDerivAt
  have hg3 : HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) x) x :=
    (h2.differentiableAt (by norm_num)).hasDerivAt
  have hf1 : HasDerivAt f (deriv f (g x)) (g x) :=
    (hf.differentiableAt (by norm_num)).hasDerivAt
  have hf2 : HasDerivAt (deriv f) (deriv (deriv f) (g x)) (g x) :=
    (hf1_cd.differentiableAt (by norm_num)).hasDerivAt
  have hf3 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) (g x)) (g x) :=
    (hf2_cd.differentiableAt (by norm_num)).hasDerivAt
  have hfg_ev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 f (g y) ∧ ContDiffAt ℝ 3 g y :=
    (hg.continuousAt.eventually (hf.eventually (by decide))).and (hg.eventually (by decide))
  have h_d1_eq : deriv (f ∘ g) =ᶠ[𝓝 x] fun y ↦ deriv f (g y) * deriv g y := by
    filter_upwards [hfg_ev] with y ⟨hfy, hgy⟩
    exact deriv_comp y (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))
  have h_d2_eq : ∀ᶠ y in 𝓝 x,
      deriv (deriv (f ∘ g)) y =
        deriv (deriv f) (g y) * (deriv g y) ^ 2 + deriv f (g y) * deriv (deriv g) y := by
    filter_upwards [h_d1_eq.eventuallyEq_nhds, hfg_ev] with y hy ⟨hfy, hgy⟩
    rw [hy.deriv_eq]
    have hgy1 : HasDerivAt g (deriv g y) y :=
      (hgy.differentiableAt (by norm_num)).hasDerivAt
    have hgy2 : HasDerivAt (deriv g) (deriv (deriv g) y) y :=
      ((hgy.derivWithin (by norm_num) : ContDiffAt ℝ 2 (deriv g) y).differentiableAt
        (by norm_num)).hasDerivAt
    have hfy2 : HasDerivAt (deriv f) (deriv (deriv f) (g y)) (g y) :=
      ((hfy.derivWithin (by norm_num) : ContDiffAt ℝ 2 (deriv f) (g y)).differentiableAt
        (by norm_num)).hasDerivAt
    have hmul := (hfy2.comp y hgy1).mul hgy2
    have hd : HasDerivAt (fun z ↦ deriv f (g z) * deriv g z)
        (deriv (deriv f) (g y) * (deriv g y) ^ 2 + deriv f (g y) * deriv (deriv g) y) y := by
      convert hmul using 1
      · funext z; rfl
      · simp only [Function.comp_apply]; ring
    exact hd.deriv
  exact schwarzian_comp hg1 hg2 hg3 hf1 hf2 hf3 h_d1_eq h_d2_eq hf' hg'

/-- Negative Schwarzian derivative is preserved under composition of `C³` functions with
nonvanishing first derivatives. -/
theorem schwarzian_comp_neg {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 3 f (g x)) (hg : ContDiffAt ℝ 3 g x)
    (hf' : deriv f (g x) ≠ 0) (hg' : deriv g x ≠ 0)
    (hSf : schwarzian f (g x) < 0) (hSg : schwarzian g x < 0) :
    schwarzian (f ∘ g) x < 0 := by
  rw [schwarzian_comp_of_contDiffAt hf hg hf' hg']
  have hsq : 0 < (deriv g x) ^ 2 := sq_pos_of_ne_zero hg'
  nlinarith

/-- Every affine map `y ↦ a * y + b` has identically zero Schwarzian derivative. -/
@[simp]
theorem schwarzian_affine (a b x : ℝ) : schwarzian (fun y ↦ a * y + b) x = 0 := by
  have hd1 : deriv (fun y : ℝ ↦ a * y + b) = fun _ ↦ a := by
    ext y
    have h : HasDerivAt (fun z : ℝ ↦ a * z + b) (a * 1 + 0) y :=
      ((hasDerivAt_id y).const_mul a).add (hasDerivAt_const y b)
    rw [h.deriv]
    ring
  have hd2 : deriv (deriv (fun y : ℝ ↦ a * y + b)) = fun _ ↦ 0 := by
    rw [hd1]
    ext y
    exact deriv_const y a
  have hd3 : deriv (deriv (deriv (fun y : ℝ ↦ a * y + b))) = fun _ ↦ 0 := by
    rw [hd2]
    ext y
    exact deriv_const y 0
  rw [schwarzian_eq_deriv, hd3, hd2, hd1]
  exact schwarzianVal_affine a

/-- The identity map has identically zero Schwarzian derivative. -/
@[simp]
theorem schwarzian_id (x : ℝ) : schwarzian id x = 0 := by
  have h : (id : ℝ → ℝ) = fun y ↦ 1 * y + 0 := by
    ext y
    simp
  rw [h]
  exact schwarzian_affine 1 0 x

/-- Every constant map has identically zero Schwarzian derivative. -/
@[simp]
theorem schwarzian_const (c x : ℝ) : schwarzian (fun _ ↦ c) x = 0 := by
  have h : (fun _ : ℝ ↦ c) = fun y ↦ 0 * y + c := by
    ext y
    simp
  rw [h]
  exact schwarzian_affine 0 c x

/-- The logistic map `y ↦ μ * y * (1 - y)` has Schwarzian derivative `-6 / (1 - 2 * x) ^ 2`
for any `μ ≠ 0` and any non-critical point `1 - 2 * x ≠ 0`. -/
theorem schwarzian_logistic {μ x : ℝ} (hμ : μ ≠ 0) (hx : 1 - 2 * x ≠ 0) :
    schwarzian (fun y ↦ μ * y * (1 - y)) x = -6 / (1 - 2 * x) ^ 2 := by
  have hd1 : deriv (fun y : ℝ ↦ μ * y * (1 - y)) = fun y ↦ μ * (1 - 2 * y) := by
    ext y
    have h1 : HasDerivAt (fun z : ℝ ↦ μ * z) (μ * 1) y := (hasDerivAt_id y).const_mul μ
    have h2 : HasDerivAt (fun z : ℝ ↦ 1 - z) (0 - 1) y :=
      (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)
    have h : HasDerivAt (fun z : ℝ ↦ μ * z * (1 - z)) (μ * (1 - 2 * y)) y := by
      convert h1.mul h2 using 1
      ring
    exact h.deriv
  have hd2 : deriv (deriv (fun y : ℝ ↦ μ * y * (1 - y))) = fun _ ↦ -2 * μ := by
    rw [hd1]
    ext y
    have h1 : HasDerivAt (fun z : ℝ ↦ 1 - 2 * z) (0 - 2 * 1) y :=
      (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).const_mul 2)
    have h : HasDerivAt (fun z : ℝ ↦ μ * (1 - 2 * z)) (-2 * μ) y := by
      convert h1.const_mul μ using 1
      ring
    exact h.deriv
  have hd3 : deriv (deriv (deriv (fun y : ℝ ↦ μ * y * (1 - y)))) = fun _ ↦ 0 := by
    rw [hd2]
    ext y
    exact deriv_const y (-2 * μ)
  rw [schwarzian_eq_deriv, hd3, hd2, hd1]
  unfold schwarzianVal
  field_simp [hμ, hx]
  ring

/-- The logistic map `y ↦ μ * y * (1 - y)` has strictly negative Schwarzian derivative at every
non-critical point `1 - 2 * x ≠ 0` when `μ ≠ 0`. -/
theorem schwarzian_logistic_neg {μ x : ℝ} (hμ : μ ≠ 0) (hx : 1 - 2 * x ≠ 0) :
    schwarzian (fun y ↦ μ * y * (1 - y)) x < 0 := by
  rw [schwarzian_logistic hμ hx]
  exact div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero hx)
