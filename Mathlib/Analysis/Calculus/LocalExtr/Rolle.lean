/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Rolle

/-!
# Rolle's Theorem

In this file we prove Rolle's Theorem. The theorem says that for a function `f : ℝ → ℝ` such that

* $f$ is differentiable on an open interval $(a, b)$, $a < b$;
* $f$ is continuous on the corresponding closed interval $[a, b]$;
* $f(a) = f(b)$,

there exists a point $c∈(a, b)$ such that $f'(c)=0$.

We prove four versions of this theorem.

* `exists_hasDerivAt_eq_zero` is closest to the statement given above. It assumes that at every
  point $x ∈ (a, b)$ function $f$ has derivative $f'(x)$, then concludes that $f'(c)=0$ for some
  $c∈(a, b)$.
* `exists_deriv_eq_zero` deals with `deriv f` instead of an arbitrary function `f'` and a predicate
  `HasDerivAt`; since we use zero as the "junk" value for `deriv f c`, this version does not
  assume that `f` is differentiable on the open interval.
* `exists_hasDerivAt_eq_zero'` is similar to `exists_hasDerivAt_eq_zero` but instead of assuming
  continuity on the closed interval $[a, b]$ it assumes that $f$ tends to the same limit as $x$
  tends to $a$ from the right and as $x$ tends to $b$ from the left.
* `exists_deriv_eq_zero'` relates to `exists_deriv_eq_zero` as `exists_hasDerivAt_eq_zero'`
  relates to `exists_hasDerivAt_eq_zero`.

We also prove versions of Rolle's Theorem for unbounded intervals, where the assumption that `f`
takes the same value at the endpoints is replaced by the assumption that `f` tends to the same
limit `l` at both ends of the interval.

* `exists_hasDerivAt_eq_zero_Ioi` and `exists_deriv_eq_zero_Ioi` are versions for the interval
  $(a, +∞)$: they assume that `f` tends to `l` at `𝓝[>] a` and along `atTop`;
* `exists_hasDerivAt_eq_zero_Iio` and `exists_deriv_eq_zero_Iio` are versions for the interval
  $(-∞, b)$: they assume that `f` tends to `l` along `atBot` and at `𝓝[<] b`;
* `exists_hasDerivAt_eq_zero_of_tendsto` and `exists_deriv_eq_zero_of_tendsto` are versions for
  the whole real line: they assume that `f` tends to `l` along `atBot` and along `atTop`.

## References

* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);

## Tags

local extremum, Rolle's Theorem
-/

public section

open Set Filter

open scoped Topology

variable {f f' : ℝ → ℝ} {a b l : ℝ}

/-- **Rolle's Theorem** `HasDerivAt` version -/
theorem exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩

/-- **Rolle's Theorem** `deriv` version -/
@[wikidata Q193286]
theorem exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has derivative `f'`
on `(a, b)` and has the same limit `l` at `𝓝[>] a` and `𝓝[<] b`, then `f' c = 0`
for some `c ∈ (a, b)`. -/
theorem exists_hasDerivAt_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo_of_tendsto hab
    (fun x hx ↦ (hff' x hx).continuousAt.continuousWithinAt) hfa hfb
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has the same limit
`l` at `𝓝[>] a` and `𝓝[<] b`, then `deriv f c = 0` for some `c ∈ (a, b)`. This version
does not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
theorem exists_deriv_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) : ∃ c ∈ Ioo a b, deriv f c = 0 := by
  by_cases! h : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x
  · exact exists_hasDerivAt_eq_zero' hab hfa hfb fun x hx => (h x hx).hasDerivAt
  · obtain ⟨c, hc, hcdiff⟩ : ∃ x ∈ Ioo a b, ¬DifferentiableAt ℝ f x := h
    exact ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩

/-! ### Rolle's Theorem on unbounded intervals -/

/-- **Rolle's Theorem** on the interval $(a, +∞)$, `HasDerivAt` version: if `f` has derivative `f'`
on `(a, +∞)` and tends to the same limit `l` at `𝓝[>] a` and along `atTop`, then `f' c = 0`
for some `c ∈ (a, +∞)`. -/
theorem exists_hasDerivAt_eq_zero_Ioi (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hftop : Tendsto f atTop (𝓝 l)) (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioi a, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioi_of_tendsto
    (fun x hx ↦ (hff' x hx).continuousAt.continuousWithinAt) hfa hftop
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩

/-- **Rolle's Theorem** on the interval $(a, +∞)$, `deriv` version: if `f` tends to the same limit
`l` at `𝓝[>] a` and along `atTop`, then `deriv f c = 0` for some `c ∈ (a, +∞)`. This version does
not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
theorem exists_deriv_eq_zero_Ioi (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hftop : Tendsto f atTop (𝓝 l)) : ∃ c ∈ Ioi a, deriv f c = 0 := by
  by_cases! h : ∀ x ∈ Ioi a, DifferentiableAt ℝ f x
  · exact exists_hasDerivAt_eq_zero_Ioi hfa hftop fun x hx => (h x hx).hasDerivAt
  · obtain ⟨c, hc, hcdiff⟩ : ∃ x ∈ Ioi a, ¬DifferentiableAt ℝ f x := h
    exact ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩

/-- **Rolle's Theorem** on the interval $(-∞, b)$, `HasDerivAt` version: if `f` has derivative `f'`
on `(-∞, b)` and tends to the same limit `l` along `atBot` and at `𝓝[<] b`, then `f' c = 0`
for some `c ∈ (-∞, b)`. -/
theorem exists_hasDerivAt_eq_zero_Iio (hfbot : Tendsto f atBot (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : ∀ x ∈ Iio b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Iio b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Iio_of_tendsto
    (fun x hx ↦ (hff' x hx).continuousAt.continuousWithinAt) hfbot hfb
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩

/-- **Rolle's Theorem** on the interval $(-∞, b)$, `deriv` version: if `f` tends to the same limit
`l` along `atBot` and at `𝓝[<] b`, then `deriv f c = 0` for some `c ∈ (-∞, b)`. This version does
not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
theorem exists_deriv_eq_zero_Iio (hfbot : Tendsto f atBot (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) : ∃ c ∈ Iio b, deriv f c = 0 := by
  by_cases! h : ∀ x ∈ Iio b, DifferentiableAt ℝ f x
  · exact exists_hasDerivAt_eq_zero_Iio hfbot hfb fun x hx => (h x hx).hasDerivAt
  · obtain ⟨c, hc, hcdiff⟩ : ∃ x ∈ Iio b, ¬DifferentiableAt ℝ f x := h
    exact ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩

/-- **Rolle's Theorem** on the whole real line, `HasDerivAt` version: if `f` has derivative `f'`
everywhere and tends to the same limit `l` along `atBot` and along `atTop`, then `f' c = 0`
for some `c`. -/
theorem exists_hasDerivAt_eq_zero_of_tendsto (hfbot : Tendsto f atBot (𝓝 l))
    (hftop : Tendsto f atTop (𝓝 l)) (hff' : ∀ x, HasDerivAt f (f' x) x) : ∃ c, f' c = 0 :=
  let ⟨c, hc⟩ := exists_isLocalExtr_of_tendsto
    (continuous_iff_continuousAt.2 fun x ↦ (hff' x).continuousAt) hfbot hftop
  ⟨c, hc.hasDerivAt_eq_zero (hff' c)⟩

/-- **Rolle's Theorem** on the whole real line, `deriv` version: if `f` tends to the same limit `l`
along `atBot` and along `atTop`, then `deriv f c = 0` for some `c`. This version does not require
differentiability of `f` because we define `deriv f c = 0` whenever `f` is not differentiable
at `c`. -/
theorem exists_deriv_eq_zero_of_tendsto (hfbot : Tendsto f atBot (𝓝 l))
    (hftop : Tendsto f atTop (𝓝 l)) : ∃ c, deriv f c = 0 := by
  by_cases! h : ∀ x, DifferentiableAt ℝ f x
  · exact exists_hasDerivAt_eq_zero_of_tendsto hfbot hftop fun x => (h x).hasDerivAt
  · obtain ⟨c, hcdiff⟩ : ∃ x, ¬DifferentiableAt ℝ f x := h
    exact ⟨c, deriv_zero_of_not_differentiableAt hcdiff⟩
